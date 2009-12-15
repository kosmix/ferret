#include <string.h>
#include <limits.h>
#include <math.h>
#include "search.h"
#include "array.h"
#include "symbol.h"
#include "internal.h"

/* #define DEBUG_DOC (1559930) */
#ifdef DEBUG_DOC
static int watch_doc = DEBUG_DOC;
static const float invalid_expl_value = -1.0;
#endif

#define PhQ(query) ((PhraseQuery *)(query))

/**
 * Use to sort the phrase positions into positional order. For phrase
 * positions matching at the same position (a very unusual case) we order by
 * first terms. The only real reason for the sorting by first terms is to get
 * consistant order of positions when testing. Functionally it makes no
 * difference.
 */
static int phrase_pos_cmp(const void *p1, const void *p2)
{
    int pos1 = ((PhrasePosition *)p1)->pos;
    int pos2 = ((PhrasePosition *)p2)->pos;
    if (pos1 > pos2) {
        return 1;
    }
    if (pos1 < pos2) {
        return -1;
    }
    return strcmp(((PhrasePosition *)p1)->terms[0],
                  ((PhrasePosition *)p2)->terms[0]);
}


/***************************************************************************
 *
 * PhraseScorer
 *
 ***************************************************************************/

/***************************************************************************
 * PhPos
 ***************************************************************************/

#define PP(p) ((PhPos *)(p))
typedef struct PhPos
{
    TermDocEnum *tpe;
    int offset;
    int count;
    int doc;
    /** apparently (<real position> - offset) or (-1), not mutually exclusive
     *  (contrary to the field's name)
     *  @todo TODO Make position really mean position offset, for clarity and
     *             to make the range of valid values easily identifiable. */
    int position;

    /** a contiguous counter (which offset is not) */
    int id;

    /** idf is used and set by ProximityPhraseScorer only */
    float idf;
    /** used by ProximityPhraseScorer to accumulate value within a document */
    float *score;
    int score_size;
    /** ProximityPhraseScorer: is term a stopword whose presence is irrelevant
        to deciding whether a document is eligible for scoring? */
    bool stop;
} PhPos;

static bool pp_next(PhPos *self)
{
    TermDocEnum *tpe = self->tpe;
    /* invalidate state from before pp_next call */
    self->position = -1;
    self->count = -1;
    int i;
    for (i = 0; i < self->score_size; ++i) {
        self->score[i] = 0;
    }
    if (!tpe->next(tpe)) {
        tpe->close(tpe);            /* close stream */
        self->tpe = NULL;
        self->doc = INT_MAX;        /* sentinel value */
        return false;
    }
    self->doc = tpe->doc_num(tpe);
    return true;
}

static bool pp_skip_to(PhPos *self, int doc_num)
{
    TermDocEnum *tpe = self->tpe;
    /* invalidate state from before pp_skip_to call */
    self->position = -1;
    self->count = -1;
    int i;
    for (i = 0; i < self->score_size; ++i) {
        self->score[i] = 0;
    }

    if (!tpe->skip_to(tpe, doc_num)) {
        tpe->close(tpe);            /* close stream */
        self->tpe = NULL;
        self->doc = INT_MAX;        /* sentinel value */
        return false;
    }
    self->doc = tpe->doc_num(tpe);
    return true;
}

static bool pp_next_position(PhPos *self)
{
    TermDocEnum *tpe = self->tpe;
    --self->count;
    if (self->count > 0) {         /* read subsequent pos's */
        self->position = tpe->next_position(tpe) - self->offset;
        return true;
    }
    else {
        self->position = -1;  /* (that's what pp_new does, but why?) */
        return false;
    }
}

static bool pp_first_position(PhPos *self)
{
    TermDocEnum *tpe = self->tpe;
    self->count = tpe->freq(tpe) + 1;
    return pp_next_position(self);
}

/*
static char *pp_to_s(PhPos *self)
{
    return strfmt("pp->(doc => %d, position => %d)", self->doc, self->position);
}
*/

#define PP_pp(p) (*(PhPos **)p)
static int pp_cmp(const void *const p1, const void *const p2)
{
    int cmp = PP_pp(p1)->doc - PP_pp(p2)->doc;
    if (cmp == 0) {
        return PP_pp(p1)->position - PP_pp(p2)->position;
    }
    else {
        return cmp;
    }
}

static int pp_pos_cmp(const void *const p1, const void *const p2)
{
    return PP_pp(p1)->position - PP_pp(p2)->position;
}

/** comparator that pushes to the end any PhPos with no positions left */
static int pp_pos_or_end_cmp(const void *const p1, const void *const p2)
{
    const int c1 = PP_pp(p1)->count, c2 = PP_pp(p2)->count;
    const int end1 = (c1 <= 0) ? 1 : 0, end2 = (c2 <= 0) ? 1 : 0;
    if ((end1 == 1) || (end2 == 1)) {
        return end1 - end2;
    } else {
        const int real_pos1 = PP_pp(p1)->position + PP_pp(p1)->offset;
        const int real_pos2 = PP_pp(p2)->position + PP_pp(p2)->offset;
        return real_pos1 - real_pos2;
    }
}

static bool pp_less_than(const PhPos *pp1, const PhPos *pp2)
{
    if (pp1->position == pp2->position) {
        return pp1->offset < pp2->offset;
    }
    else {
        return pp1->position < pp2->position;
    }
}

static void pp_destroy(PhPos *pp)
{
    if (pp->tpe) {
        pp->tpe->close(pp->tpe);
    }
    if (pp->score) {
        assert(pp->score_size);
        free(pp->score);
    }
    free(pp);
}

static PhPos *pp_new(TermDocEnum *tpe, int offset, int id)
{
    PhPos *self = ALLOC(PhPos);

    self->tpe = tpe;
    self->count = self->doc = self->position = -1;
    self->offset = offset;
    self->id = id;

    /* only ProximityPhraseScorer sets/uses these fields */
    self->idf = -1;
    self->score = NULL;
    self->score_size = 0;
    self->stop = false;

    return self;
}

/***************************************************************************
 * PhraseScorer
 ***************************************************************************/

#define PhSc(scorer) ((PhraseScorer *)(scorer))

typedef struct PhraseScorer
{
    Scorer  super;
    float (*phrase_freq)(Scorer *self);
    float   freq;
    uchar  *norms;
    float   value;
    Weight *weight;
    PhPos **phrase_pos;
    int     pp_first_idx;
    int     pp_cnt;
    int     slop;
    bool    first_time : 1;
    bool    more : 1;
    bool    check_repeats : 1;

    /** ProximityScorer: set FRT_QUERYSTATE_PHRASE_MATCH if phrase found?
     *
     *  Independent of scoring, ProximityScorer can set a flag
     *  if the entire phrase occurs (in the field being scored).
     *  Though this flag is set per scorer, all scorers set the same
     *  FRT_QUERYSTATE_PHRASE_MATCH flag.
     */
    bool    set_phrase_match_flag : 1;
    /** ProximityScorer: set FRT_QUERYSTATE_ALL_TERMS if terms present?
     *
     *  Independent of scoring, ProximityScorer can set a flag
     *  if all terms occur (in the field being scored).
     *  Though this flag is set per scorer, all scorers set the same
     *  FRT_QUERYSTATE_ALL_TERMS flag.
     */
    bool    set_all_terms_flag : 1;
    /** ProximityScorer: set FRT_QUERYSTATE_PHRASE_MATCH_TITLE_KEYWORDS?
     *
     *  Like set_phrase_match_flag, but determining whether to set
     *  FRT_QUERYSTATE_PHRASE_MATCH_TITLE_KEYWORDS.  (Kosmix-specific)
     */
    bool    set_phrase_match_title_keywords_flag : 1;

    /** ProximityScorer: apply Similarity.tf to tf for each window size?
     *
     *  For each term, ProximityScorer counts tf separately for one-term
     *  matches, two-terms-in-a-proximity-window matches, and so on up to
     *  the number of terms in the query.
     *
     *  Each of these separate tf counts is normalized through Similarity.tf
     *  if this value is true.
     */
    bool    similarity_tf : 1;
    /** ProximityScorer: require same order of terms as query string to score?
     *
     *  If true, a multi-query-term text window is scored only if the query
     *  terms occur inside the window in the same order as they appear in
     *  the query.
     *  If false, a multi-query-term text window is scored regardless of the
     *  order of the query terms occurring inside it.
     */
    bool    ordered_proximity : 1;
    /** ProximityScorer: require all non-stopwords to score document?
     *
     *  If true, any missing non-stopword makes a document ineligible for
     *  scoring and ranking.
     *  If false, any present non-stopword makes a document eligible for
     *  scoring and ranking.
     */
    bool    conjunctive_proximity : 1;
    /** ProximityScorer: score stopwords at all (even in proximity windows)?
     *
     *  If true, stopwords are scored as they occur, as usual.
     *  If false, stopword matches contribute no score to any document.
     */
    bool    score_stopwords : 1;
    /** ProximityScorer: frequency (in orders of magnitude above rarest term)
     *  above which a query term is considered a stopword.
     */
    float   stopword_gap;

    /** ProximityScorer: raw score constant factor normalization
     *  (black-box factor by which tf.idf score is scaled)
     */
    float   raw_score_norm_factor;
    /** ProximityScorer: raw score per-term factor normalization
     *  (black-box factor by which tf.idf score is reduced for each query term)
     */
    float   raw_score_term_factor;

} PhraseScorer;

static void phsc_init(PhraseScorer *phsc)
{
    int i;
    for (i = phsc->pp_cnt - 1; i >= 0; i--) {
        if (!(phsc->more = pp_next(phsc->phrase_pos[i]))) break;
    }

    if (phsc->more) {
        qsort(phsc->phrase_pos, phsc->pp_cnt,
              sizeof(PhPos *), &pp_cmp);
        phsc->pp_first_idx = 0;
    }
}

static bool phsc_do_next(Scorer *self)
{
    PhraseScorer *phsc = PhSc(self);
    const int pp_cnt = phsc->pp_cnt;
    int pp_first_idx = phsc->pp_first_idx;
    PhPos **phrase_positions = phsc->phrase_pos;

    PhPos *first = phrase_positions[pp_first_idx];
    PhPos *last  = phrase_positions[PREV_NUM(pp_first_idx, pp_cnt)];

    while (phsc->more) {
        if (self->state && self->state->is_aborted &&
            self->state->is_aborted(self->state->is_aborted_param))
        {
            break;
        }
        /* find doc with all the terms */
        while (phsc->more && first->doc < last->doc) {
            /* skip first upto last */
            phsc->more = pp_skip_to(first, last->doc);
            last = first;
            pp_first_idx = NEXT_NUM(pp_first_idx, pp_cnt);
            first = phrase_positions[pp_first_idx];
        }

        if (phsc->more) {
            /* pp_first_idx will be used by phrase_freq */
            phsc->pp_first_idx = pp_first_idx;

            /* found a doc with all of the terms */
            phsc->freq = phsc->phrase_freq(self);

            if (phsc->freq == 0.0) {            /* no match */
                /* continuing search so re-set first and last */
                pp_first_idx = phsc->pp_first_idx;
                first = phrase_positions[pp_first_idx];
                last =  phrase_positions[PREV_NUM(pp_first_idx, pp_cnt)];
                phsc->more = pp_next(last);     /* trigger further scanning */
            }
            else {
                self->doc = first->doc;
                return true;                    /* found a match */
            }

        }
    }
    return false;
}

static float phsc_score(Scorer *self)
{
    PhraseScorer *phsc = PhSc(self);
    float raw_score = sim_tf(self->similarity, phsc->freq) * phsc->value;
    /* normalize */
    return raw_score * sim_decode_norm(
        self->similarity,
        phsc->norms[self->doc]);
}

static bool phsc_next(Scorer *self)
{
    PhraseScorer *phsc = PhSc(self);
    if (phsc->first_time) {
        phsc_init(phsc);
        phsc->first_time = false;
    }
    else if (self->state && self->state->is_aborted &&
             self->state->is_aborted(self->state->is_aborted_param)) {
        return false;
    }
    else if (phsc->more) {
        /* trigger further scanning */
        phsc->more = pp_next(
            phsc->phrase_pos[PREV_NUM(phsc->pp_first_idx, phsc->pp_cnt)]);
    }

    return phsc_do_next(self);
}

static bool phsc_skip_to(Scorer *self, int doc_num)
{
    PhraseScorer *phsc = PhSc(self);
    int i;
    for (i = phsc->pp_cnt - 1; i >= 0; i--) {
        if (!(phsc->more = pp_skip_to(phsc->phrase_pos[i], doc_num))) {
            break;
        }
    }

    if (phsc->more) {
        qsort(phsc->phrase_pos, phsc->pp_cnt,
              sizeof(PhPos *), &pp_cmp);
        phsc->pp_first_idx = 0;
    }
    return phsc_do_next(self);
}

static Explanation *phsc_explain(Scorer *self, int doc_num)
{
    PhraseScorer *phsc = PhSc(self);
    float phrase_freq;

    phsc_skip_to(self, doc_num);

    phrase_freq = (self->doc == doc_num) ? phsc->freq : 0.0f;
    return expl_new(sim_tf(self->similarity, phrase_freq),
                    "tf(phrase_freq=%f)", phrase_freq);
}

static void phsc_destroy(Scorer *self)
{
    PhraseScorer *phsc = PhSc(self);
    int i;
    for (i = phsc->pp_cnt - 1; i >= 0; i--) {
        pp_destroy(phsc->phrase_pos[i]);
    }
    free(phsc->phrase_pos);
    scorer_destroy_i(self);
}

static bool phsc_check_repeats_flag(PhrasePosition *positions, int pos_cnt)
{
    HashSet *term_set = hs_new_str((free_ft)NULL);
    bool check_repeats = false;
    int i;
    for (i = 0; i < pos_cnt; i++) {
        /* check for repeats */
        char **terms = positions[i].terms;
        const int t_cnt = ary_size(terms);
        int j;
        for (j = 0; j < t_cnt; j++) {
            if (hs_add(term_set, terms[j])) {
                check_repeats = true;
                break;
            }
        }
    }
    hs_destroy(term_set);
    return check_repeats;
}

static Scorer *phsc_new(Weight *weight,
                        TermDocEnum **term_pos_enum,
                        PhrasePosition *positions, int pos_cnt,
                        Similarity *similarity,
                        uchar *norms,
                        int slop)
{
    int i;
    Scorer *self                = scorer_new(PhraseScorer, similarity);

    PhSc(self)->weight          = weight;
    PhSc(self)->norms           = norms;
    PhSc(self)->value           = weight->value;
    PhSc(self)->phrase_pos      = ALLOC_N(PhPos *, pos_cnt);
    PhSc(self)->pp_first_idx    = 0;
    PhSc(self)->pp_cnt          = pos_cnt;
    PhSc(self)->slop            = slop;
    PhSc(self)->first_time      = true;
    PhSc(self)->more            = true;
    if (slop) {
        PhSc(self)->check_repeats = phsc_check_repeats_flag(positions, pos_cnt);
    } else {
        PhSc(self)->check_repeats = false;
    }
    for (i = 0; i < pos_cnt; i++) {
        PhSc(self)->phrase_pos[i] = pp_new(term_pos_enum[i], positions[i].pos,
            i);
    }

    self->score     = &phsc_score;
    self->next      = &phsc_next;
    self->skip_to   = &phsc_skip_to;
    self->explain   = &phsc_explain;
    self->destroy   = &phsc_destroy;

    return self;
}

/***************************************************************************
 * ExactPhraseScorer
 ***************************************************************************/

static float ephsc_phrase_freq(Scorer *self)
{
    PhraseScorer *phsc = PhSc(self);
    int i;
    int pp_first_idx = 0;
    const int pp_cnt = phsc->pp_cnt;
    float freq = 0.0;
    PhPos **phrase_positions = phsc->phrase_pos;
    PhPos *first;
    PhPos *last;

    for (i = 0; i < pp_cnt; i++) {
        pp_first_position(phrase_positions[i]);
    }
    qsort(phrase_positions, pp_cnt, sizeof(PhPos *), &pp_pos_cmp);

    first = phrase_positions[0];
    last =  phrase_positions[pp_cnt - 1];

    /* scan to position with all terms */
    do {
        /* scan forward in first */
        while (first->position < last->position) {
            do {
                if (! pp_next_position(first)) {
                    /* maintain first position */
                    phsc->pp_first_idx = pp_first_idx;
                    return freq;
                }
            } while (first->position < last->position);
            last = first;
            pp_first_idx = NEXT_NUM(pp_first_idx, pp_cnt);
            first = phrase_positions[pp_first_idx];
        }
        freq += 1.0; /* all equal: a match */
    } while (pp_next_position(last));

    /* maintain first position */
    phsc->pp_first_idx = pp_first_idx;
    return freq;
}

static Scorer *exact_phrase_scorer_new(Weight *weight,
                                       TermDocEnum **term_pos_enum,
                                       PhrasePosition *positions, int pp_cnt,
                                       Similarity *similarity, uchar *norms)
{
    Scorer *self = phsc_new(weight,
                            term_pos_enum,
                            positions,
                            pp_cnt,
                            similarity,
                            norms,
                            0);

    PhSc(self)->phrase_freq = &ephsc_phrase_freq;
    return self;
}

/***************************************************************************
 * SloppyPhraseScorer
 ***************************************************************************/

static bool sphsc_check_repeats(PhPos *pp,
                                PhPos **positions,
                                const int p_cnt)
{
    int j;
    for (j = 0; j < p_cnt; j++) {
        PhPos *ppj = positions[j];
        /* If offsets are equal, either we are at the current PhPos +pp+ or
         * +pp+ and +ppj+ are supposed to match in the same position in which
         * case we don't need to check. */
        if (ppj->offset == pp->offset) {
            continue;
        }
        /* the two phrase positions are matching on the same term
         * which we want to avoid */
        if ((ppj->position + ppj->offset) == (pp->position + pp->offset)) {
            if (!pp_next_position(pp)) {
                /* We have no matches for this document */
                return false;
            }
            /* we changed the position so we need to start check again */
            j = -1;
        }
    }
    return true;
}

static float sphsc_phrase_freq(Scorer *self)
{
    PhraseScorer *phsc = PhSc(self);
    PhPos *pp;
    PriorityQueue *pq = pq_new(phsc->pp_cnt, (lt_ft)&pp_less_than, NULL);
    const int pp_cnt = phsc->pp_cnt;

    int last_pos = 0, pos, next_pos, start, match_length, i;
    bool done = false;
    bool check_repeats = phsc->check_repeats;
    float freq = 0.0;

    for (i = 0; i < pp_cnt; i++) {
        bool res;
        pp = phsc->phrase_pos[i];
        /* we should always have at least one position or this functions
         * shouldn't have been called. */
        res = pp_first_position(pp);
        assert(res);(void)res;
        if (check_repeats && i > 0) {
            if (!sphsc_check_repeats(pp, phsc->phrase_pos, i)) {
                goto return_freq;
            }
        }
        if (pp->position > last_pos) {
            last_pos = pp->position;
        }
        pq_push(pq, pp);
    }

    do {
        pp = (PhPos *)pq_pop(pq);
        pos = start = pp->position;
        next_pos = PP(pq_top(pq))->position;
        while (pos <= next_pos) {
            start = pos;        /* advance pp to min window */
            if (!pp_next_position(pp)
                || (check_repeats
                    && !sphsc_check_repeats(pp, phsc->phrase_pos, pp_cnt))) {
                done = true;
                break;
            }
            pos = pp->position;
        }

        match_length = last_pos - start;
        if (match_length <= phsc->slop) {
            /* score match */
            freq += sim_sloppy_freq(self->similarity, match_length);
        }

        if (pp->position > last_pos) {
            last_pos = pp->position;
        }
        pq_push(pq, pp);        /* restore pq */
    } while (!done);

return_freq:

    pq_destroy(pq);
    return freq;
}

static Scorer *sloppy_phrase_scorer_new(Weight *weight,
                                        TermDocEnum **term_pos_enum,
                                        PhrasePosition *positions,
                                        int pp_cnt, Similarity *similarity,
                                        int slop, uchar *norms)
{
    Scorer *self = phsc_new(weight,
                            term_pos_enum,
                            positions,
                            pp_cnt,
                            similarity,
                            norms,
                            slop);

    PhSc(self)->phrase_freq = &sphsc_phrase_freq;
    return self;
}

/***************************************************************************
 * ProximityPhraseScorer
 ***************************************************************************/

/* Unlike other PhraseScorers, this one does not require all terms in the
   phrase to occur for a document to match and be scored.  Consequently,
   all loop-initialization and traversal code has to be replaced so that
   it does not short-circuit as soon as any term runs out of occurrences
   in a document.

   PhraseScorer.pp_first_idx is unused in ProximityPhraseScorer, because
   there's no corresponding pphsc_phrase_freq in use.
   PhraseScorer.phrase_freq is set only to avoid the awkward scenario
   of a "virtual method" (reinvented) being NULL; it is not used.
 */

static bool pphsc_skip_to(Scorer *self, int doc_num)
{
    PhraseScorer *phsc = PhSc(self);
    const int pp_cnt = phsc->pp_cnt;
    PhPos **phrase_positions = phsc->phrase_pos;
    bool more = phsc->more, done = false;

    int nonstop_required = 0, i;
    if (phsc->conjunctive_proximity) {
        /* Require all nonstopwords to appear */
        for (i = 0; i < pp_cnt; ++i) {
            if (!phrase_positions[i]->stop) {
                ++nonstop_required;
            }
        }
    } else {
        /* Require any nonstopword to appear */
        nonstop_required = pp_cnt ? 1 : 0;
    }
    assert((pp_cnt > 0) == (nonstop_required > 0));

    while (!done && more) {
        /** smallest document number > doc_num with one or more nonstopwords */
        int next_doc = INT_MAX;
        /** number of nonstopwords found in document number doc_num */
        int nonstop_present = 0;
        more = false;
        for (i = 0; i < pp_cnt; ++i) {
#ifdef DEBUG_DOC
            if (doc_num == DEBUG_DOC) {
                fprintf(stderr, "checking term %d in doc_num %d\n", i, doc_num);
            }
#endif
            if (phrase_positions[i]->tpe != NULL) {
                pp_skip_to(phrase_positions[i], doc_num);
            }
            if (phrase_positions[i]->tpe != NULL) {
                /* At least more of this term is still available. */
                more = true;
                const int pp_doc = phrase_positions[i]->doc;
                assert(pp_doc >= doc_num);
                if (!phrase_positions[i]->stop && (pp_doc == doc_num)) {
                    ++nonstop_present;
                    if (nonstop_present >= nonstop_required) {
                        done = true;
                    }
                }

                if ((pp_doc < next_doc) && (pp_doc > doc_num)) {
                    next_doc = pp_doc;
                }
            }
        }
        if (!done && more) {
            assert((next_doc > doc_num) || (doc_num == INT_MAX));
            if (next_doc == INT_MAX) {
                ++doc_num;
            } else {
                doc_num = next_doc;
            }
        }
    }
    if (more) {
        qsort(phsc->phrase_pos, phsc->pp_cnt, sizeof(PhPos *), &pp_cmp);
    }
    assert((phsc->pp_first_idx == 0) && "pp_first_idx is unused and untouched");
    self->doc = phsc->phrase_pos[phsc->pp_first_idx]->doc;
    phsc->more = more;
    return phsc->more;
}

/* Initialize phsc->phrase_pos fields to first match for each term.
   (If doc has a known minimum value, this function can be replaced
    by a simpler skip_to call.) */
static bool pphsc_init(Scorer *self)
{
    PhraseScorer *phsc = PhSc(self);
    bool more = false;
    int i;
    int min_doc = INT_MAX;
    for (i = 0 ; i < phsc->pp_cnt; ++i) {
        if (pp_next(phsc->phrase_pos[i])) {
            more = true;
            if (phsc->phrase_pos[i]->doc < min_doc) {
                min_doc = phsc->phrase_pos[i]->doc;
            }
        }
    }
    if (more) {
        phsc->pp_first_idx = 0;
        return pphsc_skip_to(self, min_doc);
    } else {
        return false;
    }
}

static bool pphsc_next(Scorer *self)
{
    PhraseScorer *phsc = PhSc(self);
    if (phsc->first_time) {
        phsc->first_time = false;
        phsc->more = pphsc_init(self);    
    } else if (self->state && self->state->is_aborted &&
               self->state->is_aborted(self->state->is_aborted_param)) {
        return false;
    } else {
        phsc->more = pphsc_skip_to(self, self->doc + 1);
    }
    return phsc->more;
}

/** return the number of terms that occur in the active document
 *
 *  Precondition: phsc->phrase_pos must already be sorted in
 *                phsc->phrase_pos[i]->doc order, so that the
 *                terms that occur are listed first
 */
static int pphsc_terms_in_doc(PhraseScorer *phsc)
{
    /** The terms that appear in this document (<= pp_cnt). */
    int pp_in_doc = phsc->pp_cnt;
    int i;
    for (i = 0; i < phsc->pp_cnt; ++i) {
        if (phsc->phrase_pos[i]->doc > phsc->super.doc) {
            pp_in_doc = i;
            break;
        }
    }
    /* ordering should have been guaranteed by each next/skip_to's qsort */
    for ( ; i < phsc->pp_cnt; ++i) {
        assert((phsc->phrase_pos[i]->doc > phsc->super.doc) &&
            "Term with earlier doc appears later in phsc->phrase_pos array");
    }
    /* at least one term should have been found in this document for us to be here */
    assert((pp_in_doc != 0) && "phsc->doc has no query terms to score");

    return pp_in_doc;
}

/** like sphsc_check_repeats, but ignores out-of-occurrences terms
 *
 *  @todo TODO Supersede sphsc_check_repeats?
 */
static bool pphsc_check_repeats(PhPos *pp,
                                PhPos **positions,
                                const int p_cnt)
{
    assert(pp->count && "Position to check for repetition must exist");
    int j;
    for (j = 0; j < p_cnt; j++) {
        PhPos *ppj = positions[j];
        /* A nonexistent position cannot be a repetition of any term. */
        if (ppj->count == 0) {
            continue;
        }
        /* If offsets are equal, either we are at the current PhPos +pp+ or
         * +pp+ and +ppj+ are supposed to match in the same position in which
         * case we don't need to check. */
        if (ppj->offset == pp->offset) {
            continue;
        }
        /* the two phrase positions are matching on the same term
         * which we want to avoid */
        if ((ppj->position + ppj->offset) == (pp->position + pp->offset)) {
            if (!pp_next_position(pp)) {
                /* We have no matches left for this document */
                return false;
            }
            /* we changed the position so we need to start check again */
            j = -1;
        }
    }
    return true;
}

/* The (largest) size of the text window in which proximity is considered:
 *     window_size_{number_of_terms} =
 *         window_size_base + (number_of_terms)*window_size_per_term
 */
static const int window_size_base = 1, window_size_per_term = 1;

/* If one or more terms occur in a text window, the score of the
 * text occurrences in the window is a "magic" formula replacing
 * the straight tf.idf product of a term/phrase.
 *
 * The formula simply sums for each document, at each term occurrence
 * in the document:
 *  s(1) *    (idf of occurring term)
 *  s(2) * sum(idf of first two occurring terms, if in window_size_{2 terms})
 *  s(3) * sum(idf of first three occurring terms, if in window_size_{3 terms})
 *       :
 * where s(n) = base_tf_score * tf_scale^n, for (presumably) tf_scale > 1.
 *
 * Optionally, each tf component of the above formula may be fed through
 * Similarity's tf normalization before being multiplied by the respective idf.
 * To implement Similarity.tf, count the one-term-window occurrences of each
 * term separately from the two-term-window occurrences of the term, and so on.
 * (Feed each n-term-window count through Similarity.tf separately.)
 *
 * Because of the way the scoring loop identifies text windows
 * (advancing the position pointer of one term, then scoring again),
 * all n-term sequences occurring within window_size_{n terms} are
 * scored exactly once.  (Proof: Each sequence's first word is the
 * earliest position pointer in exactly one iteration of the loop.)
 *
 * As consequences of this current scoring formula:
 *
 * * Terms that never occur in a proximity window end up scored as
 *   sum(idf) == tf.idf.  (Ferret and Lucene seem to use idf^2 for
 *   text scoring, but the squaring does not seem helpful.)  Hence,
 *   the degenerate case of no-proximal-text is scored as expected.
 *
 * * Terms that do occur in nontrivial text-proximity windows have
 *   a total score that must exceed the same terms occurring with
 *   same frequency in only trivial (one-word) proximity windows;
 *   because the former score includes the latter sum.
 *
 * * Ordering of terms in a document, relative to their ordering in
 *   a query, is ignored.  I have not found any references that
 *   encourage ordering-sensitive proximity scoring for relevance;
 *   in fact, users may commonly write query terms in "incorrect" order.
 *
 * * Longer documents are favored, because the effective tf is not
 *   scaled directly to the length of the document.  This behavior is
 *   contrary to the text scoring in Ferret and Lucene, which use
 *   sqrt(tf) to reduce the effect of high tf in longer documents.
 *
 *   Actually, Ferret and Lucene use sqrt(tf) * 1/sqrt(L) [length norm],
 *   but this proximity formula leads to tf * 1/sqrt(L) [length norm].
 *   This formula, then, is vulnerable to query-term repetition in a
 *   document; Ferret and Lucene normalize away this effect.
 */

static const float base_tf_score = 0.1, tf_scale = 10;

/** Collect the number of occurrences of each term that should be included
    in the sum-of-idfs formula.

    Note that this function defines local position variables that represent
    *real* positions, not the fake (position-offset) misnomers used in
    original Ferret code.  The ordering of the words in the query are ignored,
    so the sliding window walk is sorted by true position for all query terms.

    @param explanation - NULL if no explanation detail desired
 */
static void pphsc_textscore_tf(Scorer *self, Explanation *explanation)
{
    PhraseScorer *phsc = PhSc(self);
    const int pp_in_doc = pphsc_terms_in_doc(phsc);
    PhPos **phrase_positions = phsc->phrase_pos;
    const bool check_repeats = phsc->check_repeats;
    assert((pp_in_doc > 0) && "At least one term must be in scored document");
    if (phsc->set_all_terms_flag && (pp_in_doc == phsc->pp_cnt)) {
        if (self->state) {
            self->state->doc_flags |= FRT_QUERYSTATE_ALL_TERMS;
        }
    }

    int i;
    for (i = 0; i < pp_in_doc; i++) {
        PhPos *pp = phsc->phrase_pos[i];
        assert(pp->doc == self->doc);
        /* we should always have at least one position or this function
         * shouldn't have been called. */
        if (!pp_first_position(pp)) {
            assert(0 && "Term occurring in document should have some position");
        }
        if (check_repeats && (i > 0)) {
            pphsc_check_repeats(pp, phsc->phrase_pos, i);
        }
        assert(pp->score_size == phsc->pp_cnt);
        int j;
        for (j = 0; j < phsc->pp_cnt; ++j) {
            assert(pp->score[j] == 0);
        }
    }

    for ( ; i < phsc->pp_cnt; ++i) {
        assert((phrase_positions[i]->doc != self->doc) &&
            "Ignored terms for document must not exist on document");
        assert(phrase_positions[i]->score_size == phsc->pp_cnt);
        int j;
        for (j = 0; j < phsc->pp_cnt; ++j) {
            assert(phrase_positions[i]->score[j] == 0);
        }
    }
    qsort(phrase_positions, pp_in_doc, sizeof(PhPos *), &pp_pos_or_end_cmp);

#ifdef DEBUG_DOC
    if (!explanation && (self->doc == watch_doc)) {
        explanation = expl_new(invalid_expl_value, "query execution");
    }
#endif

    /** [phsc->pp_cnt*i + j]: tf for word (id i) in windows with j+1 terms */
    Explanation **window_explanations = NULL;
    if (explanation) {
        const int window_explanations_size = phsc->pp_cnt * phsc->pp_cnt;
        window_explanations = ALLOC_N(Explanation *, window_explanations_size);
        int i;
        for (i = 0; i < window_explanations_size; ++i) {
            window_explanations[i] = NULL;
        }

        for (i = 0; i < phsc->pp_cnt; ++i) {
            const PhPos *ppi = phrase_positions[i];
            int window_size;
            for (window_size = 1; window_size <= phsc->pp_cnt; ++window_size) {
                const int term_ord = ppi->offset + 1;
                /* score for explanation to be filled in at end */
                Explanation *e = expl_new(0.0,
                    "tf for term #%d (idf=%f) in text windows with %d term%s",
                    term_ord, ppi->idf, window_size,
                    (window_size == 1) ? "" : "s");
                const size_t offset = phsc->pp_cnt * ppi->id + (window_size-1);
                assert(offset < (size_t)window_explanations_size);
                assert(window_explanations[offset] == NULL);
                window_explanations[offset] = e;
            }
        }
        for (i = 0; i < window_explanations_size; ++i) {
            assert(window_explanations[i]);
        }
    }

    int pp_left = pp_in_doc;
    while (phrase_positions[0]->count) {
        PhPos *pp = phrase_positions[0];
        const int start_pos = pp->position + pp->offset;
        int window_size = window_size_base;
        /** Is the match so far [start_pos, ppi] a prefix of the query terms
         *  in query order? */
        bool phrase_prefix = true;
        for (i = 0; i < pp_left; ++i) {
            PhPos *ppi = phrase_positions[i];
            if (ppi->count == 0) {
                int j;
                for (j = i; j < pp_in_doc; ++j) {
                    assert((phrase_positions[j]->count == 0) &&
                        "phrase_positions ordering must leave terms with "
                        "no occurrences left at end of array");
                    assert((phrase_positions[j]->position == -1) &&
                        "phrase_positions ordering must leave terms with "
                        "no occurrences left at end of array");
                }
                pp_left = i;
                break;
            } else {
                assert(ppi->tpe != NULL);
                assert(ppi->position + ppi->offset >= start_pos);
            }

            /* Check whether term i is consistent with a phrase match. */
            const int pos = ppi->position + ppi->offset;
            if ((ppi->id != i) || (pos != start_pos + i)) {
                phrase_prefix = false;
            }

            /* If ordering is broken, stop checking for longer text windows.
               @todo TODO Another version could step over out-of-order terms
               as if the out-of-order term were not a match. */
            if (phsc->ordered_proximity) {
                const int last_offset = i ? phrase_positions[i-1]->offset :
                    pp->offset; 
                if (ppi->offset < last_offset)
                    break;
            }

            /* PhPos.position is a position-offset value, not a position,
               so window_size needs to be adjusted by the sums of the offsets
               for any text-window-size check to work. */
            window_size += window_size_per_term;
            assert((i == 0) || (pos > start_pos));
            if (pos - start_pos + 1 <= window_size) {
                int j = 0;
                for (j = 0; j <= i; ++j) {
                    /* just accumulate tf component now */
                    /* idf multiply happens in pphsc_score */
                    if (phsc->score_stopwords || !ppi->stop) {
                        ++phrase_positions[j]->score[i];
                    }
                }
                if (explanation) {
                    for (j = 0; j <= i; ++j) {
                        PhPos *ppj = phrase_positions[j];
                        if (phsc->score_stopwords || !ppi->stop) {
                            const int term_pos = ppj->position + ppj->offset;
                            Explanation *w = expl_new(1.0,
                                "text window [%d, %d] (size %d <= %d) "
                                "includes [%d]",
                                start_pos, pos,
                                pos - start_pos + 1, window_size,
                                term_pos);

                            const size_t offset = phsc->pp_cnt * ppj->id + i;
                            expl_add_detail(window_explanations[offset], w);
                        }
                    }
                }
            }
        }
        /* check whether a full phrase match occurred */
        if (phrase_prefix && (i == phsc->pp_cnt)) {
            if (phsc->set_phrase_match_flag && self->state) {
                self->state->doc_flags |= FRT_QUERYSTATE_PHRASE_MATCH;
            }
            if (phsc->set_phrase_match_title_keywords_flag && self->state) {
                self->state->doc_flags |=
                    FRT_QUERYSTATE_PHRASE_MATCH_TITLE_KEYWORDS;
            }
        }

        assert(pp->count > 0);
        if (pp_next_position(pp) && check_repeats) {
            pphsc_check_repeats(pp, phsc->phrase_pos, pp_left);
        }
        qsort(phrase_positions, pp_left, sizeof(PhPos *), &pp_pos_or_end_cmp);
    }

    /* Normalize [Similarity.tf], scale [tf_scale] tf values as appropriate. */
    float tf_window_factor = base_tf_score;
    for (i = 0; i < phsc->pp_cnt; ++i) {
        tf_window_factor *= tf_scale;
        int j;
        for (j = 0; j < phsc->pp_cnt; ++j) {
            PhPos *ppj = phsc->phrase_pos[j];
            float tf = ppj->score[i];
            if (phsc->similarity_tf) {
                /* Similarity.tf goes here, if desired: */
                tf = self->similarity->tf(self->similarity, tf);
            }
            tf *= tf_window_factor;
            ppj->score[i] = tf;
        }
    }
 
#ifdef DEBUG_DOC
    float raw_score = 0;
#endif
    if (explanation) {
        float score_increment = base_tf_score;
        int window_size, j;
        for (window_size = 1; window_size <= phsc->pp_cnt; ++window_size) {
            score_increment *= tf_scale;
            for (j = 0; j < phsc->pp_cnt; ++j) {
                const PhPos *ppj = phsc->phrase_pos[j];
                const size_t offset = phsc->pp_cnt * ppj->id + (window_size-1);
                window_explanations[offset]->value = ppj->score[window_size-1];
#ifdef DEBUG_DOC
                raw_score += ppj->score[window_size-1] * ppj->idf;
#endif
            }
        }
        for (window_size = phsc->pp_cnt; window_size > 0; --window_size) {
            for (j = 0; j < phsc->pp_cnt; ++j) {
                const size_t offset = phsc->pp_cnt * j + (window_size-1);
                Explanation *e = window_explanations[offset];
                if (e->value) {
                    expl_add_detail(explanation, e);
                } else {
                    expl_destroy(e);
                }
            }
        }
        free(window_explanations);
        window_explanations = NULL;
    }

#ifdef DEBUG_DOC
    if ((self->doc == watch_doc) && (explanation->value == invalid_expl_value))
    {
        explanation->value = raw_score;

        char *s = expl_to_s_depth(explanation, 0);
        printf("%s", s);
        expl_destroy(explanation);
        explanation = NULL;
    }
#endif

    return;
}

/** Fold pphsc_textscore_tf's values in with Ferret's other parameters.
 *
 *  @param explanation - NULL if no explanation value/detail desired
 */
static float pphsc_score(Scorer *self, Explanation *explanation)
{
    PhraseScorer *phsc = PhSc(self);
    pphsc_textscore_tf(self, explanation);
    float raw_score = 0;
    int i, j;
    for (i = 0; i < phsc->pp_cnt; ++i) {
        for (j = 0; j < phsc->pp_cnt; ++j) {
            float tf = phsc->phrase_pos[j]->score[i];
            assert((phsc->phrase_pos[j]->idf > 0) &&
                "valid idf not set for term");
            raw_score += tf * phsc->phrase_pos[j]->idf;
        }
    }
    /* @todo TODO Provide a real/modelled score normalization. */
    raw_score *= phsc->raw_score_norm_factor *
        powf(phsc->raw_score_term_factor, phsc->pp_cnt);

    if (explanation) {
        /* For consistency with other Explanations, omit normalization
           values from this Explanation's reported value. */
        explanation->value = raw_score;
    }
    /* normalize */
    return raw_score * phsc->value * sim_decode_norm(
        self->similarity,
        phsc->norms[self->doc]);
}

static float pphsc_score_wrapper(Scorer *self)
{
    return pphsc_score(self, NULL);
}

static Explanation *pphsc_explain(Scorer *self, int doc_num)
{
    pphsc_skip_to(self, doc_num);
    if (self->doc == doc_num) {
        Explanation *e = expl_new(0, "total of termwise tf.idf scores");
        pphsc_score(self, e);
        return e;
    } else {
        Explanation *e = expl_new(0, "no words detected");
        return e;
    }
}

/* Examine query's terms to determine which ones are really required to appear
 * in a document for the document to be relevant to the query at all.
 *
 * By automatically marking only the more selective terms as required, we can
 * avoid scoring documents with only occurrences of disproportionately popular
 * words (e.g., stopwords), documents which are unlikely to be relevant to the
 * query anyway.  By making the determination at query time rather than at
 * indexing time, we can decide the status of the same term differently
 * depending on the query in which it resides.
 *
 * By imposing this requirement as an automatic stopword mechanism, we
 * * avoid generating corpus-specific stopword lists (e.g., as Cohen et al.
 *   did for Lucene in the TREC 2007 1MQ track);
 * * allow "to be or not to be"~p to run and get proximity scoring "as usual"
 *   because optional words need not be removed entirely from the query; and
 * * allow recall/performance tuning (the fewer documents qualify for scoring,
 *   the more quickly a search completes).
 *
 * For one approach to this computation, observe that Lucene (and Ferret)
 * compute idf(<term>) as [see Similarity::idf]
 *
 * 	1 + log( <documents in corpus> / (1 + <documents with term>) )
 *
 * which is approximately <constant> - log( <fraction of documents with term> ).
 */
/** Set phrase_pos[0 .. (pp_cnt-1)].stop flags automatically for query.
 *
 *  @param stopword_gap - hint how many orders of magnitude more frequent
 *                        stopwords are than rare terms (e.g., 0.6-2.0)
 */
static void proximity_phrase_stopword_selection(PhPos **phrase_pos, int pp_cnt,
    float stopword_gap)
{
    const float magnitude = logf(10);
    float max_idf = 0;
    int i;
    for (i = 0; i < pp_cnt; ++i) {
        phrase_pos[i]->stop = false;
        if (phrase_pos[i]->idf > max_idf) {
            max_idf = phrase_pos[i]->idf;
        }
    }

    const float min_idf_cutoff = max_idf - (stopword_gap * magnitude);
    for (i = 0; i < pp_cnt; ++i) {
        /* if word is stopword_gap orders of magnitude more frequent than
           rarest word */
        if (phrase_pos[i]->idf < min_idf_cutoff) {
            phrase_pos[i]->stop = true;
        }
    }
}

static Scorer *proximity_phrase_scorer_new(Weight *weight,
                                           TermDocEnum **term_pos_enum,
                                           PhrasePosition *positions, int pp_cnt,
                                           Similarity *similarity, uchar *norms,
                                           float *idf, int scoring_function)
{
    Scorer *self = phsc_new(weight,
                            term_pos_enum,
                            positions,
                            pp_cnt,
                            similarity,
                            norms,
                            0);

    /* set results flags for all fields */
    PhSc(self)->set_phrase_match_flag = true;
    PhSc(self)->set_all_terms_flag    = true;
    PhSc(self)->set_phrase_match_title_keywords_flag = false;
    /* Kosmix-specific behavior: set flags for certain hardwired fields */
    {
        PhraseQuery *q = PhQ(weight->query);
        if ((q->field == intern("title")) || (q->field == intern("keywords"))) {
            PhSc(self)->set_phrase_match_title_keywords_flag = true;
        }
    }

    /* set some default magic values */
    PhSc(self)->similarity_tf = false;
    PhSc(self)->ordered_proximity = false;
    PhSc(self)->conjunctive_proximity = false;
    PhSc(self)->score_stopwords = true;
    /** a stopword is any word 2+ orders of magnitude more frequent than the
        rarest term in the query */
    PhSc(self)->stopword_gap = 2.0;

#if 0
    PhSc(self)->raw_score_norm_factor = 1.0/6.0;
    PhSc(self)->raw_score_term_factor = 1.0/tf_scale;
#endif
    PhSc(self)->raw_score_norm_factor = 1.0;
    PhSc(self)->raw_score_term_factor = 1.0;

    switch (scoring_function) {
    case -2:
        PhSc(self)->similarity_tf = true;
        PhSc(self)->stopword_gap = 1.0;
        break;
    case -3:
        PhSc(self)->similarity_tf = true;
        PhSc(self)->conjunctive_proximity = true;
        break;
    case -1:
    default:
        break;
    };

    int i;
    for (i = 0; i < pp_cnt; ++i) {
        PhSc(self)->phrase_pos[i]->idf = idf[i];
        PhSc(self)->phrase_pos[i]->stop = false;
        PhSc(self)->phrase_pos[i]->score = ALLOC_N(float, pp_cnt);
        PhSc(self)->phrase_pos[i]->score_size = pp_cnt;
    }
    /* Set PhSc(self)->phrase_pos[i]->stop flags. */
    proximity_phrase_stopword_selection(PhSc(self)->phrase_pos, pp_cnt,
        PhSc(self)->stopword_gap);

    PhSc(self)->check_repeats = phsc_check_repeats_flag(positions, pp_cnt);

    self->score       = &pphsc_score_wrapper;
    self->next        = &pphsc_next;
    self->skip_to     = &pphsc_skip_to;
    self->explain     = &pphsc_explain;

    /* Proximity scoring does not use phrase_freq; one is installed here only
     * because the value (number of occurrences of all words in a window)
     * is still well-defined, not because it is still useful here. */
    PhSc(self)->phrase_freq = &sphsc_phrase_freq;
    return self;
}

/***************************************************************************
 *
 * PhraseWeight
 *
 ***************************************************************************/

static char *phw_to_s(Weight *self)
{
    return strfmt("PhraseWeight(%f)", self->value);
}

static bool phw_is_proximity_search(PhraseQuery *self)
{
    /* See q_parser.y:get_phrase_q for slop-value settings. */
    return (self->slop < 0);
}

static Scorer *phw_scorer(Weight *self, IndexReader *ir)
{
    int i;
    Scorer *phsc = NULL;
    PhraseQuery *phq = PhQ(self->query);
    TermDocEnum **tps, *tpe;
    float *idf;
    PhrasePosition *positions = phq->positions;
    const int pos_cnt = phq->pos_cnt;
    const int field_num = fis_get_field_num(ir->fis, phq->field);
    /* See q_parser.y:get_phrase_q for slop-value settings (overload). */
    const int scoring_function = phq->slop;
    const bool fixed_idf_field = false;

    if (pos_cnt == 0 || field_num < 0) {
        return NULL;
    }

    tps = ALLOC_N(TermDocEnum *, pos_cnt);
    /** idf[i] == Similarity-munged idf for term i */
    idf = ALLOC_N(float, pos_cnt);

    for (i = 0; i < pos_cnt; i++) {
        char **terms = positions[i].terms;
        const int t_cnt = ary_size(terms);
        int idf_field_num = field_num;
        if (phw_is_proximity_search(phq) && fixed_idf_field) {
            idf_field_num = fis_get_field_num(ir->fis, intern("content"));
        }
        if (t_cnt == 1) {
            tpe = tps[i] = ir->term_positions(ir);
            tpe->seek(tpe, field_num, terms[0]);
            idf[i] = ir->doc_freq(ir, idf_field_num, terms[0]);
        }
        else {
            tps[i] = mtdpe_new(ir, field_num, terms, t_cnt);
            idf[i] = 0;
            int j;
            for (j = 0; j < t_cnt; ++j) {
                idf[i] += ir->doc_freq(ir, idf_field_num, terms[j]);
            }
        }
        /* neither mtdpe_new nor ir->term_positions should return NULL */
        assert(NULL != tps[i]);
        idf[i] = self->similarity->idf(self->similarity,
                                       idf[i], ir->num_docs(ir));
    }

    if (phw_is_proximity_search(phq)) {
        phsc = proximity_phrase_scorer_new(self, tps, positions, pos_cnt,
                                           self->similarity,
                                           ir_get_norms_i(ir, field_num),
                                           idf, scoring_function);
    } else if (phq->slop == 0) {       /* optimize exact (common) case */
        phsc = exact_phrase_scorer_new(self, tps, positions, pos_cnt,
                                       self->similarity,
                                       ir_get_norms_i(ir, field_num));
    }
    else {
        phsc = sloppy_phrase_scorer_new(self, tps, positions, pos_cnt,
                                        self->similarity, phq->slop,
                                        ir_get_norms_i(ir, field_num));
    }
    free(idf);
    free(tps);
    return phsc;
}

static Explanation *phw_explain(Weight *self, IndexReader *ir, int doc_num)
{
    Explanation *expl;
    Explanation *idf_expl1;
    Explanation *idf_expl2;
    Explanation *query_expl;
    Explanation *qnorm_expl;
    Explanation *field_expl;
    Explanation *tf_expl;
    Scorer *scorer;
    uchar *field_norms;
    float field_norm;
    Explanation *field_norm_expl;
    char *query_str;
    PhraseQuery *phq = PhQ(self->query);
    const int pos_cnt = phq->pos_cnt;
    PhrasePosition *positions = phq->positions;
    int i, j;
    char *doc_freqs = NULL;
    size_t len = 0, pos = 0;
    const int field_num = fis_get_field_num(ir->fis, phq->field);
    const char *field = S(phq->field);

    if (field_num < 0) {
        return expl_new(0.0, "field \"%s\" does not exist in the index", field);
    }

    scorer = self->scorer(self, ir);
    query_str = self->query->to_s(self->query, NULL);

    expl = expl_new(0.0, "weight(%s in %d), product of:", query_str, doc_num);

    /* ensure the phrase positions are in order for explanation */
    qsort(positions, pos_cnt, sizeof(PhrasePosition), &phrase_pos_cmp);

    for (i = 0; i < phq->pos_cnt; i++) {
        char **terms = phq->positions[i].terms;
        for (j = ary_size(terms) - 1; j >= 0; j--) {
            len += strlen(terms[j]) + 40;
        }
    }
    doc_freqs = ALLOC_N(char, len);
    for (i = 0; i < phq->pos_cnt; i++) {
        char **terms = phq->positions[i].terms;
        const int t_cnt = ary_size(terms);
        for (j = 0; j < t_cnt; j++) {
            char *term = terms[j];
            pos += sprintf(doc_freqs + pos, "%s=%d%s, ",
                           term, ir->doc_freq(ir, field_num, term),
                           PhSc(scorer)->phrase_pos[i]->stop ? " [stop]" : "");
        }
    }
    if (phq->pos_cnt > 0) {
        pos -= 2; /* remove ", " from the end */
    }
    doc_freqs[pos] = 0;

    idf_expl1 = expl_new(self->idf, "idf(%s:<%s>)", field, doc_freqs);
    idf_expl2 = expl_new(self->idf, "idf(%s:<%s>)", field, doc_freqs);
    free(doc_freqs);

    /* explain query weight */
    query_expl = expl_new(0.0, "query_weight(%s), product of:", query_str);

    if (self->query->boost != 1.0) {
        expl_add_detail(query_expl, expl_new(self->query->boost, "boost"));
    }
    expl_add_detail(query_expl, idf_expl1);

    qnorm_expl = expl_new(self->qnorm, "query_norm");
    expl_add_detail(query_expl, qnorm_expl);

    query_expl->value = self->query->boost * self->idf * self->qnorm;

    expl_add_detail(expl, query_expl);

    /* explain field weight */
    field_expl = expl_new(0.0, "field_weight(%s in %d), product of:",
                          query_str, doc_num);
    free(query_str);

    tf_expl = scorer->explain(scorer, doc_num);
    scorer->destroy(scorer);
    expl_add_detail(field_expl, tf_expl);
    expl_add_detail(field_expl, idf_expl2);

    field_norms = ir->get_norms(ir, field_num);
    field_norm = (field_norms != NULL)
        ? sim_decode_norm(self->similarity, field_norms[doc_num])
        : (float)0.0;
    field_norm_expl = expl_new(field_norm, "field_norm(field=%s, doc=%d)",
                               field, doc_num);

    expl_add_detail(field_expl, field_norm_expl);

    field_expl->value = tf_expl->value * self->idf * field_norm;

    /* combine them */
    if (query_expl->value == 1.0) {
        expl_destroy(expl);
        return field_expl;
    }
    else {
        expl->value = (query_expl->value * field_expl->value);
        expl_add_detail(expl, field_expl);
        return expl;
    }
}

static Weight *phw_new(Query *query, Searcher *searcher)
{
    Weight *self        = w_new(Weight, query);

    self->scorer        = &phw_scorer;
    self->explain       = &phw_explain;
    self->to_s          = &phw_to_s;

    self->similarity    = query->get_similarity(query, searcher);
    self->value         = query->boost;
    if (phw_is_proximity_search(PhQ(query))) {
        /* per-term idf is moved inside Scorer, so make this idf inert */
        self->idf       = 1;
        self->sum_of_squared_weights(self);
        self->normalize(self, self->qnorm);
    } else {
        self->idf       = sim_idf_phrase(self->similarity, PhQ(query)->field,
                                         PhQ(query)->positions,
                                         PhQ(query)->pos_cnt, searcher);
    }
    return self;
}

/***************************************************************************
 *
 * PhraseQuery
 *
 ***************************************************************************/

/* ** TVPosEnum ** */
typedef struct TVPosEnum
{
    int index;
    int size;
    int offset;
    int pos;
    int positions[1];
} TVPosEnum;

static bool tvpe_next(TVPosEnum *self)
{
    if (++(self->index) < self->size) {
        self->pos = self->positions[self->index] - self->offset;
        return true;
    }
    else {
        self->pos = -1;
        return false;
    }
}

static int tvpe_skip_to(TVPosEnum *self, int position)
{
    int i;
    int search_pos = position + self->offset;
    for (i = self->index + 1; i < self->size; i++) {
        if (self->positions[i] >= search_pos) {
            self->pos = self->positions[i] - self->offset;
            break;
        }
    }
    self->index = i;
    if (i == self->size) {
        self->pos = -1;
        return false;
    }
    return true;
}

static bool tvpe_lt(TVPosEnum *tvpe1, TVPosEnum *tvpe2)
{
    return tvpe1->pos < tvpe2->pos;
}

static TVPosEnum *tvpe_new(int *positions, int size, int offset)
{
    TVPosEnum *self = (TVPosEnum*)emalloc(sizeof(TVPosEnum) + size*sizeof(int));
    memcpy(self->positions, positions, size * sizeof(int));
    self->size = size;
    self->offset = offset;
    self->index = -1;
    self->pos = -1;
    return self;
}

static TVPosEnum *tvpe_new_merge(char **terms, int t_cnt, TermVector *tv,
                                 int offset)
{
    int i, total_positions = 0;
    PriorityQueue *tvpe_pq = pq_new(t_cnt, (lt_ft)tvpe_lt, &free);
    TVPosEnum *self = NULL;

    for (i = 0; i < t_cnt; i++) {
        TVTerm *tv_term = tv_get_tv_term(tv, terms[i]);
        if (tv_term) {
            TVPosEnum *tvpe = tvpe_new(tv_term->positions, tv_term->freq, 0);
            /* got tv_term so tvpe_next should always return true once here */
            bool res = tvpe_next(tvpe);
            assert(res);(void)res;
            pq_push(tvpe_pq, tvpe);
            total_positions += tv_term->freq;
        }
    }
    if (tvpe_pq->size == 0) {
        pq_destroy(tvpe_pq);
    }
    else {
        int index = 0;
        self = (TVPosEnum *)emalloc(sizeof(TVPosEnum)
                                    + total_positions * sizeof(int));
        self->size = total_positions;
        self->offset = offset;
        self->index = -1;
        self->pos = -1;
        while (tvpe_pq->size > 0) {
            TVPosEnum *top = (TVPosEnum *)pq_top(tvpe_pq);
            self->positions[index++] = top->pos;
            if (! tvpe_next(top)) {
                pq_pop(tvpe_pq);
                free(top);
            }
            else {
                pq_down(tvpe_pq);
            }
        }
        pq_destroy(tvpe_pq);
    }
    return self;
}

static TVPosEnum *get_tvpe(TermVector *tv, char **terms, int t_cnt, int offset)
{
    TVPosEnum *tvpe = NULL;
    if (t_cnt == 1) {
        TVTerm *tv_term = tv_get_tv_term(tv, terms[0]);
        if (tv_term) {
            tvpe = tvpe_new(tv_term->positions, tv_term->freq, offset);
        }
    }
    else {
        tvpe = tvpe_new_merge(terms, t_cnt, tv, offset);
    }
    return tvpe;
}

static MatchVector *phq_get_matchv_i(Query *self, MatchVector *mv,
                                     TermVector *tv)
{
    if (tv->field == PhQ(self)->field) {
        const int pos_cnt = PhQ(self)->pos_cnt;
        int i;
        int slop = PhQ(self)->slop;
        bool done = false;

        if (slop > 0) {
            PriorityQueue *tvpe_pq = pq_new(pos_cnt, (lt_ft)tvpe_lt, &free);
            int last_pos = 0;
            for (i = 0; i < pos_cnt; i++) {
                PhrasePosition *pp = &(PhQ(self)->positions[i]);
                const int t_cnt = ary_size(pp->terms);
                TVPosEnum *tvpe = get_tvpe(tv, pp->terms, t_cnt, pp->pos);
                if (tvpe && tvpe_next(tvpe)) {
                    if (tvpe->pos > last_pos) {
                        last_pos = tvpe->pos;
                    }
                    pq_push(tvpe_pq, tvpe);
                }
                else {
                    done = true;
                    free(tvpe);
                    break;
                }
            }
            while (! done) {
                TVPosEnum *tvpe = (TVPosEnum *)pq_pop(tvpe_pq);
                int pos;
                int start = pos = tvpe->pos;
                int next_pos = ((TVPosEnum *)pq_top(tvpe_pq))->pos;
                while (pos <= next_pos) {
                    start = pos;
                    if (!tvpe_next(tvpe)) {
                        done = true;
                        break;
                    }
                    pos = tvpe->pos;
                }

                if (last_pos - start <= slop) {
                    int min, max = min = start + tvpe->offset;
                    for (i = tvpe_pq->size; i > 0; i--) {
                        TVPosEnum *t = (TVPosEnum *)tvpe_pq->heap[i];
                        int p = t->pos + t->offset;
                        max = p > max ? p : max;
                        min = p < min ? p : min;
                    }
                    matchv_add(mv, min, max);
                }
                if (tvpe->pos > last_pos) {
                    last_pos = tvpe->pos;
                }
                pq_push(tvpe_pq, tvpe);
            }

            pq_destroy(tvpe_pq);
        }
        else { /* exact match */
            TVPosEnum **tvpe_a = ALLOC_AND_ZERO_N(TVPosEnum *, pos_cnt);
            TVPosEnum *first, *last;
            int first_index = 0;
            done = false;
            qsort(PhQ(self)->positions, pos_cnt, sizeof(PhrasePosition),
                  &phrase_pos_cmp);
            for (i = 0; i < pos_cnt; i++) {
                PhrasePosition *pp = &(PhQ(self)->positions[i]);
                const int t_cnt = ary_size(pp->terms);
                TVPosEnum *tvpe = get_tvpe(tv, pp->terms, t_cnt, pp->pos);
                if (tvpe && ((i == 0 && tvpe_next(tvpe))
                             || tvpe_skip_to(tvpe, tvpe_a[i-1]->pos))) {
                    tvpe_a[i] = tvpe;
                }
                else {
                    done = true;
                    free(tvpe);
                    break;
                }
            }

            first = tvpe_a[0];
            last = tvpe_a[pos_cnt - 1];

            while (!done) {
                while (first->pos < last->pos) {
                    if (tvpe_skip_to(first, last->pos)) {
                        last = first;
                        first_index = NEXT_NUM(first_index, pos_cnt);
                        first = tvpe_a[first_index];
                    }
                    else {
                        done = true;
                        break;
                    }
                }
                if (!done) {
                    matchv_add(mv, tvpe_a[0]->pos + tvpe_a[0]->offset,
                               tvpe_a[pos_cnt-1]->pos + tvpe_a[pos_cnt-1]->offset);
                }
                if (!tvpe_next(last)) {
                    done = true;
                }
            }
            for (i = 0; i < pos_cnt; i++) {
                free(tvpe_a[i]);
            }
            free(tvpe_a);
        }
    }
    return mv;
}


/* ** PhraseQuery besides highlighting stuff ** */

#define PhQ_INIT_CAPA 4

static void phq_extract_terms(Query *self, HashSet *term_set)
{
    PhraseQuery *phq = PhQ(self);
    int i, j;
    for (i = 0; i < phq->pos_cnt; i++) {
        char **terms = phq->positions[i].terms;
        for (j = ary_size(terms) - 1; j >= 0; j--) {
            hs_add(term_set, term_new(phq->field, terms[j]));
        }
    }
}

static char *phq_to_s(Query *self, Symbol default_field)
{
    PhraseQuery *phq = PhQ(self);
    const int pos_cnt = phq->pos_cnt;
    PhrasePosition *positions = phq->positions;
    const char *field = S(phq->field);
    int flen = strlen(field);

    int i, j, buf_index = 0, pos, last_pos;
    size_t len = 0;
    char *buffer;

    if (phq->pos_cnt == 0) {
        if (default_field != phq->field) {
            return strfmt("%s:\"\"", field);
        }
        else {
            return estrdup("\"\"");
        }
    }

    /* sort the phrase positions by position */
    qsort(positions, pos_cnt, sizeof(PhrasePosition), &phrase_pos_cmp);

    len = flen + 1;

    for (i = 0; i < pos_cnt; i++) {
        char **terms = phq->positions[i].terms;
        for (j = ary_size(terms) - 1; j >= 0; j--) {
            len += strlen(terms[j]) + 5;
        }
    }

    /* add space for extra <> characters and boost and slop */
    len += 100 + 3
        * (phq->positions[phq->pos_cnt - 1].pos - phq->positions[0].pos);

    buffer = ALLOC_N(char, len);

    if (default_field != phq->field) {
        memcpy(buffer, field, flen);
        buffer[flen] = ':';
        buf_index += flen + 1;
    }

    buffer[buf_index++] = '"';

    last_pos = positions[0].pos - 1;
    for (i = 0; i < pos_cnt; i++) {
        char **terms = positions[i].terms;
        const int t_cnt = ary_size(terms);

        pos = positions[i].pos;
        if (pos == last_pos) {
            buffer[buf_index - 1] = '&';
        }
        else {
            for (j = last_pos; j < pos - 1; j++) {
                memcpy(buffer + buf_index, "<> ", 3);
                buf_index += 3;
            }
        }

        last_pos = pos;
        for (j = 0; j < t_cnt; j++) {
            char *term = terms[j];
            len = strlen(term);
            memcpy(buffer + buf_index, term, len);
            buf_index += len;
            buffer[buf_index++] = '|';
        }
        buffer[buf_index-1] = ' '; /* change last '|' to ' ' */
    }

    if (buffer[buf_index-1] == ' ') {
        buf_index--;
    }

    buffer[buf_index++] = '"';
    buffer[buf_index] = 0;

    if (phq->slop != 0) {
        buf_index += sprintf(buffer + buf_index, "~%d", phq->slop);
    }

    if (self->boost != 1.0) {
        buffer[buf_index++] = '^';
        dbl_to_s(buffer + buf_index, self->boost);
    }

    return buffer;
}

static void phq_destroy(Query *self)
{
    PhraseQuery *phq = PhQ(self);
    int i;
    for (i = 0; i < phq->pos_cnt; i++) {
        ary_destroy(phq->positions[i].terms, &free);
    }
    free(phq->positions);
    q_destroy_i(self);
}

static Query *phq_rewrite(Query *self, IndexReader *ir)
{
    PhraseQuery *phq = PhQ(self);
    (void)ir;
    if ((phq->pos_cnt == 1) && !phw_is_proximity_search(phq)) {
        /* optimize one-position case */
        char **terms = phq->positions[0].terms;
        const int t_cnt = ary_size(terms);
        if (t_cnt == 1) {
            Query *tq = tq_new(phq->field, terms[0]);
            tq->boost = self->boost;
            return tq;
        }
        else {
            Query *q = multi_tq_new(phq->field);
            int i;
            for (i = 0; i < t_cnt; i++) {
                multi_tq_add_term(q, terms[i]);
            }
            q->boost = self->boost;
            return q;
        }
    } else {
        self->ref_cnt++;
        return self;
    }
}

static unsigned long phq_hash(Query *self)
{
    int i, j;
    PhraseQuery *phq = PhQ(self);
    unsigned long hash = sym_hash(phq->field);
    for (i = 0; i < phq->pos_cnt; i++) {
        char **terms = phq->positions[i].terms;
        for (j = ary_size(terms) - 1; j >= 0; j--) {
            hash = (hash << 1) ^ (str_hash(terms[j])
                                  ^ phq->positions[i].pos);
        }
    }
    return (hash ^ phq->slop);
}

static int phq_eq(Query *self, Query *o)
{
    int i, j;
    PhraseQuery *phq1 = PhQ(self);
    PhraseQuery *phq2 = PhQ(o);
    if (phq1->slop != phq2->slop
        || phq1->field != phq2->field
        || phq1->pos_cnt != phq2->pos_cnt) {
        return false;
    }
    for (i = 0; i < phq1->pos_cnt; i++) {
        char **terms1 = phq1->positions[i].terms;
        char **terms2 = phq2->positions[i].terms;
        const int t_cnt = ary_size(terms1);
        if (t_cnt != ary_size(terms2)
            || phq1->positions[i].pos != phq2->positions[i].pos) {
            return false;
        }
        for (j = 0; j < t_cnt; j++) {
            if (strcmp(terms1[j], terms2[j]) != 0) {
                return false;
            }
        }
    }
    return true;
}

Query *phq_new(Symbol field)
{
    Query *self = q_new(PhraseQuery);

    PhQ(self)->field        = field;
    PhQ(self)->pos_cnt      = 0;
    PhQ(self)->pos_capa     = PhQ_INIT_CAPA;
    PhQ(self)->positions    = ALLOC_N(PhrasePosition, PhQ_INIT_CAPA);

    self->type              = PHRASE_QUERY;
    self->rewrite           = &phq_rewrite;
    self->extract_terms     = &phq_extract_terms;
    self->to_s              = &phq_to_s;
    self->hash              = &phq_hash;
    self->eq                = &phq_eq;
    self->destroy_i         = &phq_destroy;
    self->create_weight_i   = &phw_new;
    self->get_matchv_i      = &phq_get_matchv_i;
    return self;
}

void phq_add_term_abs(Query *self, const char *term, int position)
{
    PhraseQuery *phq = PhQ(self);
    int index = phq->pos_cnt;
    PhrasePosition *pp;
    if (index >= phq->pos_capa) {
        phq->pos_capa <<= 1;
        REALLOC_N(phq->positions, PhrasePosition, phq->pos_capa);
    }
    pp = &(phq->positions[index]);
    pp->terms = ary_new_type_capa(char *, 2);
    ary_push(pp->terms, estrdup(term));
    pp->pos = position;
    phq->pos_cnt++;
}

void phq_add_term(Query *self, const char *term, int pos_inc)
{
    PhraseQuery *phq = PhQ(self);
    int position;
    if (phq->pos_cnt == 0) {
        position = 0;
    }
    else {
        position = phq->positions[phq->pos_cnt - 1].pos + pos_inc;
    }
    phq_add_term_abs(self, term, position);
}

void phq_append_multi_term(Query *self, const char *term)
{
    PhraseQuery *phq = PhQ(self);
    int index = phq->pos_cnt - 1;

    if (index < 0) {
        phq_add_term(self, term, 0);
    }
    else {
        ary_push(phq->positions[index].terms, estrdup(term));
    }
}

void frt_phq_set_slop(FrtQuery *self, int slop)
{
    PhQ(self)->slop = slop;
}
