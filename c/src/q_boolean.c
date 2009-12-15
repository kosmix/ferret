#include <string.h>
#include "search.h"
#include "array.h"
#include "internal.h"

#define BQ(query) ((BooleanQuery *)(query))
#define BW(weight) ((BooleanWeight *)(weight))

/***************************************************************************
 *
 * BooleanScorer
 *
 ***************************************************************************/

/***************************************************************************
 * Coordinator
 ***************************************************************************/

typedef struct Coordinator
{
    int max_coord;
    float *coord_factors;
    Similarity *similarity;
    int num_matches;
} Coordinator;

static Coordinator *coord_new(Similarity *similarity)
{
    Coordinator *self = ALLOC_AND_ZERO(Coordinator);
    self->similarity = similarity;
    return self;
}

static Coordinator *coord_init(Coordinator *self)
{
    int i;
    self->coord_factors = ALLOC_N(float, self->max_coord + 1);

    for (i = 0; i <= self->max_coord; i++) {
        self->coord_factors[i]
            = sim_coord(self->similarity, i, self->max_coord);
    }

    return self;
}

/***************************************************************************
 * DisjunctionSumScorer
 ***************************************************************************/

#define DSSc(scorer) ((DisjunctionSumScorer *)(scorer))

typedef struct DisjunctionSumScorer
{
    Scorer          super;
    float           cum_score;
    int             num_matches;
    int             min_num_matches;
    Scorer        **sub_scorers;
    int             ss_cnt;
    /** current_scorers[0, num_matches) point to scorers at super.doc. */
    Scorer        **current_scorers;
    /** current_scorers[0, current_scorers_end) point to scorers with docs. */
    int             current_scorers_end;
    Coordinator    *coordinator;
} DisjunctionSumScorer;

static float dssc_score(Scorer *self)
{
    DisjunctionSumScorer *dssc = DSSc(self);
    Scorer **current_scorers = dssc->current_scorers;

    assert(dssc->num_matches <= dssc->current_scorers_end);
    assert(dssc->current_scorers_end <= dssc->ss_cnt);
    if (dssc->cum_score == 0) {
        int i;
        for (i = 0; i < dssc->num_matches; ++i) {
            dssc->cum_score += current_scorers[i]->score(current_scorers[i]);
        }
    }
    return dssc->cum_score;
}

static void swap_scorers(Scorer **a, Scorer **b)
{
    Scorer *tmp = *a;
    *a = *b;
    *b = tmp;
}

/** Resort current_scorers[0, current_scorers_end) into a valid state.
 *
 *  A valid state requires a constructed dssc->current_scorers (as built by
 *  dssc_init_current_scorers), sorted into two regions such that
 *    dssc->current_scorers[0, dssc->num_matches)
 *      consists of all Scorers at self->doc; and
 *    dssc->current_scorers(dssc->num_matches, dssc->current_scorers_end)
 *      consists of Scorers at documents greater than self->doc (i.e., at a
 *      document in the range (self->doc, INT_MAX)).
 *  (Either/both of the regions can be empty.)
 *    dssc->current_scorers(dssc->current_scorers_end, dssc->ss_cnt) is unused.
 *
 *  Every scorer at a document (i.e., that has not run out of documents) must
 *  appear in dssc->current_scorers[0, dssc->current_scorers_end).
 *
 *  If self->doc != INT_MAX, no scorer in dssc->sub_scorers is at any document
 *    earlier than self->doc.
 *  If self->doc == INT_MAX, not enough scorers remain at some document to
 *    satisfy dssc->min_num_matches.
 *
 *  This function assumes that current_scorers[0, current_scorers_end) contains
 *  the only scorers left with documents available (e.g., after some changes
 *  to the scorers changed their state).  This function rearranges the array to
 *  create the two regions and sets dssc->num_matches and self->doc accordingly.
 */
static void dssc_sort_current_scorers(DisjunctionSumScorer *dssc)
{
    Scorer **current_scorers = dssc->current_scorers;
    int min_doc = INT_MAX, min_end = 0, i;
    for (i = 0; i < dssc->current_scorers_end; ++i) {
        if (current_scorers[i]->doc < min_doc) {
            min_doc = current_scorers[i]->doc;
            min_end = 0;
        }
        if (current_scorers[i]->doc == min_doc) {
            assert(min_end < dssc->current_scorers_end);
            swap_scorers(&current_scorers[min_end], &current_scorers[i]);
            ++min_end;
        }
    }
    dssc->super.doc = min_doc;
    dssc->num_matches = min_end;
    dssc->cum_score = 0;
    assert(dssc->num_matches <= dssc->current_scorers_end);
}

/** Allocate and fill dssc->current_scorers (and current_scorers_end). */
static void dssc_init_current_scorers(DisjunctionSumScorer *dssc)
{
    int i;
    Scorer *sub_scorer;
    dssc->current_scorers = calloc(dssc->ss_cnt, sizeof(Scorer *));
    dssc->current_scorers_end = 0;

    for (i = 0; i < dssc->ss_cnt; i++) {
        sub_scorer = dssc->sub_scorers[i];
        sub_scorer->state = dssc->super.state;
        if (sub_scorer->next(sub_scorer)) {
            dssc->current_scorers[dssc->current_scorers_end] = sub_scorer;
            ++dssc->current_scorers_end;
        }
    }
    assert(dssc->current_scorers_end >= 0);
    assert(dssc->current_scorers_end <= dssc->ss_cnt);

    dssc_sort_current_scorers(dssc);
}

/** Advance current_scorers[0, num_matches) (the ones at self->doc). */
static void dssc_current_scorers_next(Scorer *self)
{
    DisjunctionSumScorer *dssc = DSSc(self);
    Scorer **current_scorers = dssc->current_scorers;
    int i;

    assert(current_scorers);
    assert(dssc->num_matches <= dssc->current_scorers_end);
    assert(dssc->current_scorers_end <= dssc->ss_cnt);
    i = 0;
    while (i < dssc->num_matches) {
        if (current_scorers[i]->next(current_scorers[i])) {
            ++i;
        } else {
            /* Scorer *tmp = current_scorers[i]; */
            --dssc->num_matches;
            --dssc->current_scorers_end;
            current_scorers[i] = current_scorers[dssc->num_matches];
            current_scorers[dssc->num_matches] =
                current_scorers[dssc->current_scorers_end];
            /* This last step completes this swap, but is not necessary: */
            /* current_scorers[dssc->current_scorers_end] = tmp; */
        }
    }
    assert(dssc->current_scorers_end >= 0);
    assert(dssc->current_scorers_end <= dssc->ss_cnt);

    dssc_sort_current_scorers(dssc);
}

/** Advance scorers as needed until self->doc satisfies min_num_matches. */
static bool dssc_advance_to_current(Scorer *self)
{
    DisjunctionSumScorer *dssc = DSSc(self);

    // while (dssc->num_matches + scorer_queue->size >= dssc->min_num_matches) {
    while (dssc->current_scorers_end >= dssc->min_num_matches) {
        if (self->state && self->state->is_aborted &&
            self->state->is_aborted(self->state->is_aborted_param)) {
            return false;
        }

        assert(dssc->num_matches <= dssc->current_scorers_end);
        assert(dssc->current_scorers_end <= dssc->ss_cnt);
        if (dssc->num_matches < dssc->min_num_matches) {
            dssc_current_scorers_next(self);
        } else {
            return true;
        }
    }

    /* Here, it is impossible to collect dssc->min_num_matches scorers into
       dssc->current_scorers (i.e., aligned at any self->doc left), because
       there are too few usable scorers left. */
    return false;
}

static bool dssc_next(Scorer *self)
{
    if (DSSc(self)->current_scorers == NULL) {
        dssc_init_current_scorers(DSSc(self));
    }
    else {
        dssc_current_scorers_next(self);
    }
    return dssc_advance_to_current(self);
}

static bool dssc_skip_to(Scorer *self, int doc_num)
{
    DisjunctionSumScorer *dssc = DSSc(self);

    if (dssc->current_scorers == NULL) {
        dssc_init_current_scorers(dssc);
    }
    else if (doc_num <= self->doc) {
        if ((self->doc != INT_MAX) && (self->doc != -1)) {
            return true;
        } else {
            return false;
        }
    }

    if (dssc->current_scorers_end < dssc->min_num_matches) {
        assert(self->doc == INT_MAX);
        return false;
    }
    if (doc_num > self->doc) {
        /* Advance scorers to at least doc_num as needed. */
        Scorer **current_scorers = dssc->current_scorers;
        int i = 0;
        while (i < dssc->current_scorers_end) {
            if (current_scorers[i]->skip_to(current_scorers[i], doc_num)) {
                ++i;
            } else {
                --dssc->current_scorers_end;
                /* A swap is not strictly necessary: */
                current_scorers[i] = current_scorers[dssc->current_scorers_end];
                /* swap_scorers(&current_scorers[i],
                    &current_scorers[dssc->current_scorers_end]); */
            }
        }
        dssc_sort_current_scorers(dssc);
    }
    return dssc_advance_to_current(self);
}

static Explanation *dssc_explain(Scorer *self, int doc_num)
{
    int i;
    DisjunctionSumScorer *dssc = DSSc(self);
    Scorer *sub_scorer;
    Explanation *e
        = expl_new(0.0, "At least %d of:", dssc->min_num_matches);
    for (i = 0; i < dssc->ss_cnt; i++) {
        sub_scorer = dssc->sub_scorers[i];
        expl_add_detail(e, sub_scorer->explain(sub_scorer, doc_num));
    }
    return e;
}

static void dssc_destroy(Scorer *self)
{
    DisjunctionSumScorer *dssc = DSSc(self);
    int i;
    for (i = 0; i < dssc->ss_cnt; i++) {
        dssc->sub_scorers[i]->destroy(dssc->sub_scorers[i]);
    }
    free(dssc->current_scorers);
    scorer_destroy_i(self);
}

static Scorer *disjunction_sum_scorer_new(Scorer **sub_scorers, int ss_cnt,
                                          int min_num_matches) 
{
    Scorer *self = scorer_new(DisjunctionSumScorer, NULL);
    DSSc(self)->ss_cnt = ss_cnt;

    /* The document number of the current match */
    self->doc = -1;
    DSSc(self)->cum_score = -1.0;

    /* The number of subscorers that provide the current match. */
    DSSc(self)->num_matches = 0;
    DSSc(self)->coordinator = NULL;

#ifdef DEBUG
    if (min_num_matches <= 0) {
        RAISE(ARG_ERROR, "The min_num_matches value <%d> should not be less "
              "than 0\n", min_num_matches);
    }
    if (ss_cnt <= 1) {
        RAISE(ARG_ERROR, "There should be at least 2 sub_scorers in a "
              "DiscjunctionSumScorer. <%d> is not enough", ss_cnt);
    }
#endif

    DSSc(self)->min_num_matches     = min_num_matches;
    DSSc(self)->sub_scorers         = sub_scorers;
    DSSc(self)->current_scorers     = NULL;
    DSSc(self)->current_scorers_end = 0;

    self->score   = &dssc_score;
    self->next    = &dssc_next;
    self->skip_to = &dssc_skip_to;
    self->explain = &dssc_explain;
    self->destroy = &dssc_destroy;

    return self;
}

static float cdssc_score(Scorer *self)
{
    DSSc(self)->coordinator->num_matches += DSSc(self)->num_matches;
    return dssc_score(self);
}

static Scorer *counting_disjunction_sum_scorer_new(
    Coordinator *coordinator, Scorer **sub_scorers, int ss_cnt,
    int min_num_matches)
{
    Scorer *self = disjunction_sum_scorer_new(sub_scorers, ss_cnt,
                                              min_num_matches);
    DSSc(self)->coordinator = coordinator;
    self->score = &cdssc_score;
    return self;
}

/***************************************************************************
 * ConjunctionScorer
 ***************************************************************************/

#define CSc(scorer) ((ConjunctionScorer *)(scorer))

typedef struct ConjunctionScorer
{
    Scorer          super;
    bool            first_time : 1;
    bool            more : 1;
    float           coord;
    Scorer        **sub_scorers;
    int             ss_cnt;
    int             first_idx;
    Coordinator    *coordinator;
    int             last_scored_doc;
} ConjunctionScorer;

static void csc_sort_scorers(ConjunctionScorer *csc)
{
    int i;
    Scorer *current = csc->sub_scorers[0], *previous;
    for (i = 1; i < csc->ss_cnt; i++) {
        previous = current;
        current = csc->sub_scorers[i];
        if (previous->doc > current->doc) {
            if (!current->skip_to(current, previous->doc)) {
                csc->more = false;
                return;
            }
        }
    }
    /*qsort(csc->sub_scorers, csc->ss_cnt, sizeof(Scorer *), &scorer_doc_cmp);*/
    csc->first_idx = 0;
}

static void csc_init(Scorer *self, bool init_scorers)
{
    ConjunctionScorer *csc = CSc(self);
    const int sub_sc_cnt = csc->ss_cnt;

    /* compute coord factor */
    csc->coord = sim_coord(self->similarity, sub_sc_cnt, sub_sc_cnt);

    csc->more = (sub_sc_cnt > 0);

    if (init_scorers) {
        int i;
        /* move each scorer to its first entry */
        for (i = 0; i < sub_sc_cnt; i++) {
            Scorer *sub_scorer = csc->sub_scorers[i];
            sub_scorer->state = self->state;
            if (!csc->more) {
                break;
            }
            csc->more = sub_scorer->next(sub_scorer);
        }
        if (csc->more) {
            csc_sort_scorers(csc);
        }
    }

    csc->first_time = false;
}

static float csc_score(Scorer *self)
{
    ConjunctionScorer *csc = CSc(self);
    const int sub_sc_cnt = csc->ss_cnt;
    float score = 0.0; /* sum scores */
    int i;
    for (i = 0; i < sub_sc_cnt; i++) {
        Scorer *sub_scorer = csc->sub_scorers[i];
        score += sub_scorer->score(sub_scorer);
    }
    score *= csc->coord;
    return score;
}

static bool csc_do_next(Scorer *self)
{
    ConjunctionScorer *csc = CSc(self);
    const int sub_sc_cnt = csc->ss_cnt;
    int first_idx = csc->first_idx;
    Scorer *first_sc = csc->sub_scorers[first_idx];
    Scorer *last_sc = csc->sub_scorers[PREV_NUM(first_idx, sub_sc_cnt)];

    /* skip to doc with all clauses */
    while (csc->more && (first_sc->doc < last_sc->doc)) {
        if (self->state && self->state->is_aborted &&
            self->state->is_aborted(self->state->is_aborted_param))
        {
            return false;
        }
        /* skip first upto last */
        csc->more = first_sc->skip_to(first_sc, last_sc->doc);
        /* move first to last */
        last_sc = first_sc;
        first_idx = NEXT_NUM(first_idx, sub_sc_cnt);
        first_sc = csc->sub_scorers[first_idx];
    }
    self->doc = first_sc->doc;
    csc->first_idx = first_idx;
    return csc->more;
}

static bool csc_next(Scorer *self)
{
    ConjunctionScorer *csc = CSc(self);
    if (csc->first_time) {
        csc_init(self, true);
    }
    else if (self->state && self->state->is_aborted &&
             self->state->is_aborted(self->state->is_aborted_param)) {
        return false;
    }
    else if (csc->more) {
        /* trigger further scanning */
        const int last_idx = PREV_NUM(csc->first_idx, csc->ss_cnt);
        Scorer *sub_scorer = csc->sub_scorers[last_idx];
        csc->more = sub_scorer->next(sub_scorer);
    }
    return csc_do_next(self);
}

static bool csc_skip_to(Scorer *self, int doc_num)
{
    ConjunctionScorer *csc = CSc(self);
    const int sub_sc_cnt = csc->ss_cnt;
    int i;
    bool more = csc->more;

    if (csc->first_time) {
        csc_init(self, false);
    }

    for (i = 0; i < sub_sc_cnt; i++) {
        if (!more) {
            break;
        }
        else {
            Scorer *sub_scorer = csc->sub_scorers[i];
            more = sub_scorer->skip_to(sub_scorer, doc_num);
        }
    }
    if (more) {
        /* resort the scorers */
        csc_sort_scorers(csc);
    }

    csc->more = more;
    return csc_do_next(self);
}

static void csc_destroy(Scorer *self)
{
    ConjunctionScorer *csc = CSc(self);
    const int sub_sc_cnt = csc->ss_cnt;
    int i;
    for (i = 0; i < sub_sc_cnt; i++) {
        csc->sub_scorers[i]->destroy(csc->sub_scorers[i]);
    }
    free(csc->sub_scorers);
    scorer_destroy_i(self);
}

static Scorer *conjunction_scorer_new(Similarity *similarity) 
{
    Scorer *self = scorer_new(ConjunctionScorer, similarity);

    CSc(self)->first_time   = true;
    CSc(self)->more         = true;
    CSc(self)->coordinator  = NULL;

    self->score             = &csc_score;
    self->next              = &csc_next;
    self->skip_to           = &csc_skip_to;
    self->destroy           = &csc_destroy;

    return self;
}

static float ccsc_score(Scorer *self)
{
    ConjunctionScorer *csc = CSc(self);

    int doc;
    if ((doc = self->doc) > csc->last_scored_doc) {
        csc->last_scored_doc = doc;
        csc->coordinator->num_matches += csc->ss_cnt;
    }

    return csc_score(self);
}

static Scorer *counting_conjunction_sum_scorer_new(Similarity *similarity,
    Coordinator *coordinator, Scorer **sub_scorers, int ss_cnt)
{
    Scorer *self = conjunction_scorer_new(similarity);
    ConjunctionScorer *csc = CSc(self);
    csc->coordinator = coordinator;
    csc->last_scored_doc = -1;
    csc->sub_scorers = ALLOC_N(Scorer *, ss_cnt);
    memcpy(csc->sub_scorers, sub_scorers, sizeof(Scorer *) * ss_cnt);
    csc->ss_cnt = ss_cnt;

    self->score = &ccsc_score;

    return self;
}

/***************************************************************************
 * SingleMatchScorer
 ***************************************************************************/

#define SMSc(scorer) ((SingleMatchScorer *)(scorer))

typedef struct SingleMatchScorer
{
    Scorer          super;
    Coordinator    *coordinator;
    Scorer         *scorer;
} SingleMatchScorer;


static float smsc_score(Scorer *self)
{
    SMSc(self)->coordinator->num_matches++;
    return SMSc(self)->scorer->score(SMSc(self)->scorer);
}

static bool smsc_next(Scorer *self)
{
    Scorer *scorer = SMSc(self)->scorer;
    if (scorer->state != self->state) {
        scorer->state = self->state;
    }
    if (scorer->next(scorer)) {
        self->doc = scorer->doc;
        return true;
    }
    return false;
}

static bool smsc_skip_to(Scorer *self, int doc_num)
{
    Scorer *scorer = SMSc(self)->scorer;
    if (scorer->skip_to(scorer, doc_num)) {
        self->doc = scorer->doc;
        return true;
    }
    return false;
}

static Explanation *smsc_explain(Scorer *self, int doc_num)
{
    Scorer *scorer = SMSc(self)->scorer;
    return scorer->explain(scorer, doc_num);
}

static void smsc_destroy(Scorer *self)
{
    Scorer *scorer = SMSc(self)->scorer;
    scorer->destroy(scorer);
    scorer_destroy_i(self);
}

static Scorer *single_match_scorer_new(Coordinator *coordinator,
                                       Scorer *scorer)
{
    Scorer *self = scorer_new(SingleMatchScorer, scorer->similarity);
    SMSc(self)->coordinator = coordinator;
    SMSc(self)->scorer      = scorer;

    self->score             = &smsc_score;
    self->next              = &smsc_next;
    self->skip_to           = &smsc_skip_to;
    self->explain           = &smsc_explain;
    self->destroy           = &smsc_destroy;
    return self;
}

/***************************************************************************
 * ReqOptSumScorer
 ***************************************************************************/

#define ROSSc(scorer) ((ReqOptSumScorer *)(scorer))

typedef struct ReqOptSumScorer
{
    Scorer  super;
    Scorer *req_scorer;
    Scorer *opt_scorer;
    bool    first_time_opt;
} ReqOptSumScorer;

static float rossc_score(Scorer *self)
{
    ReqOptSumScorer *rossc = ROSSc(self);
    Scorer *req_scorer = rossc->req_scorer;
    Scorer *opt_scorer = rossc->opt_scorer;
    int cur_doc = req_scorer->doc;
    float req_score = req_scorer->score(req_scorer);

    if (rossc->first_time_opt) {
        rossc->first_time_opt = false;
        if (! opt_scorer->skip_to(opt_scorer, cur_doc)) {
            SCORER_NULLIFY(rossc->opt_scorer);
            return req_score;
        }
    }
    else if (opt_scorer == NULL) {
        return req_score;
    }
    else if ((opt_scorer->doc < cur_doc)
             && ! opt_scorer->skip_to(opt_scorer, cur_doc)) {
        SCORER_NULLIFY(rossc->opt_scorer);
        return req_score;
    }
    /* assert (@opt_scorer != nil) and (@opt_scorer.doc() >= cur_doc) */
    return (opt_scorer->doc == cur_doc)
        ? req_score + opt_scorer->score(opt_scorer)
        : req_score;
}

static bool rossc_next(Scorer *self)
{
    Scorer *req_scorer = ROSSc(self)->req_scorer;
    if (req_scorer->state != self->state) {
        req_scorer->state = self->state;
    }
    Scorer *opt_scorer = ROSSc(self)->opt_scorer;
    if (opt_scorer && (opt_scorer->state != self->state)) {
        opt_scorer->state = self->state;
    }
    if (req_scorer->next(req_scorer)) {
        self->doc = req_scorer->doc;
        return true;
    }
    return false;
}

static bool rossc_skip_to(Scorer *self, int doc_num)
{
    Scorer *req_scorer = ROSSc(self)->req_scorer;
    if (req_scorer->skip_to(req_scorer, doc_num)) {
        self->doc = req_scorer->doc;
        return true;
    }
    return false;
}

static Explanation *rossc_explain(Scorer *self, int doc_num)
{
    Scorer *req_scorer = ROSSc(self)->req_scorer;
    Scorer *opt_scorer = ROSSc(self)->opt_scorer;

    Explanation *e = expl_new(self->score(self),"required, optional:");
    expl_add_detail(e, req_scorer->explain(req_scorer, doc_num));
    expl_add_detail(e, opt_scorer->explain(opt_scorer, doc_num));
    return e;
}

static void rossc_destroy(Scorer *self)
{
    ReqOptSumScorer *rossc = ROSSc(self);
    if (rossc->req_scorer) {
        rossc->req_scorer->destroy(rossc->req_scorer);
    }
    if (rossc->opt_scorer) {
        rossc->opt_scorer->destroy(rossc->opt_scorer);
    }
    scorer_destroy_i(self);
}


static Scorer *req_opt_sum_scorer_new(Scorer *req_scorer, Scorer *opt_scorer)
{
    Scorer *self = scorer_new(ReqOptSumScorer, NULL);

    ROSSc(self)->req_scorer     = req_scorer;
    ROSSc(self)->opt_scorer     = opt_scorer;
    ROSSc(self)->first_time_opt = true;

    self->score   = &rossc_score;
    self->next    = &rossc_next;
    self->skip_to = &rossc_skip_to;
    self->explain = &rossc_explain;
    self->destroy = &rossc_destroy;

    return self;
}

/***************************************************************************
 * ReqExclScorer
 ***************************************************************************/

#define RXSc(scorer) ((ReqExclScorer *)(scorer))
typedef struct ReqExclScorer
{
    Scorer  super;
    Scorer *req_scorer;
    Scorer *excl_scorer;
    bool    first_time;
} ReqExclScorer;

static bool rxsc_to_non_excluded(Scorer *self)
{
    Scorer *req_scorer = RXSc(self)->req_scorer;
    Scorer *excl_scorer = RXSc(self)->excl_scorer;
    int excl_doc = excl_scorer->doc, req_doc;

    do { 
        /* may be excluded */
        req_doc = req_scorer->doc;
        if (req_doc < excl_doc) {
            /* req_scorer advanced to before excl_scorer, ie. not excluded */
            self->doc = req_doc;
            return true;
        }
        else if (req_doc > excl_doc) {
            if (! excl_scorer->skip_to(excl_scorer, req_doc)) {
                /* emptied, no more exclusions */
                SCORER_NULLIFY(RXSc(self)->excl_scorer);
                self->doc = req_doc;
                return true;
            }
            excl_doc = excl_scorer->doc;
            if (excl_doc > req_doc) {
                self->doc = req_doc;
                return true; /* not excluded */
            }
        }
    } while (req_scorer->next(req_scorer));
    /* emptied, nothing left */
    SCORER_NULLIFY(RXSc(self)->req_scorer);
    return false;
}

static bool rxsc_next(Scorer *self)
{
    ReqExclScorer *rxsc = RXSc(self);
    Scorer *req_scorer = rxsc->req_scorer;
    Scorer *excl_scorer = rxsc->excl_scorer;

    if (rxsc->first_time) {
        req_scorer->state = self->state;
        excl_scorer->state = self->state;
        if (! excl_scorer->next(excl_scorer)) {
            /* emptied at start */
            SCORER_NULLIFY(rxsc->excl_scorer);
            excl_scorer = NULL;
        }
        rxsc->first_time = false;
    }
    if (req_scorer == NULL) {
        return false;
    }
    if (self->state && self->state->is_aborted &&
        self->state->is_aborted(self->state->is_aborted_param))
    {
        return false;
    }
    if (! req_scorer->next(req_scorer)) {
        /* emptied, nothing left */
        SCORER_NULLIFY(rxsc->req_scorer);
        return false;
    }
    if (excl_scorer == NULL) {
        self->doc = req_scorer->doc;
        /* req_scorer->next() already returned true */
        return true;
    }
    return rxsc_to_non_excluded(self);
}

static bool rxsc_skip_to(Scorer *self, int doc_num)
{
    ReqExclScorer *rxsc = RXSc(self);
    Scorer *req_scorer = rxsc->req_scorer;
    Scorer *excl_scorer = rxsc->excl_scorer;

    if (rxsc->first_time) {
        rxsc->first_time = false;
        if (! excl_scorer->skip_to(excl_scorer, doc_num)) {
            /* emptied */
            SCORER_NULLIFY(rxsc->excl_scorer);
            excl_scorer = NULL;
        }
    }
    if (req_scorer == NULL) {
        return false;
    }
    if (excl_scorer == NULL) {
        if (req_scorer->skip_to(req_scorer, doc_num)) {
            self->doc = req_scorer->doc;
            return true;
        }
        return false;
    }
    if (! req_scorer->skip_to(req_scorer, doc_num)) {
        SCORER_NULLIFY(rxsc->req_scorer);
        return false;
    }
    return rxsc_to_non_excluded(self);
}

static float rxsc_score(Scorer *self)
{
    Scorer *req_scorer = RXSc(self)->req_scorer;
    return req_scorer->score(req_scorer);
}

static Explanation *rxsc_explain(Scorer *self, int doc_num)
{
    ReqExclScorer *rxsc = RXSc(self);
    Scorer *req_scorer = rxsc->req_scorer;
    Scorer *excl_scorer = rxsc->excl_scorer;
    Explanation *e;

    if (excl_scorer->skip_to(excl_scorer, doc_num)
        && excl_scorer->doc == doc_num) {
        e = expl_new(0.0, "excluded:");
    }
    else {
        e = expl_new(0.0, "not excluded:");
        expl_add_detail(e, req_scorer->explain(req_scorer, doc_num));
    }
    return e;
}

static void rxsc_destroy(Scorer *self)
{
    ReqExclScorer *rxsc = RXSc(self);
    if (rxsc->req_scorer) {
        rxsc->req_scorer->destroy(rxsc->req_scorer);
    }
    if (rxsc->excl_scorer) {
        rxsc->excl_scorer->destroy(rxsc->excl_scorer);
    }
    scorer_destroy_i(self);
}

static Scorer *req_excl_scorer_new(Scorer *req_scorer, Scorer *excl_scorer)
{
    Scorer *self            = scorer_new(ReqExclScorer, NULL);
    RXSc(self)->req_scorer  = req_scorer;
    RXSc(self)->excl_scorer = excl_scorer;
    RXSc(self)->first_time  = true;

    self->score             = &rxsc_score;
    self->next              = &rxsc_next;
    self->skip_to           = &rxsc_skip_to;
    self->explain           = &rxsc_explain;
    self->destroy           = &rxsc_destroy;

    return self;
}

/***************************************************************************
 * NonMatchScorer
 ***************************************************************************/

static float nmsc_score(Scorer *self)
{
    (void)self;
    return 0.0;
}

static bool nmsc_next(Scorer *self)
{
    (void)self;
    return false;
}

static bool nmsc_skip_to(Scorer *self, int doc_num)
{
    (void)self; (void)doc_num;
    return false;
}

static Explanation *nmsc_explain(Scorer *self, int doc_num)
{
    (void)self; (void)doc_num;
    return expl_new(0.0, "No documents matched");
}

static Scorer *non_matching_scorer_new()
{
    Scorer *self    = scorer_new(Scorer, NULL);
    self->score     = &nmsc_score;
    self->next      = &nmsc_next;
    self->skip_to   = &nmsc_skip_to;
    self->explain   = &nmsc_explain;

    return self;
}

/***************************************************************************
 * BooleanScorer
 ***************************************************************************/

#define BSc(scorer) ((BooleanScorer *)(scorer))
typedef struct BooleanScorer
{
    Scorer          super;
    Scorer        **required_scorers;
    int             rs_cnt;
    int             rs_capa;
    Scorer        **optional_scorers;
    int             os_cnt;
    int             os_capa;
    Scorer        **prohibited_scorers;
    int             ps_cnt;
    int             ps_capa;
    Scorer         *counting_sum_scorer;
    Coordinator    *coordinator;
} BooleanScorer;

static Scorer *counting_sum_scorer_create3(BooleanScorer *bsc,
                                           Scorer *req_scorer,
                                           Scorer *opt_scorer)
{
    if (bsc->ps_cnt == 0) {
        /* no prohibited */
        return req_opt_sum_scorer_new(req_scorer, opt_scorer);
    }
    else if (bsc->ps_cnt == 1) {
        /* 1 prohibited */
        return req_opt_sum_scorer_new(
            req_excl_scorer_new(req_scorer, bsc->prohibited_scorers[0]),
            opt_scorer);
    }
    else {
        /* more prohibited */
        return req_opt_sum_scorer_new(
            req_excl_scorer_new(
                req_scorer,
                disjunction_sum_scorer_new(bsc->prohibited_scorers,
                                              bsc->ps_cnt, 1)),
            opt_scorer);
    }
}

static Scorer *counting_sum_scorer_create2(BooleanScorer *bsc,
                                           Scorer *req_scorer,
                                           Scorer **optional_scorers,
                                           int os_cnt)
{
    if (os_cnt == 0) {
        if (bsc->ps_cnt == 0) {
            return req_scorer;
        }
        else if (bsc->ps_cnt == 1) {
            return req_excl_scorer_new(req_scorer,
                                       bsc->prohibited_scorers[0]);
        }
        else {
            /* no optional, more than 1 prohibited */
            return req_excl_scorer_new(
                req_scorer,
                disjunction_sum_scorer_new(bsc->prohibited_scorers,
                                           bsc->ps_cnt, 1));
        }
    }
    else if (os_cnt == 1) {
        return counting_sum_scorer_create3(
            bsc,
            req_scorer,
            single_match_scorer_new(bsc->coordinator, optional_scorers[0]));
    }
    else {
        /* more optional */
        return counting_sum_scorer_create3(
            bsc,
            req_scorer,
            counting_disjunction_sum_scorer_new(bsc->coordinator,
                                                optional_scorers, os_cnt, 1));
    }
}

static Scorer *counting_sum_scorer_create(BooleanScorer *bsc)
{
    if (bsc->rs_cnt == 0) {
        if (bsc->os_cnt == 0) {
            int i;
            /* only prohibited scorers so return non_matching scorer */
            for (i = 0; i < bsc->ps_cnt; i++) {
                bsc->prohibited_scorers[i]->destroy(
                    bsc->prohibited_scorers[i]);
            }
            return non_matching_scorer_new();
        }
        else if (bsc->os_cnt == 1) {
            /* the only optional scorer is required */
            return counting_sum_scorer_create2(
                bsc,
                single_match_scorer_new(bsc->coordinator,
                                           bsc->optional_scorers[0]),
                NULL, 0); /* no optional scorers left */
        }
        else {
            /* more than 1 optional_scorers, no required scorers */
            return counting_sum_scorer_create2(
                bsc,
                counting_disjunction_sum_scorer_new(bsc->coordinator,
                                                       bsc->optional_scorers,
                                                       bsc->os_cnt, 1), 
                NULL, 0); /* no optional scorers left */
        }
    }
    else if (bsc->rs_cnt == 1) {
        /* 1 required */
        return counting_sum_scorer_create2(
            bsc,
            single_match_scorer_new(bsc->coordinator, bsc->required_scorers[0]),
            bsc->optional_scorers, bsc->os_cnt);
    }
    else {
        /* more required scorers */
        return counting_sum_scorer_create2(
            bsc,
            counting_conjunction_sum_scorer_new(bsc->super.similarity,
                                                bsc->coordinator,
                                                bsc->required_scorers,
                                                bsc->rs_cnt),
            bsc->optional_scorers, bsc->os_cnt);
    }
}

static Scorer *bsc_init_counting_sum_scorer(BooleanScorer *bsc)
{
    coord_init(bsc->coordinator);
    int i;
    for (i = 0; i < bsc->rs_cnt; ++i) {
        bsc->required_scorers[i]->state = bsc->super.state;
    }
    for (i = 0; i < bsc->os_cnt; ++i) {
        bsc->optional_scorers[i]->state = bsc->super.state;
    }
    for (i = 0; i < bsc->ps_cnt; ++i) {
        bsc->prohibited_scorers[i]->state = bsc->super.state;
    }
    Scorer *css = counting_sum_scorer_create(bsc);
    css->state = bsc->super.state;
    bsc->counting_sum_scorer = css;
    return bsc->counting_sum_scorer;
}

static void bsc_add_scorer(Scorer *self, Scorer *scorer, unsigned int occur) 
{
    BooleanScorer *bsc = BSc(self);
    if (occur != BC_MUST_NOT) {
        bsc->coordinator->max_coord++;
    }

    switch (occur) {
        case BC_MUST:
            RECAPA(bsc, rs_cnt, rs_capa, required_scorers, Scorer *);
            bsc->required_scorers[bsc->rs_cnt++] = scorer;
            break;
        case BC_SHOULD:
            RECAPA(bsc, os_cnt, os_capa, optional_scorers, Scorer *);
            bsc->optional_scorers[bsc->os_cnt++] = scorer;
            break;
        case BC_MUST_NOT:
            RECAPA(bsc, ps_cnt, ps_capa, prohibited_scorers, Scorer *);
            bsc->prohibited_scorers[bsc->ps_cnt++] = scorer;
            break;
        default:
            RAISE(ARG_ERROR, "Invalid value for :occur. Try :should, :must or "
                  ":must_not instead");
    }
    if (scorer->state != self->state) {
        scorer->state = self->state;
    }
}

static float bsc_score(Scorer *self)
{
    BooleanScorer *bsc = BSc(self);
    Coordinator *coord = bsc->coordinator;
    float sum;
    coord->num_matches = 0;
    sum = bsc->counting_sum_scorer->score(bsc->counting_sum_scorer);
    return sum * coord->coord_factors[coord->num_matches];
}

static bool bsc_next(Scorer *self)
{
    Scorer *cnt_sum_sc = BSc(self)->counting_sum_scorer;

    if (!cnt_sum_sc) {
        cnt_sum_sc = bsc_init_counting_sum_scorer(BSc(self));
    }
    if (cnt_sum_sc->next(cnt_sum_sc)) {
        self->doc = cnt_sum_sc->doc;
        return true;
    }
    else {
        return false;
    }
}

static bool bsc_skip_to(Scorer *self, int doc_num)
{
    Scorer *cnt_sum_sc = BSc(self)->counting_sum_scorer;

    if (!BSc(self)->counting_sum_scorer) {
        cnt_sum_sc = bsc_init_counting_sum_scorer(BSc(self));
    }
    if (cnt_sum_sc->skip_to(cnt_sum_sc, doc_num)) {
        self->doc = cnt_sum_sc->doc;
        return true;
    }
    else {
        return false;
    }
}

static void bsc_destroy(Scorer *self)
{
    BooleanScorer *bsc = BSc(self);
    Coordinator *coord = bsc->coordinator;

    free(coord->coord_factors);
    free(coord);

    if (bsc->counting_sum_scorer) {
        bsc->counting_sum_scorer->destroy(bsc->counting_sum_scorer);
    }
    else {
        int i;
        for (i = 0; i < bsc->rs_cnt; i++) {
            bsc->required_scorers[i]->destroy(bsc->required_scorers[i]);
        }

        for (i = 0; i < bsc->os_cnt; i++) {
            bsc->optional_scorers[i]->destroy(bsc->optional_scorers[i]);
        }

        for (i = 0; i < bsc->ps_cnt; i++) {
            bsc->prohibited_scorers[i]->destroy(bsc->prohibited_scorers[i]);
        }
    }
    free(bsc->required_scorers);
    free(bsc->optional_scorers);
    free(bsc->prohibited_scorers);
    scorer_destroy_i(self);
}

static Explanation *bsc_explain(Scorer *self, int doc_num)
{
    (void)self; (void)doc_num;
    return expl_new(0.0, "This explanation is not supported");
}

static Scorer *bsc_new(Similarity *similarity)
{
    Scorer *self = scorer_new(BooleanScorer, similarity);
    BSc(self)->coordinator          = coord_new(similarity);
    BSc(self)->counting_sum_scorer  = NULL;

    self->score     = &bsc_score;
    self->next      = &bsc_next;
    self->skip_to   = &bsc_skip_to;
    self->explain   = &bsc_explain;
    self->destroy   = &bsc_destroy;
    return self;
}

/***************************************************************************
 *
 * BooleanWeight
 *
 ***************************************************************************/

typedef struct BooleanWeight
{
    Weight w;
    Weight **weights;
    int w_cnt;
} BooleanWeight;


static float bw_sum_of_squared_weights(Weight *self)
{
    BooleanQuery *bq = BQ(self->query);
    float sum = 0.0;
    int i;

    for (i = 0; i < BW(self)->w_cnt; i++) {
        if (! bq->clauses[i]->is_prohibited) {
            Weight *weight = BW(self)->weights[i];
            /* sum sub-weights */
            sum += weight->sum_of_squared_weights(weight);
        }
    }

    /* boost each sub-weight */
    sum *= self->value * self->value;
    return sum;
}

static void bw_normalize(Weight *self, float normalization_factor)
{
    BooleanQuery *bq = BQ(self->query);
    int i;

    normalization_factor *= self->value; /* multiply by query boost */

    for (i = 0; i < BW(self)->w_cnt; i++) {
        if (! bq->clauses[i]->is_prohibited) {
            Weight *weight = BW(self)->weights[i];
            /* sum sub-weights */
            weight->normalize(weight, normalization_factor);
        }
    }
}

static Scorer *bw_scorer(Weight *self, IndexReader *ir)
{
    Scorer *bsc = bsc_new(self->similarity);
    BooleanQuery *bq = BQ(self->query);
    int i;

    for (i = 0; i < BW(self)->w_cnt; i++) {
        BooleanClause *clause = bq->clauses[i];
        Weight *weight = BW(self)->weights[i];
        Scorer *sub_scorer = weight->scorer(weight, ir);
        if (sub_scorer) {
            bsc_add_scorer(bsc, sub_scorer, clause->occur);
        }
        else if (clause->is_required) {
            bsc->destroy(bsc);
            return NULL;
        }
    }

    return bsc;
}

static char *bw_to_s(Weight *self)
{
    return strfmt("BooleanWeight(%f)", self->value);
}

static void bw_destroy(Weight *self)
{
    int i;

    for (i = 0; i < BW(self)->w_cnt; i++) {
        BW(self)->weights[i]->destroy(BW(self)->weights[i]);
    }

    free(BW(self)->weights);
    w_destroy(self);
}

static Explanation *bw_explain(Weight *self, IndexReader *ir, int doc_num)
{
    BooleanQuery *bq = BQ(self->query);
    Explanation *sum_expl = expl_new(0.0, "sum of:");
    Explanation *explanation;
    int coord = 0;
    int max_coord = 0;
    float coord_factor = 0.0;
    float sum = 0.0;
    int i;

    for (i = 0; i < BW(self)->w_cnt; i++) {
        Weight *weight = BW(self)->weights[i];
        BooleanClause *clause = bq->clauses[i];
        explanation = weight->explain(weight, ir, doc_num);
        if (!clause->is_prohibited) {
            max_coord++;
        }
        if (explanation->value > 0.0) {
            if (!clause->is_prohibited) {
                expl_add_detail(sum_expl, explanation);
                sum += explanation->value;
                coord++;
            }
            else {
                expl_destroy(explanation);
                expl_destroy(sum_expl);
                return expl_new(0.0, "match prohibited");
            }
        }
        else if (clause->is_required) {
            expl_destroy(explanation);
            expl_destroy(sum_expl);
            return expl_new(0.0, "match required");
        }
        else {
            expl_destroy(explanation);
        }
    }
    sum_expl->value = sum;

    if (coord == 1) {                /* only one clause matched */
        explanation = sum_expl;      /* eliminate wrapper */
        ary_size(sum_expl->details) = 0;
        sum_expl = sum_expl->details[0];
        expl_destroy(explanation);
    }

    coord_factor = sim_coord(self->similarity, coord, max_coord);

    if (coord_factor == 1.0) {       /* coord is no-op */
        return sum_expl;             /* eliminate wrapper */
    }
    else {
        explanation = expl_new(sum * coord_factor, "product of:");
        expl_add_detail(explanation, sum_expl);
        expl_add_detail(explanation, expl_new(coord_factor, "coord(%d/%d)",
                                              coord, max_coord));
        return explanation;
    }
}

static Weight *bw_new(Query *query, Searcher *searcher)
{
    int i;
    Weight *self = w_new(BooleanWeight, query);

    BW(self)->w_cnt = BQ(query)->clause_cnt;
    BW(self)->weights = ALLOC_N(Weight *, BW(self)->w_cnt);
    for (i = 0; i < BW(self)->w_cnt; i++) {
        BW(self)->weights[i] = q_weight(BQ(query)->clauses[i]->query, searcher);
    }

    self->normalize                 = &bw_normalize;
    self->scorer                    = &bw_scorer;
    self->explain                   = &bw_explain;
    self->to_s                      = &bw_to_s;
    self->destroy                   = &bw_destroy;
    self->sum_of_squared_weights    = &bw_sum_of_squared_weights;

    self->similarity                = query->get_similarity(query, searcher);
    self->value                     = query->boost;

    return self;
}

/***************************************************************************
 *
 * BooleanClause
 *
 ***************************************************************************/

void bc_set_occur(BooleanClause *self, BCType occur)
{
    self->occur = occur;
    switch (occur) {
        case BC_SHOULD:
            self->is_prohibited = false;
            self->is_required = false;
            break;
        case BC_MUST:
            self->is_prohibited = false;
            self->is_required = true;
            break;
        case BC_MUST_NOT:
            self->is_prohibited = true;
            self->is_required = false;
            break;
        default:
            RAISE(ARG_ERROR, "Invalid value for :occur. Try :occur => :should, "
                  ":must or :must_not instead");
    }
}

void bc_deref(BooleanClause *self)
{
    if (--self->ref_cnt <= 0) {
        q_deref(self->query);
        free(self);
    }
}

static unsigned long bc_hash(BooleanClause *self)
{
    return ((q_hash(self->query) << 2) | self->occur);
}

static int  bc_eq(BooleanClause *self, BooleanClause *o)
{
    return ((self->occur == o->occur) && q_eq(self->query, o->query)); 
}

BooleanClause *bc_new(Query *query, BCType occur)
{
    BooleanClause *self = ALLOC(BooleanClause);
    self->ref_cnt = 1;
    self->query = query;
    bc_set_occur(self, occur);
    return self;
}

/***************************************************************************
 *
 * BooleanQuery
 *
 ***************************************************************************/

static MatchVector *bq_get_matchv_i(Query *self, MatchVector *mv,
                                    TermVector *tv)
{
    int i;
    for (i = BQ(self)->clause_cnt - 1; i >= 0; i--) {
        if (BQ(self)->clauses[i]->occur != BC_MUST_NOT) {
            Query *q = BQ(self)->clauses[i]->query;
            q->get_matchv_i(q, mv, tv);
        }
    }
    return mv;
}

static Query *bq_rewrite(Query *self, IndexReader *ir)
{
    int i;
    const int clause_cnt = BQ(self)->clause_cnt;
    bool rewritten = false;
    bool has_non_prohibited_clause = false;

    if (clause_cnt == 1) { 
        /* optimize 1-clause queries */
        BooleanClause *clause = BQ(self)->clauses[0];
        if (! clause->is_prohibited) {
            /* just return clause. Re-write first. */
            Query *q = clause->query->rewrite(clause->query, ir);

            if (self->boost != 1.0) {
                /* original_boost is initialized to 0.0. If it has been set to
                 * something else it means this query has already been boosted
                 * before so boost from the original value */
                if ((q == clause->query) && BQ(self)->original_boost) {
                    /* rewrite was no-op */
                    q->boost = BQ(self)->original_boost * self->boost;
                }
                else {
                    /* save original boost in case query is rewritten again */
                    BQ(self)->original_boost = q->boost;
                    q->boost *= self->boost;
                }
            }

            return q;
        }
    }

    self->ref_cnt++;
    /* replace each clause's query with its rewritten query */
    for (i = 0; i < clause_cnt; i++) {
        BooleanClause *clause = BQ(self)->clauses[i];
        Query *rq = clause->query->rewrite(clause->query, ir);
        /* check for at least one non-prohibited clause */
        if (clause->is_prohibited == false) has_non_prohibited_clause = true;
        if (rq != clause->query) {
            if (!rewritten) {
                int j;
                Query *new_self = q_new(BooleanQuery);
                memcpy(new_self, self, sizeof(BooleanQuery));
                BQ(new_self)->clauses = ALLOC_N(BooleanClause *,
                                                BQ(self)->clause_capa);
                memcpy(BQ(new_self)->clauses, BQ(self)->clauses,
                       BQ(self)->clause_capa * sizeof(BooleanClause *));
                for (j = 0; j < clause_cnt; j++) {
                    REF(BQ(self)->clauses[j]);
                }
                self->ref_cnt--;
                self = new_self;
                self->ref_cnt = 1;
                rewritten = true;
            }
            DEREF(clause);
            BQ(self)->clauses[i] = bc_new(rq, clause->occur);
        } else {
            DEREF(rq);
        }
    }
    if (clause_cnt > 0 && !has_non_prohibited_clause) {
        bq_add_query_nr(self, maq_new(), BC_MUST);
    }

    return self;
}

static void bq_extract_terms(Query *self, HashSet *terms)
{
    int i;
    for (i = 0; i < BQ(self)->clause_cnt; i++) {
        BooleanClause *clause = BQ(self)->clauses[i];
        clause->query->extract_terms(clause->query, terms);
    }
}

static char *bq_to_s(Query *self, Symbol field)
{
    int i;
    BooleanClause *clause;
    Query *sub_query;
    char *buffer;
    char *clause_str;
    int bp = 0;
    int size = QUERY_STRING_START_SIZE;
    int needed;
    int clause_len;

    buffer = ALLOC_N(char, size);
    if (self->boost != 1.0) {
        buffer[0] = '(';
        bp++;
    }

    for (i = 0; i < BQ(self)->clause_cnt; i++) {
        clause = BQ(self)->clauses[i];
        clause_str = clause->query->to_s(clause->query, field);
        clause_len = (int)strlen(clause_str);
        needed = clause_len + 5;
        while ((size - bp) < needed) {
            size *= 2;
            REALLOC_N(buffer, char, size);
        }

        if (i > 0) {
            buffer[bp++] = ' ';
        }
        if (clause->is_prohibited) {
            buffer[bp++] = '-';
        }
        else if (clause->is_required) {
            buffer[bp++] = '+';
        }

        sub_query = clause->query;
        if (sub_query->type == BOOLEAN_QUERY) {
            /* wrap sub-bools in parens */
            buffer[bp++] = '(';
            memcpy(buffer + bp, clause_str, sizeof(char) * clause_len);
            bp += clause_len;
            buffer[bp++] = ')';
        }
        else {
            memcpy(buffer + bp, clause_str, sizeof(char) * clause_len);
            bp += clause_len;
        }
        free(clause_str);
    }

    if (self->boost != 1.0) {
        char *boost_str = strfmt(")^%f", self->boost);
        int boost_len = (int)strlen(boost_str);
        REALLOC_N(buffer, char, bp + boost_len + 1);
        memcpy(buffer + bp, boost_str, sizeof(char) * boost_len);
        bp += boost_len;
        free(boost_str);
    }
    buffer[bp] = 0;
    return buffer;
}

static void bq_destroy(Query *self)
{
    int i;
    for (i = 0; i < BQ(self)->clause_cnt; i++) {
        bc_deref(BQ(self)->clauses[i]);
    }
    free(BQ(self)->clauses);
    if (BQ(self)->similarity) {
        BQ(self)->similarity->destroy(BQ(self)->similarity);
    }
    q_destroy_i(self);
}

static float bq_coord_disabled(Similarity *sim, int overlap, int max_overlap)
{
    (void)sim; (void)overlap; (void)max_overlap;
    return 1.0;
}

static Similarity *bq_get_similarity(Query *self, Searcher *searcher)
{
    if (!BQ(self)->similarity) {
        Similarity *sim = q_get_similarity_i(self, searcher); 
        BQ(self)->similarity = ALLOC(Similarity);
        memcpy(BQ(self)->similarity, sim, sizeof(Similarity));
        BQ(self)->similarity->coord = &bq_coord_disabled;
        BQ(self)->similarity->destroy = (void (*)(Similarity *))&free;
    }

    return BQ(self)->similarity;
}

static unsigned long bq_hash(Query *self)
{
    int i;
    unsigned long hash = 0;
    for (i = 0; i < BQ(self)->clause_cnt; i++) {
        hash ^= bc_hash(BQ(self)->clauses[i]);
    }
    return (hash << 1) | BQ(self)->coord_disabled;
}

static int  bq_eq(Query *self, Query *o)
{
    int i;
    BooleanQuery *bq1 = BQ(self);
    BooleanQuery *bq2 = BQ(o);
    if ((bq1->coord_disabled != bq2->coord_disabled)
        || (bq1->max_clause_cnt != bq1->max_clause_cnt)
        || (bq1->clause_cnt != bq2->clause_cnt)) {
        return false;
    }

    for (i = 0; i < bq1->clause_cnt; i++) {
        if (!bc_eq(bq1->clauses[i], bq2->clauses[i])) {
            return false;
        }
    }
    return true;
}

Query *bq_new(bool coord_disabled)
{
    Query *self = q_new(BooleanQuery);
    BQ(self)->coord_disabled = coord_disabled;
    if (coord_disabled) {
        self->get_similarity = &bq_get_similarity;
    }
    BQ(self)->max_clause_cnt = DEFAULT_MAX_CLAUSE_COUNT;
    BQ(self)->clause_cnt = 0;
    BQ(self)->clause_capa = BOOLEAN_CLAUSES_START_CAPA;
    BQ(self)->clauses = ALLOC_N(BooleanClause *, BOOLEAN_CLAUSES_START_CAPA);
    BQ(self)->similarity = NULL;
    BQ(self)->original_boost = 0.0;

    self->type = BOOLEAN_QUERY;
    self->rewrite = &bq_rewrite;
    self->extract_terms = &bq_extract_terms;
    self->to_s = &bq_to_s;
    self->hash = &bq_hash;
    self->eq = &bq_eq;
    self->destroy_i = &bq_destroy;
    self->create_weight_i = &bw_new;
    self->get_matchv_i = &bq_get_matchv_i;

    return self;
}

Query *bq_new_max(bool coord_disabled, int max)
{
    Query *q = bq_new(coord_disabled);
    BQ(q)->max_clause_cnt = max;
    return q;
}

BooleanClause *bq_add_clause_nr(Query *self, BooleanClause *bc)
{
    if (BQ(self)->clause_cnt >= BQ(self)->max_clause_cnt) {
        RAISE(STATE_ERROR, "Two many clauses. The max clause limit is set to "
              "<%d> but your query has <%d> clauses. You can try increasing "
              ":max_clause_count for the BooleanQuery or using a different "
              "type of query.", BQ(self)->clause_cnt, BQ(self)->max_clause_cnt);
    }
    if (BQ(self)->clause_cnt >= BQ(self)->clause_capa) {
        BQ(self)->clause_capa *= 2;
        REALLOC_N(BQ(self)->clauses, BooleanClause *, BQ(self)->clause_capa);
    }
    BQ(self)->clauses[BQ(self)->clause_cnt] = bc;
    BQ(self)->clause_cnt++;
    return bc;
}

BooleanClause *bq_add_clause(Query *self, BooleanClause *bc)
{
    REF(bc);
    return bq_add_clause_nr(self, bc);
}

BooleanClause *bq_add_query_nr(Query *self, Query *sub_query, BCType occur)
{
    BooleanClause *bc;
    if (BQ(self)->clause_cnt >= BQ(self)->max_clause_cnt) {
        RAISE(STATE_ERROR, "Two many clauses. The max clause limit is set to "
              "<%d> but your query has <%d> clauses. You can try increasing "
              ":max_clause_count for the BooleanQuery or using a different "
              "type of query.", BQ(self)->clause_cnt, BQ(self)->max_clause_cnt);
    }
    bc = bc_new(sub_query, occur);
    bq_add_clause(self, bc);
    bc_deref(bc); /* bc was referenced unnecessarily */
    return bc;
}

BooleanClause *bq_add_query(Query *self, Query *sub_query, BCType occur)
{
    REF(sub_query);
    return bq_add_query_nr(self, sub_query, occur);
}

