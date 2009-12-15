#include "similarity.h"
#include "search.h"
#include "array.h"
#include "helper.h"
#include "symbol.h"
#include "boosted_term.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include "internal.h"

/****************************************************************************
 *
 * Term
 *
 ****************************************************************************/

Term *term_new(Symbol field, const char *text)
{
    Term *t = ALLOC(Term);
    t->field = field;
    t->text = estrdup(text);
    return t;
}

void term_destroy(Term *self)
{
    free(self->text);
    free(self);
}

int term_eq(const void *t1, const void *t2)
{
    return (strcmp(((Term *)t1)->text, ((Term *)t2)->text)) == 0 &&
        (((Term *)t1)->field == ((Term *)t2)->field);
}

unsigned long term_hash(const void *t)
{
    return str_hash(((Term *)t)->text) * sym_hash(((Term *)t)->field);
}

/****************************************************************************
 *
 * Similarity
 *
 ****************************************************************************/

static float simdef_length_norm(Similarity *s, Symbol field, int num_terms)
{
    (void)s;
    (void)field;
    return (float)(1.0 / sqrt(num_terms));
}

static float simdef_query_norm(struct Similarity *s, float sum_of_squared_weights)
{
    (void)s;
    return (float)(1.0 / sqrt(sum_of_squared_weights));
}

static float simdef_tf(struct Similarity *s, float freq)
{
    (void)s;
    return (float)sqrt(freq);
}

static float simdef_sloppy_freq(struct Similarity *s, int distance)
{
    (void)s;
    return (float)(1.0 / (double)(distance + 1));
}

static float simdef_idf_term(struct Similarity *s, Symbol field, char *term,
                      Searcher *searcher)
{
    return s->idf(s, searcher->doc_freq(searcher, field, term),
                  searcher->max_doc(searcher));
}

static float simdef_idf_phrase(struct Similarity *s, Symbol field,
                        PhrasePosition *positions,
                        int pp_cnt, Searcher *searcher)
{
    float idf = 0.0;
    int i, j;
    for (i = 0; i < pp_cnt; i++) {
        char **terms = positions[i].terms;
        for (j = ary_size(terms) - 1; j >= 0; j--) {
            idf += sim_idf_term(s, field, terms[j], searcher);
        }
    }
    return idf;
}

static float simdef_idf_multiterm(struct Similarity *s, Symbol field,
                        PriorityQueue *boosted_terms, Searcher *searcher)
{
    int doc_freq = 0, i;
    for (i = boosted_terms->size; i > 0; i--) {
        BoostedTerm *bt = boosted_terms->heap[i];
        doc_freq += searcher->doc_freq(searcher, field, bt->term);
    }
    return sim_idf(s, doc_freq, searcher->max_doc(searcher));
}

static float simdef_idf(struct Similarity *s, int doc_freq, int num_docs)
{
    (void)s;
    return (float)(log((float)num_docs/(float)(doc_freq+1)) + 1.0);
}

static float simdef_coord(struct Similarity *s, int overlap, int max_overlap)
{
    (void)s;
    return (float)((double)overlap / (double)max_overlap);
}

static float simdef_decode_norm(struct Similarity *s, uchar b)
{
    return s->norm_table[b];
}

static uchar simdef_encode_norm(struct Similarity *s, float f)
{
    (void)s;
    return float2byte(f);
}

static void simdef_destroy(Similarity *s)
{
    (void)s;
    /* nothing to do here */
}

static Similarity default_similarity = {
    NULL,
    {0},
    &simdef_length_norm,
    &simdef_query_norm,
    &simdef_tf,
    &simdef_sloppy_freq,
    &simdef_idf_term,
    &simdef_idf_phrase,
    &simdef_idf_multiterm,
    &simdef_idf,
    &simdef_coord,
    &simdef_decode_norm,
    &simdef_encode_norm,
    &simdef_destroy
};

Similarity *sim_create_default()
{
    int i;
    if (!default_similarity.data) {
        for (i = 0; i < 256; i++) {
            default_similarity.norm_table[i] = byte2float((unsigned char)i);
        }

        default_similarity.data = &default_similarity;
    }
    return &default_similarity;
}

/****************************************************************************
 *
 * FlatFieldsSimilarity
 *
 ****************************************************************************/

/// A Similarity object that returns idf=1 for certain specified fields.

// Arguably, a FlatFieldsSimilarity should simply be a layer over an existing
// Similarity object, rather objects of a specific subclass of Similarity.
// This part of the code seems rarely touched, though, so such flexibility
// can wait until it is actually needed.  Until then, there's no point in
// writing and setting a dozen passthrough functions just so we can hold a
// pointer to a Similarity rather than hold a Similarity itself.

typedef struct FlatFieldsSimilarity {
    Similarity super;
    Symbol *fields;
    int num_fields;
} FlatFieldsSimilarity;

#define FFS(s) ((FlatFieldsSimilarity *)(s))

static int is_specified_field(FlatFieldsSimilarity *s, Symbol field)
{
    int i;
    for (i = 0; i < s->num_fields; ++i) {
        if (field == s->fields[i])
            return 1;
    }
    return 0;
}

static float simflatfields_idf_term(struct Similarity *s, Symbol field,
                      char *term, Searcher *searcher)
{
    FlatFieldsSimilarity *fs = FFS(s);
    if (is_specified_field(fs, field))
        return 1;
    else
        return simdef_idf_term(s, field, term, searcher);
}

static float simflatfields_idf_phrase(struct Similarity *s, Symbol field,
                        PhrasePosition *positions,
                        int pp_cnt, Searcher *searcher)
{
    FlatFieldsSimilarity *fs = FFS(s);
    if (is_specified_field(fs, field))
        return 1;
    else
        return simdef_idf_phrase(s, field, positions, pp_cnt, searcher);
}
    
static float simflatfields_idf_multiterm(struct Similarity *s, Symbol field,
                        PriorityQueue *boosted_terms, Searcher *searcher)
{
    FlatFieldsSimilarity *fs = FFS(s);
    if (is_specified_field(fs, field))
        return 1;
    else
        return simdef_idf_multiterm(s, field, boosted_terms, searcher);
}

static void simflatfields_destroy(Similarity *s)
{
    FlatFieldsSimilarity *fs = FFS(s);
    if (fs) {
        free(fs->fields);
        fs->fields = NULL;
    }
    free(fs);
}

Similarity *sim_create_flat_fields(const Symbol *fields, int num_fields)
{
    if (num_fields == 0)
        return sim_create_default();

    assert(fields);
    FlatFieldsSimilarity *s = malloc(sizeof(FlatFieldsSimilarity));
    if (s) {
        s->fields = malloc(sizeof(Symbol) * num_fields);
        if (s->fields) {
            // a contorted way to construct super, because sim_create_default
            // has no in-place-pointer version
            Similarity *temp = sim_create_default();
            memcpy(&s->super, temp, sizeof(Similarity));
            temp->destroy(temp);

            memcpy(s->fields, fields, sizeof(Symbol) * num_fields);
            s->num_fields          = num_fields;

            s->super.idf_term      = &simflatfields_idf_term;
            s->super.idf_phrase    = &simflatfields_idf_phrase;
            s->super.idf_multiterm = &simflatfields_idf_multiterm;
            s->super.destroy       = &simflatfields_destroy;
        } else {
            free(s);
            s = NULL;
        }
    }
    return (Similarity *) s;
}

