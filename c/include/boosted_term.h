#ifndef FRT_BOOSTED_TERM_H
#define FRT_BOOSTED_TERM_H

/***************************************************************************
 * BoostedTerm
 ***************************************************************************/

typedef struct BoostedTerm
{
    char *term;
    float boost;
} BoostedTerm;

// Functions for BoostedTerm are defined in and used by q_multi_term.c.

#endif
