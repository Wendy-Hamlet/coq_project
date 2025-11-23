#ifndef UTIL_H
#define UTIL_H

#include <stdio.h>
#include <stdlib.h>

/* Fatal error with message */
static inline void die(const char *msg) {
    fprintf(stderr, "Fatal error: %s\n", msg);
    exit(1);
}

/* Memory allocation wrapper */
static inline void *xmalloc(size_t sz) {
    void *p = malloc(sz);
    if (!p) die("Out of memory");
    return p;
}

/* Duplicate string */
char *xstrdup(const char *s);

#endif
