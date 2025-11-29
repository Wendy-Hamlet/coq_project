#include "util.h"
#include <string.h>
/* Ensure strdup is declared even under strict feature macros */
extern char *strdup(const char *);

char *xstrdup(const char *s) {
	if (!s) return NULL;
	char *r = strdup(s);
	if (!r) die("Out of memory");
	return r;
}
