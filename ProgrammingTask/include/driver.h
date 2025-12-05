#ifndef DRIVER_H
#define DRIVER_H

#include <stdio.h>

/**
 * Compilation driver entry point.
 * @param input Open file pointer (pass stdin for standard input)
 * @return 0 on success, non-zero on failure
 */
int driver_compile(FILE *input);

#endif