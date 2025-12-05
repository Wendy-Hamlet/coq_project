/**
 * Main entry point for the typed WhileD compiler.
 * Usage: whiled [source_file]
 * If no source file is provided, reads from stdin.
 */
#include <stdio.h>
#include <stdlib.h>
#include "driver.h"

int main(int argc, char **argv) {
    FILE *input = stdin;

    /* Step 1: Process command line arguments */
    if (argc > 1) {
        input = fopen(argv[1], "r");
        if (!input) {
            perror(argv[1]);
            return 1;
        }
    }

    /* Step 2: Hand control to the driver for compilation */
    int result = driver_compile(input);

    /* Step 3: Clean up resources */
    if (input != stdin) {
        fclose(input);
    }

    return result;
}