/* { dg-do run } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */
/* { dg-prune-output "LOAD segment with RWX permissions" } */

extern void abort (void);

void
add4 (signed char *c, signed char *a, signed char *b) {
    int i;
    for (i = 0; i < 4; i++)
    c[i] = a[i] + b[i];
}

int
main (void) {
    signed char a[4] = {1, 2, 3, 4};
    signed char b[4] = {10, 20, 30, 40};
    signed char c[4];
    signed char expected[4] = {11, 22, 33, 44};
    int i;

    add4 (c, a, b);

    for (i = 0; i < 4; i++)
        if (c[i] != expected[i])
            abort ();

    return 0;
}