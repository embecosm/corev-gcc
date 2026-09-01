/* { dg-do compile } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */

void
add4 (signed char *c, signed char *a, signed char *b) {
    int i;
    for (i = 0; i < 4; i++)
    c[i] = a[i] + b[i];
}

/* { dg-final { scan-assembler "cv\\.add\\.b" } } */