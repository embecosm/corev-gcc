/* { dg-do compile } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */

void
cadd90 (short *c, short *a, short *b, int n) {
    for (int i = 0; i < 2*n; i += 2) {
        c[i] = a[i] - b[i+1];
        c[i+1] = a[i+1] + b[i];
    }
}

void
cadd270 (short *c, short *a, short *b, int n) {
    for (int i = 0; i < 2*n; i += 2) {
        c[i] = a[i] + b[i+1];
        c[i+1] = a[i+1] - b[i];
    }
}

/* { dg-final { scan-assembler "cv\\.subrotmj\\s+\\w+,zero," } } */
/* { dg-final { scan-assembler "cv\\.add\\.h" } } */
/* { dg-final { scan-assembler "cv\\.sub\\.h" } } */