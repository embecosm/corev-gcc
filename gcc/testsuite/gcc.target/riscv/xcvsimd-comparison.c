/* { dg-do compile } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */

void
cmpeq4 (signed char *c, signed char *a, signed char *b) {
    int i;
    for (i = 0; i < 4; i++)
        c[i] = a[i] == b[i] ? -1 : 0;
}

void
cmple4 (signed char *c, signed char *a, signed char *b) {
    int i;
    for (i = 0; i < 4; i++)
        c[i] = a[i] <= b[i] ? -1 : 0;
}

void
cmpltu4 (unsigned char *c, unsigned char *a, unsigned char *b) {
    int i;
    for (i = 0; i < 4; i++)
        c[i] = a[i] < b[i] ? 1 : 0;
}

void
sel4 (signed char *c, signed char *a, signed char *b) {
    int i;
    for (i = 0; i < 4; i++)
        c[i] = a[i] > b[i] ? a[i] + 1 : b[i] - 1;
}

void
cmpeq_h (short *c, short *a, short *b, int n) {
    int i;
    for (i = 0; i < n; i++)
        c[i] = a[i] == b[i] ? -1 : 0;
}

void
cmple_h (short *c, short *a, short *b, int n) {
    int i;
    for (i = 0; i < n; i++)
        c[i] = a[i] <= b[i] ? -1 : 0;
}

/* { dg-final { scan-assembler "cv\\.cmpeq\\.b" } } */
/* { dg-final { scan-assembler "cv\\.cmple\\.b" } } */
/* { dg-final { scan-assembler "cv\\.cmpltu\\.b" } } */
/* { dg-final { scan-assembler "cv\\.cmpgt\\.b" } } */
/* { dg-final { scan-assembler "cv\\.cmpeq\\.h" } } */
/* { dg-final { scan-assembler "cv\\.cmple\\.h" } } */
/* { dg-skip-if "" { *-*-* } { "-O0" "-O1" "-O2" "-Os" "-Og" "-Oz" } } */