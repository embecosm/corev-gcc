/* { dg-do compile } */
/* { dg-options "-O3 -fno-vect-cost-model -march=rv32imc_xcvsimd -mabi=ilp32" } */
/* { dg-skip-if "" { *-*-* } { "-O0" "-O1" "-O2" "-Os" "-Og" "-Oz" } } */

int
sext_b (int x) {
    return (signed char) x;
}

int
sext_h (int x) {
    return (short) x;
}

unsigned
zext_h (unsigned x) {
    return (unsigned short) x;
}

int
ext_b (unsigned w) {
    return (signed char) (w >> 16);
}

unsigned
extu_b (unsigned w) {
    return (w >> 8) & 0xff;
}

void
gather_b (signed char *c, signed char *a, signed char *b, int s, int n) {
    int i;
    for (i = 0; i < n; i++)
        c[i] = a[i * s] + b[i];
}

void
gather_h (short *c, short *a, short *b, int s, int n) {
    int i;
    for (i = 0; i < n; i++)
        c[i] = a[i * s] + b[i];
}

/* { dg-final { scan-assembler "cv\\.extract\\.b\[^\\n\]*,0" } } */
/* { dg-final { scan-assembler "cv\\.extract\\.h\[^\\n\]*,0" } } */
/* { dg-final { scan-assembler "cv\\.extractu\\.h\[^\\n\]*,0" } } */
/* { dg-final { scan-assembler "cv\\.extract\\.b\[^\\n\]*,2" } } */
/* { dg-final { scan-assembler "cv\\.extractu\\.b\[^\\n\]*,1" } } */
/* { dg-final { scan-assembler "cv\\.insert\\.b\[^\\n\]*,3" } } */
/* { dg-final { scan-assembler "cv\\.insert\\.h\[^\\n\]*,1" } } */
/* { dg-final { scan-assembler "cv\\.add\\.b" } } */
/* { dg-final { scan-assembler "cv\\.add\\.h" } } */