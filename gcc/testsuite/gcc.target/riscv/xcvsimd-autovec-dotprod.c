/* { dg-do compile } */
/* { dg-options "-march=rv32imc_xcvsimd -mabi=ilp32 -O3" } */

int sdot_b(signed char *a, signed char *b, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++)
        sum += a[i] * b[i];
    return sum;
}

unsigned int udot_b(unsigned char *a, unsigned char *b, int n) {
unsigned int sum = 0;
    for (int i = 0; i < n; i++)
        sum += a[i] * b[i];
    return sum;
}

int sdot_h(short *a, short *b, int n) {
    int sum = 0;
    for (int i = 0; i < n; i++)
        sum += a[i] * b[i];
    return sum;
}

unsigned int udot_h(unsigned short *a, unsigned short *b, int n) {
    unsigned int sum = 0;
    for (int i = 0; i < n; i++)
        sum += a[i] * b[i];
    return sum;
}

/* { dg-final { scan-assembler "cv\\.dotsp\\.b" } } */
/* { dg-final { scan-assembler "cv\\.dotup\\.b" } } */
/* { dg-final { scan-assembler "cv\\.dotsp\\.h" } } */
/* { dg-final { scan-assembler "cv\\.dotup\\.h" } } */