/* { dg-do compile } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */

void
avg8 (short *c, short *a, short *b) {
    int i;
    for (i = 0; i < 8; i++) {
        short sum = a[i] + b[i];
        c[i] = sum >> 1;
    }
}

/* { dg-final { scan-assembler-times "cv\\.add\\.div2" 4 } } */
/* { dg-final { scan-assembler-not "cv\\.sra\\.sci\\.h" } } */