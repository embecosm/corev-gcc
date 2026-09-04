/* { dg-do compile } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */

void
div4_8 (short *c, short *a, short *b) {
    int i;
    for (i = 0; i < 8; i++) {
        short sum = a[i] + b[i];
        c[i] = sum >> 2;
    }
}

/* { dg-final { scan-assembler-times "cv\\.add\\.div4" 4 } } */
/* { dg-final { scan-assembler-not "cv\\.sra\\.sci\\.h" } } */