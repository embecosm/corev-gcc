/* { dg-do compile } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */

void
cadd90_div2 (short *c, short *a, short *b, int n) {
for (int i = 0; i < 2*n; i += 2)
  {
    c[i]   = (short) (a[i]   - b[i+1]) >> 1;
    c[i+1] = (short) (a[i+1] + b[i])   >> 1;
  }
}

void
cadd270_div4 (short *c, short *a, short *b, int n) {
for (int i = 0; i < 2*n; i += 2)
  {
    c[i]   = (short) (a[i]   + b[i+1]) >> 2;
    c[i+1] = (short) (a[i+1] - b[i])   >> 2;
  }
}

/* { dg-final { scan-assembler "cv\\.subrotmj\\.div2" } } */
/* { dg-final { scan-assembler "cv\\.subrotmj\\.div4" } } */
/* { dg-final { scan-assembler-not "cv\\.sra" } } */
