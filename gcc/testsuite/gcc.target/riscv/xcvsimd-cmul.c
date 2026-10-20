/* { dg-do compile } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */

typedef _Complex short cshort;

void
cmul (cshort *c, cshort *a, cshort *b, int n) {
  for (int i = 0; i < n; i++)
    c[i] = a[i] * b[i];
}

void
cmul_conj (cshort *c, cshort *a, cshort *b, int n) {
  for (int i = 0; i < n; i++)
    c[i] = a[i] * ~b[i];
}

/* { dg-final { scan-assembler "cv\\.cplxconj" } } */
/* { dg-final { scan-assembler "cv\\.subrotmj\\s+\\w+,zero," } } */
/* { dg-final { scan-assembler "cv\\.dotsp\\.h" } } */
/* { dg-final { scan-assembler "cv\\.pack\\s" } } */
