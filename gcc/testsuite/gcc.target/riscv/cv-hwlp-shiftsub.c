/* { dg-do compile } */
/* { dg-options "-march=rv32imc_xcvhwlp -mabi=ilp32 -O2" } */

int f (int i, int j)
{
 while (--j)
   i = (i << 1) - 13;
  return i;
}
/* { dg-final { scan-assembler {\mcv.setupi\M} } } */
