/* { dg-do compile } */
/* { dg-options "-march=rv32imac_zicsr_xcvhwlp -mabi=ilp32 -Os" } */
/* { dg-skip-if "" { *-*-* }  { "-O0" } { "" } } */

char *a;
int b, c;

int
d (void)
{
  char e = 0;
  for (; e < 6; e++)
    a[b] |= a[e] |= a[b] |= a[c + e >> 4 * b] |= 80 >> e + 1;
}
