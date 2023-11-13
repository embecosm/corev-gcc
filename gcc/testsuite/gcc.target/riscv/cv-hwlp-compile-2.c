/* { dg-do compile } */
/* { dg-options "-march=rv32imac_zicsr_xcvhwlp -mabi=ilp32 -Os -Wno-implicit-function-declaration -Wno-implicit-int -Wno-int-conversion" } */
/* { dg-skip-if "" { *-*-* }  { "-O0" } { "" } } */

int *c;
int d[12];
int e;

_start ()
{
  volatile a = b ();
}

int
f (void)
{
  short g, h;
  for (; e;)
    {
      g = 0;
      for (; g < 8; g++)
	{
	  h = 0;
	  for (; h < 4; h++)
	    d[h] = c[h] = d[0];
	}
    }
}

int
b (void)
{
  return f;
}
