// Source: data/benchmarks/diffy_cav21_bench/ifeqn5.c
#include <stdlib.h>
#define assume(e) if(!(e)) exit(-1);

/*@
	requires N > 0;
	requires \separated(a+(0..N-1), b+(0..N-1));
*/
int main(int* a, int* b, int N)
{

	int i;

	/* Loop_A */  for(i=0; i<N; i++)
	{
		if(i==0) {
			a[0] = 10;
		} else {
			a[i] = a[i-1] + 10;
		}
	}

	/* Loop_B */  for(i=0; i<N; i++)
	{
		if(i==0) {
			b[0] = 1;
		} else {
			b[i] = b[i-1] + a[i-1];
		}
	}

	/* Loop_C */  for(i=0; i<N; i++)
	{
		{;
//@ assert(b[i] == 5*i*i + 5*i + 1);
}

	}
	return 1;
}