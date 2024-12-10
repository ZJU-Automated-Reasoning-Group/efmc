// Source: data/benchmarks/tpdb/C_Integer/Stroeder_15/ChenFlurMukhopadhyay-SAS2012-Ex4.01_true-termination.c
#include <stdlib.h>
#define assume(e) if(!(e)) exit(-1);
extern int unknown_int(void);

typedef enum {false, true} bool;

int main() {
    int x, y, z, n;
    x = unknown_int();
    y = unknown_int();
    z = unknown_int();
    n = unknown_int();
    while (x + y >= 0 && x <= n) {
        x = 2*x + y;
        y = z;
        z = z;
        z = z + 1;
    }
    return 0;
}