// Source: data/benchmarks/tpdb/C/SV-COMP_Termination_Category/CookSeeZuleger-TACAS2013-Fig1_true-termination.c
#include <stdlib.h>
#define assume(e) if(!(e)) exit(-1);
extern int unknown_int(void);

int main() {
	int x = unknown_int();
	int y = unknown_int();
    while (x>0 && y>0) {
        if (unknown_int()) {
            x = x - 1;
        } else {
            x = unknown_int();
            y = y - 1;
        }
    }
}