#include <stdlib.h>
#include <stdio.h>

/* macro conversions between a double-word pointerand unsigned int value
 * based on the memory system provided by memlib.c where max heap size 
 * is no larger than 32-bit
 */

 #define PTOI(hp, p) ((unsigned int)(p - hp))
 #define ITOP(hp, val) ((char *)val + hp)


 int main () {
 	char *p1 = malloc(4);
 	char *p2 = malloc(12);

 	printf("p1 value: %p\n", p1);
 	printf("p2 value: %p\n", p2);
 	printf("%d\n", PTOI(p1, p2));

 	printf("%d", (unsigned int)NULL);
 }