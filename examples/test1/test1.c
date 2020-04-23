#include <stdio.h>
int main()
{
    int a;
    int *p;
    scanf("%d", &a);
    p = &a;
    if (*p == 1) {
        printf("Number = %d\n", *p);
    }
    return 0;
}