#include <stdio.h>
int main()
{
    int testInteger;
    printf("Enter an integer: ");
    scanf("%d", &testInteger);
    if (testInteger == 1) {
        printf("Number = %d\n", testInteger);
    }
    return 0;
}