#include <stdio.h>
#include <stdlib.h>

int main()
{
    int N = 2;
    int **p = malloc(N * sizeof(int*));
    for (int i = 0; i < N; i++) {
        p[i] = calloc(N, sizeof(int));
    }
    p[0][0] = 1;
    int a, b;
    scanf("%d", &a);
    scanf("%d", &b);
    if (p[a][b] == 1) {
        printf("Pass\n");
    }
    return 0;
}