#include <stdio.h>
#include <stdlib.h>

int main() {
	int N = 10;
	int **matrix = malloc(N * sizeof(int*));
	for (int i = 0; i < N; i++) matrix[i] = calloc(N, sizeof(int));

	matrix[2][3] = 120;
    matrix[2][7] = 120;

	int row = 2;
    int column = 0;
    printf("Enter row number: ");
    scanf("%d", &column);

    if (matrix[row][column % 10] > 0) {
        printf("Found number greater than 0" );
    }

	return 0;
}