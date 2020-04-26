#include <stdio.h>
#include <stdlib.h>

int main() {
	int N;
    printf("Enter the size of the matrix: ");
    scanf("%d", &N);
	int **matrix = malloc(N * sizeof(int*));
	for (int i = 0; i < N; i++) matrix[i] = calloc(N, sizeof(int));

	matrix[0][0] = 120;

	int row;
    printf("Enter row number: ");
    scanf("%d", &row);

    if(row >= N)
        row = 0;

    int column = 0;

    if (matrix[row][column] > 0) {
        printf("Found number greater than 0" );
    }

	return 0;
}