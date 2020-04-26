#include <stdio.h>
#include <stdlib.h>

int main() {
	int N = 10;
	int *array = calloc(N, sizeof(int));

	int row;
    printf("Enter row number: ");
    scanf("%d", &row);

    if(row < 6 && row > 9)
        row = 8;

    array[row] = 1;
    if (array[8] > 0) {
        printf("Found number greater than 0" );
    }

	return 0;
}