#include <stdio.h>
#include <stdlib.h>

int main() {
	int N = 10;
	int *array = calloc(N, sizeof(int));

	int row;
    printf("Enter row number: ");
    scanf("%d", &row);

    for(int i = 0; i < 10; i++)
        array[(row + i) % 10] = 1;

    if (array[6] > 0) {
        printf("Found number greater than 0" );
    }

	return 0;
}