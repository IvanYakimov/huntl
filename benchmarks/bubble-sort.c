#include "sort-drive.h"

int* sort(int array[], int n) { for(int x=0; x<n; x++) {
    for(int y=0; y<n-1; y++) {
      if(array[y]>array[y+1]) {
	int temp = array[y+1];
	array[y+1] = array[y];
	array[y] = temp;
      }}}
  return array;
}
