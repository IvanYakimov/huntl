#include "sort-drive.h"

int * sort(int array[], int n) {
  for(int x=0; x<n; x++) {
    int index_of_min = x;
    for(int y=x; y<n; y++) {
      if(array[index_of_min]>array[y]) {
	index_of_min = y;
      }
    }
    int temp = array[x];
    array[x] = array[index_of_min];
    array[index_of_min] = temp;
  }
  return array;
}
