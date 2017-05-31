#include "sort-drive.h"

void swap(int intArray[], int num1, int num2) {
   int temp = intArray[num1];
   intArray[num1] = intArray[num2];
   intArray[num2] = temp;
}

int partition(int intArray[], int left, int right, int pivot) {
   int leftPointer = left -1;
   int rightPointer = right;

   while(!0) {
      while(intArray[++leftPointer] < pivot) {
         //do nothing
      }
		
      while(rightPointer > 0 && intArray[--rightPointer] > pivot) {
         //do nothing
      }

      if(leftPointer >= rightPointer) {
         break;
      } else {
	swap(intArray, leftPointer, rightPointer);
      }
   }
	
   swap(intArray, leftPointer, right);
   return leftPointer;
}

int* quickSort(int intArray[], int left, int right) {
   if(right-left <= 0) {
      return intArray;   
   } else {
      int pivot = intArray[right];
      int partitionPoint = partition(intArray, left, right, pivot);
      quickSort(intArray, left,partitionPoint-1);
      quickSort(intArray, partitionPoint+1,right);
   }
   return intArray;
}

int* sort(int array[], int n) {
  return quickSort(array,0,n-1);
}
