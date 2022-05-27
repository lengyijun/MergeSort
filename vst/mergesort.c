#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void my_mergesort(int *arr, int len) {
  //printf("%p %d\n", arr, len);
  if (len == 1) { return; }

  int p = len/2;
  int *arr1 = arr;
  int *arr2 = arr+p;

  my_mergesort(arr1, p);
  my_mergesort(arr2, len-p);

  int *t = malloc(sizeof(int)*len);
  if(!t){exit(1);}


  int i=0; 
  int j =p;
  int k=0;

  for(; i< p && j < len ; k++){
    if(arr[i]<=arr[j]){
      t[k]=arr[i];
      i++;
    }else{
      t[k]=arr[j];
      j++;
    }
  }

  for(;i<p ; i++, k++){
    t[k]=arr[i];
  }
  for(;j<len ; j++, k++){
    t[k]=arr[j];
  }


  memcpy(arr, t, sizeof(int)*len);
  free(t);
}

int main() {
  int a[] = {5,9,1,3,4,6,6,3,2};
  int len = sizeof(a)/sizeof(int);
  my_mergesort(a, sizeof(a)/sizeof(int));
  for (int i = 0; i < len; i++) {
    printf("%d ", a[i]);
  }
  printf("\n");
}

