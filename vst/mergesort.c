#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void c_mergesort(unsigned *arr, int len) {
  //printf("%p %d\n", arr, len);
  if (len == 1) { return; }

  int p = len/2;
  unsigned *arr1 = arr;
  unsigned *arr2 = arr+p;

  c_mergesort(arr1, p);
  c_mergesort(arr2, len-p);

  unsigned *t = malloc(sizeof(unsigned)*len);
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


  memcpy(arr, t, sizeof(unsigned)*len);
  free(t);
}

int main() {
  unsigned a[] = {5,9,1,3,4,6,6,3,2};
  int len = sizeof(a)/sizeof(unsigned);
  c_mergesort(a, sizeof(a)/sizeof(unsigned));
  for (int i = 0; i < len; i++) {
    printf("%d ", a[i]);
  }
  printf("\n");
}

