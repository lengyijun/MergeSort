---
# try also 'default' to start simple
theme: default
# random image from a curated Unsplash collection by Anthony
# like them? see https://unsplash.com/collections/94734566/slidev
background: https://source.unsplash.com/collection/94734566/1920x1080
# apply any windi css classes to the current slide
class: 'text-center'
# https://sli.dev/custom/highlighters.html
highlighter: shiki
# show line numbers in code blocks
lineNumbers: false
# some information about the slides, markdown enabled
info: |
  ## Slidev Starter Template
  Presentation slides for developers.

  Learn more at [Sli.dev](https://sli.dev)
# persist drawings in exports and build
drawings:
  persist: false
---

# Use VST to prove mergesort


<!--
The last comment block of each slide will be treated as slide notes. It will be visible and editable in Presenter Mode along with the slide. [Read more in the docs](https://sli.dev/guide/syntax.html#notes)
-->

---

<div grid="~ cols-2 gap-4">
<div>

```c
void my_mergesort(unsigned *arr, int len) {
  if (len == 1) { return; }

  int p = len/2;
  unsigned *arr1 = arr;
  unsigned *arr2 = arr+p;

  my_mergesort(arr1, p);
  my_mergesort(arr2, len-p);

  unsigned *t = malloc(sizeof(unsigned)*len);
  if(!t){exit(1);}

  int i=0; int j=p; int k=0;

  for(; i< p && j < len ; k++){
    if(arr[i]<=arr[j]){
      t[k]=arr[i];
      i++;
    }else{
      t[k]=arr[j];
      j++;
    }
  }
```

</div>
<div>

```c
  for(;i<p ; i++, k++){
    t[k]=arr[i];
  }
  for(;j<len ; j++, k++){
    t[k]=arr[j];
  }

  memcpy(arr, t, sizeof(unsigned)*len);
  free(t);
}
```

</div>

</div>

---

```
Definition my_mergesort_spec : ident * funspec :=
 DECLARE _my_mergesort
 WITH p: val,  sh : share, il: list Z, gv: globals
 PRE [ tptr tuint , tint ]
    PROP ( writable_share sh;
           0 < Zlength il <= Int.max_signed;
           Forall (fun x => 0 <= x <= Int.max_unsigned) il)
    PARAMS (p; Vint (Int.repr (Zlength il)) )
    GLOBALS(gv)
    SEP (data_at sh (tarray tuint (Zlength il)) (map Vint (map Int.repr il)) p;
         mem_mgr gv)

 POST [ tvoid ]
    PROP ( ) RETURN ()
    SEP (data_at sh (tarray tuint (Zlength il)) (map Vint (map Int.repr (mergesort il))) p;
         mem_mgr gv).
```

---

<div class="half">

```c
void my_mergesort(unsigned *arr, int len) {
  ...
}
```

</div>



<div class="pre">

```
PROP ( writable_share sh;
       0 < Zlength il <= Int.max_signed;
       Forall (fun x => 0 <= x <= Int.max_unsigned) il)
PARAMS (arr; Vint (Int.repr (Zlength il)) )
GLOBALS(gv)
SEP (
   data_at sh (tarray tuint (Zlength il)) il arr;
   mem_mgr gv)
```

</div>


<arrow v-click="0" x1="400" y1="100" x2="230" y2="170" color="#564" width="3" arrowSize="5" />

<arrow v-click="0" x1="400" y1="330" x2="230" y2="270" color="#564" width="3" arrowSize="5" />

<div class="post">

```
PROP ( ) RETURN ()
SEP (
  data_at sh (tarray tuint (Zlength il)) (mergesort il) arr;
  mem_mgr gv).
```

</div>


<style>
.half{
  position: absolute;
  top: 180px;
  width: 35%
}
.pre{
  position: absolute;
  top: 20px;
  right:100px;
  border: double;
  width : 470px;
}
.post{
  position: absolute;
  bottom: 170px;
  right:100px;
  border: double;
  width : 470px;
}
</style>

---

<div class="half" >

```c {all|8-9|16-30}
void my_mergesort(unsigned *arr, int len) {
  if (len == 1) { return; }

  int p = len/2;
  unsigned *arr1 = arr;
  unsigned *arr2 = arr+p;

  my_mergesort(arr1, p);
  my_mergesort(arr2, len-p);

  unsigned *t = malloc(sizeof(unsigned)*len);
  if(!t){exit(1);}

  int i=0; int j=p; int k=0;

  for(; i< p && j < len ; k++){
    if(arr[i]<=arr[j]){
      t[k]=arr[i];
      i++;
    }else{
      t[k]=arr[j];
      j++;
    }
  }
 ... 



```

<arrow v-click="1" x1="430" y1="135" x2="230" y2="170" color="#564" width="2" arrowSize="5" />

</div>

<div v-click="1" class="sep1">

```
// il : List Z
SEP (data_at sh (tarray tuint (Zlength il)) il arr )
```

</div>

<arrow v-click="1" x1="430" y1="255" x2="230" y2="220" color="#564" width="2" arrowSize="5" />

<div v-click="1" class="sep2" >

```
SEP (data_at sh (tarray tuint (Zlength il)) (l1 ++ l2) arr)
// l1 = mergesort (firstn p il)
// l2 = mergesort (skipn p il)
```

</div>

<arrow v-click="2" x1="430" y1="400" x2="230" y2="400" color="#564" width="2" arrowSize="5" />

<div v-click="2" class="sep3">

```
// loop invariant
firstn (i + j - p) (merge l1 l2) = 
  merge (firstn i l1) (firstn (j - p) l2)

SEP (data_at sh (tarray tuint (Zlength il)) 
      firstn (i + j - p) (merge l1 l2) t)
```

</div>

<arrow v-click="2" x1="430" y1="490" x2="230" y2="490" color="#564" width="2" arrowSize="5" />

<div v-click="2" class="sep4">

```
// after loop
i = p \/ j = len
```

</div>

<style>
.half{
  width: 40%
}
.sep1{
  position: absolute;
  top: 120px;
  right:90px;
  border: double;
  width : 470px;
}
.sep2{
  position: absolute;
  bottom: 250px;
  right: 90px;
  border: double;
  width : 470px;
}
.sep3{
  position: absolute;
  bottom: 80px;
  right: 90px;
  border: double;
  width : 470px;
}
.sep4{
  position: absolute;
  bottom: 15px;
  right: 90px;
  border: double;
  width : 470px;
}
</style>

---

## (1) i = p

<div class="half" >

```c
  for(;i<p ; i++, k++){
    t[k]=arr[i];
  }

  for(;j<len ; j++, k++){
    t[k]=arr[j];
  }










  memcpy(arr, t, sizeof(unsigned)*len);
  



  free(t);
}
```

</div>

<arrow v-click="1" x1="420" y1="120" x2="230" y2="120" color="#564" width="2" arrowSize="5" />

<div v-click="1" class="sep1" >  
Nothing happens
</div>

<arrow v-click="2" x1="430" y1="220" x2="230" y2="190" color="#564" width="2" arrowSize="5" />

<div v-click="2" class="sep2">

```
// loop invariant
firstn j (merge l1 l2) = 
  merge l1 (firstn (j - p) l2)

SEP (data_at sh (tarray tuint (Zlength il)) 
      (firstn j (merge l1 l2)) t)
```

</div>

<arrow v-click="3" x1="430" y1="340" x2="230" y2="340" color="#564" width="2" arrowSize="5" />

<div v-click="3" class="sep3">

```
// after loop
j = len; k = len
SEP (data_at sh (tarray tuint (Zlength il)) (merge l1 l2) t)
```

</div>

<arrow v-click="4" x1="430" y1="450" x2="230" y2="450" color="#564" width="2" arrowSize="5" />

<div v-click="4" class="sep4">

```
// after memcpy
SEP (data_at sh (tarray tuint (Zlength il)) (merge l1 l2) arr)
```

</div>

<style>
.half{
  width: 40%
}
.sep1{
  position: absolute;
  top: 110px;
  right:90px;
  border: double;
  width : 470px;
}
.sep2{
  position: absolute;
  bottom: 260px;
  right: 90px;
  border: double;
  width : 470px;
}
.sep3{
  position: absolute;
  bottom: 165px;
  right: 90px;
  border: double;
  width : 470px;
}
.sep4{
  position: absolute;
  bottom: 65px;
  right: 90px;
  border: double;
  width : 470px;
}
</style>

---

## (2) j = len

<div class="half" >

```c
  for(;i<p ; i++, k++){
    t[k]=arr[i];
  }










  for(;j<len ; j++, k++){
    t[k]=arr[j];
  }

  memcpy(arr, t, sizeof(unsigned)*len);
  



  free(t);
}
```
</div>

<arrow v-click="1" x1="420" y1="120" x2="230" y2="120" color="#564" width="2" arrowSize="5" />

<div v-click="1" class="sep1">

```
// loop invariant
firstn (i + len - p) (merge l1 l2) = 
  merge (firstn i l1) l2

SEP (data_at sh (tarray tuint (Zlength il)) 
      firstn (i + len - p) (merge l1 l2) t )
```

</div>

<arrow v-click="2" x1="430" y1="220" x2="230" y2="220" color="#564" width="2" arrowSize="5" />

<div v-click="2" class="sep2">

```
// after loop
i = p; k = len
SEP (data_at sh (tarray tuint (Zlength il)) (merge l1 l2) t)
```

</div>

<arrow v-click="3" x1="420" y1="355" x2="230" y2="355" color="#564" width="2" arrowSize="5" />

<div v-click="3" class="sep3" >  
Nothing happens
</div>


<arrow v-click="4" x1="430" y1="450" x2="230" y2="450" color="#564" width="2" arrowSize="5" />

<div v-click="4" class="sep4">

```
// after memcpy
SEP (data_at sh (tarray tuint (Zlength il)) (merge l1 l2) arr)
```

</div>

<style>
.half{
  width: 40%
}
.sep1{
  position: absolute;
  top: 60px;
  right:90px;
  border: double;
  width : 470px;
}
.sep2{
  position: absolute;
  bottom: 270px;
  right: 90px;
  border: double;
  width : 470px;
}
.sep3{
  position: absolute;
  bottom: 185px;
  right: 90px;
  border: double;
  width : 470px;
}
.sep4{
  position: absolute;
  bottom: 60px;
  right: 90px;
  border: double;
  width : 470px;
}
</style>

---

<div class="half">

```c
void c-mergesort(unsigned *arr, int len) {
  if (len == 1) { return; }

  int p = len/2;
  unsigned *arr1 = arr;
  unsigned *arr2 = arr+p;

  my_mergesort(arr1, p);
  my_mergesort(arr2, len-p);

  unsigned *t = malloc(sizeof(unsigned)*len);
  if(!t){exit(1);}

  int i=0; int j=p; int k=0;

  for(; i< p && j < len ; k++){
    if(arr[i]<=arr[j]){
      t[k]=arr[i];
      i++;
    }else{
      t[k]=arr[j];
      j++;
    }
  }
```

</div>

<div class="coq">

```
Program Fixpoint coq-mergesort (x : list Z) {measure (length x)}: list Z :=
  match x with
  | nil => nil
  | x :: nil => x :: nil
  | x :: y :: nil => if x <=? y
    then (x :: y :: nil)
    else (y :: x :: nil)
  | x :: y :: z :: rest =>
    let a := (x :: y :: z :: rest) in
    let p := (Nat.div2 (length a)) in
    merge (mergesort (firstn p a)) (mergesort (skipn p a))
  end.
```

</div>

<div class="explan">
如果 arr 地址的数组是 il，<br>
那么 c-mergesort 返回时，arr里的数组是 coq-mergesort il <br>
所以 c-mergesort 的返回结果满足 Permutation 和 Sorted
</div>

<style>
.half{
  width: 35%;
  position: absolute;
  left: 10px;
}
.coq{
  width: 560px;
  position: absolute;
  top: 40px;
  right: 10px
}
.explan{
  width: 540px;
  position: absolute;
  bottom: 40px;
  right: 10px
}
</style>

---

## loop invariant

```
merge (firstn i l1) (firstn j l2) = firstn (i + j) (merge l1 l2)
l1[i] <= l2[j]
-------------------------------------------------------------------------
merge (firstn (i+1) l1) (firstn j l2) = firstn (i + 1 + j) (merge l1 l2)
```

---

## loop invariant

```
merge (firstn i l1) (firstn j l2) = firstn (i + j) (merge l1 l2)
l1[i] <= l2[j]
------------------------------------------------------------------------------------------------------------
merge (firstn (i+1) l1) (firstn j l2)       =    firstn (i + 1 + j) (merge l1 l2)
                 ||                                                      ||
merge (firstn i l1) (firstn j l2) + l1[i]                            merge (firstn i l1) (firstn j l2) ++
                                                                     merge (skipn i l1) (skipn j l2)
           Lemma2 + Lemma1                                                       Lemma1
```

<div v-click="1">

```
// Lemma1
merge (firstn i l1) (firstn j l2) = firstn (i + j) (merge l1 l2)
----------------------------------------------------------------------------------
merge l1 l2 = merge (firstn i l1) (firstn j l2) ++ merge (skipn i l1) (skipn j l2)
```

</div>
<div v-click="2">

```
// Lemma2
merge (firstn i l1) (firstn j l2) = firstn (i + j) (merge l1 l2)
-------------------------------------------------------------------------------------------
merge (firstn i l1) (firstn j l2) = firstn (i + j) (merge (firstn (i+1) l1) (firstn j l2))
```
</div>

---

# Q&A

1. 相同的逻辑，证明的难度会不同？

比如使用指针比较越界？

---

# Conclusion

1. 所有关于merge的lemma，都用总长度做induction

