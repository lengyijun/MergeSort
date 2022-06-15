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

<arrow v-click="0" x1="350" y1="330" x2="230" y2="270" color="#564" width="3" arrowSize="5" />

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
  right:5px;
  border: double;
}
.post{
  position: absolute;
  bottom: 170px;
  right:5px;
  border: double;
}
</style>

---

<div class="half" >

```c {all|8-9}
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

<div class="sep1">

```
SEP ( data_at sh (tarray tuint (Zlength il)) il arr )
```

</div>

<div class="sep2">

```
SEP ( data_at sh (tarray tuint (Zlength il)) (l1 ++ l2) arr)
// l1 = mergesort (firstn p il)
// l2 = mergesort (skipn p il)
```

</div>

<div class="sep3">

```
// loop invariant
firstn (i + j - (Zlength il /2)) (merge l1 l2) = 
  merge (firstn i l1) (firstn (j - p) l2)

SEP ( data_at sh (tarray tuint (Zlength il)) 
    firstn (i + j - p) (merge l1 l2)
    t )
```

</div>

<div class="sep4">

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
  right:100px;
  border: double;
  width : 450px;
}
.sep2{
  position: absolute;
  bottom: 250px;
  right: 100px;
  border: double;
}
.sep3{
  position: absolute;
  bottom: 80px;
  right: 100px;
  border: double;
  width : 450px;
}
.sep4{
  position: absolute;
  bottom: 15px;
  right: 100px;
  border: double;
  width : 450px;
}
</style>

---


