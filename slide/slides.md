---
# try also 'default' to start simple
theme: seriph
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

# Verify merge sort in Agda and Coq


---

# Prove Merge Sort

- Defination
  - sorted, ≤, split, ( ★ ☆ ☆ ☆ ☆ )
  - merge ( ★ ★ ★ ★ ☆ )
    - multi definition in Agda and Coq
- Prove the output is sorted ( ★ ★ ★ ★ ☆ )
  - 2 approaches
- Prove the output is permutation of input ( ★ ☆ ☆ ☆ ☆ )
  - 1 approach
- Time complexity O(log n) ( ★ ★ ★ ★ ★ )

---

# Part1 : Prepare to sorted

<img border="rounded" src="part1.drawio.svg" >

---

# Part2 : Sorted

<img border="rounded" src="part2.drawio.svg" >
---

# Part3 : Permutation

<img border="rounded" src="part3.drawio.svg" >
---

# List 
```
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
```

---

# Question

1. 如果第一步展开错了怎么办？

  <br/>

2. 如果没有发现 coqlemma 怎么办？

  <br/>

3. with 的含义

---

# Question

1. 如果第一步展开错了怎么办？

  依然可以证明出来

  <br/>

2. 如果没有发现 coqlemma 怎么办？

  可能不得不引入一些复杂的引理（mutual）

  <br/>

3. with 的含义

  mutual 的语法糖

---

# Termination

众所周知，函数是否可以停机是很难判断的

递归的函数，终止性是很难判断的

agda 要求函数必须可以终止

- 单个函数的 termination
  - 一个参数
  - 二个参数
- mutual 函数的 termination
  - mutual 终止的复杂性
  - 一种可终止的模式

---

# 单个函数的termination

```
{- - -}
foo : ℕ ->  ℕ
foo x = foo x
```

```
{- ↑ -}
foo : ℕ ->  ℕ
foo x = foo (suc x)
```

```
{- ↓ -}
fib : ℕ ->  ℕ
fib zero = one
fib (suc zero) = one
fib (suc (suc x)) = fib x + fib (suc x)
```

## Observation

一个参数的递归函数能终止，参数必须下降 

--- 

# 2 arguments

显然，如果有多个参数，也必须有至少一个参数下降

```
foo: ℕ -> ℕ ->  ℕ
foo x y = foo (suc x) y
```

<img border="rounded" src="single-5.drawio.svg" >

--- 

如果发生两种递归，那只有 C(5, 2) = 10 种情况

<img border="rounded" src="1234.drawio.svg" >

---

<img border="rounded" src="1234-answer.drawio.svg" >

Obversation: 所有的递归，固定一个参数下降，函数可以终止

---

<img border="rounded" src="56.drawio.svg" >

---

<img border="rounded" src="56-answer.drawio.svg" >

<br/>

Obversation: 所有的递归，固定一个参数下降，函数可以终止

---

<img border="rounded" src="78910.drawio.svg" >

---

<img border="rounded" src="78910-answer.drawio.svg" >

---

# Counter example of (10)


<div grid="~ cols-2 gap-4">
<div>

<img border="rounded" src="10.drawio.svg" >

</div>
<div>

```
foo : ℕ -> ℕ -> ℕ
foo zero y = zero
foo (suc x) zero = zero
foo (suc x) (suc y) = foo x (suc (suc y))
                    + foo (suc (suc x)) y
```

</div>
</div>



<div grid="~ cols-2 gap-4">
<div>
</div>

<div>
<img border="rounded" src="55.drawio.svg" >
</div>
</div>

---

<img border="rounded" src="9.drawio.svg" >


```
merge : List ℕ -> List ℕ -> List ℕ
merge [] x₁ = x₁
merge (x ∷ x₂) [] = x ∷ x₂
merge (x ∷ xs) (y ∷ ys) with em x y | merge xs (y ∷ ys) | merge (x ∷ xs) ys
merge (x ∷ xs) (y ∷ ys) | inj₁ x₁ | b | c = x ∷ b
merge (x ∷ xs) (y ∷ ys) | inj₂ y₁ | b | c = y ∷ c
```

---

<img border="rounded" src="789-answer.drawio.svg" >

---

# 单个函数终止性总结

必须满足以下两种条件之一

1. 每次递归，固定一个参数A下降

2. 每次递归，必须是以下两种可能

  - 参数 A 下降
  - 参数 A 不变，参数 B 下降

---

# Termination example : ackermann

<div grid="~ cols-2 gap-4">
<div>
<img border="rounded" src="ackermann.svg" >
</div>

<div>

```
ackermann : ℕ -> ℕ -> ℕ
ackermann zero y = suc y
ackermann (suc x) zero = ackermann x (suc zero)
ackermann (suc x) (suc y) = 
              ackermann x (ackermann (suc x) y)
```

</div>
</div>

<img border="rounded" src="ackermann.drawio.svg" >

---

# Complexitivy of termination in mutual

就算存在不下降的递归，也有可能终止

```
{- agda hello.agda --termination-depth=3 -}
mutual
  foo : List ℕ -> List ℕ
  foo [] = []
  foo (x ∷ []) = []
  foo (x ∷ x₁ ∷ x₂) = bar x₂

  bar :  List ℕ -> List ℕ
  bar x = foo (zero ∷ x)
```

---

# Coq's approach

---

<img border="rounded" src="sorted-merge.drawio.svg" >

<!--

# Different way to prove sorted

<style type="text/css">
.tg  {border-collapse:collapse;border-spacing:0;}
.tg td{border-color:black;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;
  overflow:hidden;padding:10px 5px;word-break:normal;}
.tg th{border-color:black;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;
  font-weight:normal;overflow:hidden;padding:10px 5px;word-break:normal;}
.tg .tg-0lax{text-align:left;vertical-align:top}
</style>
<table class="tg">
<thead>
  <tr>
    <th class="tg-0lax"></th>
    <th class="tg-0lax">Agda<br></th>
    <th class="tg-0lax">Coq</th>
  </tr>
</thead>
<tbody>
  <tr>
    <td class="tg-0lax">structure<br>induction<br></td>
    <td class="tg-0lax">★★☆☆☆</td>
    <td class="tg-0lax">★★★★☆</td>
  </tr>
  <tr>
    <td class="tg-0lax">length<br>induction<br></td>
    <td class="tg-0lax">★★☆☆☆</td>
    <td class="tg-0lax">★★☆☆☆</td>
  </tr>
</tbody>
</table>

-->

---

# 失败的证明路线

- `merge xs ys = merge ys xs`

---

# Summary

<table style="border-collapse:collapse;border-spacing:0" class="tg"><thead><tr><th style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;font-weight:normal;overflow:hidden;padding:10px 5px;text-align:left;vertical-align:top;word-break:normal"></th><th style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;font-weight:normal;overflow:hidden;padding:10px 5px;text-align:left;vertical-align:top;word-break:normal"></th><th style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;font-weight:normal;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal" colspan="2"><span style="font-weight:normal">Agda</span></th><th style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;font-weight:normal;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal" colspan="2"><span style="font-weight:normal">Coq</span></th></tr></thead><tbody><tr><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:left;vertical-align:top;word-break:normal"></td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:left;vertical-align:top;word-break:normal">definition of merge</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">`with`</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">mutual define</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">`Fixpoint`</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">`Function`</td></tr><tr><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:left;vertical-align:top;word-break:normal" rowspan="3">structural<br>recursion</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:left;vertical-align:top;word-break:normal">nested recursion</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">𐄂</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">𐄂</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">✓</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">-</td></tr><tr><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:left;vertical-align:top;word-break:normal">mutual recursion</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">single-mutual</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">mutual-mutual</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">𐄂</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal"><span style="font-weight:400;font-style:normal">𐄂</span></td></tr><tr><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:left;vertical-align:top;word-break:normal">other tactic</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">with</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">𐄂</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">𐄂</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">functional induction</td></tr><tr><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:left;vertical-align:top;word-break:normal">length <br>recursion</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:left;vertical-align:top;word-break:normal">length xs + length ys</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">length-decrease</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">mutual-length-decrease</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">✓</td><td style="border-color:#000000;border-style:solid;border-width:1px;font-family:Arial, sans-serif;font-size:14px;overflow:hidden;padding:10px 5px;text-align:center;vertical-align:top;word-break:normal">-</td></tr></tbody></table>
---

# Future work

1. 验证mergesort时间复杂度 O(log n)
2. Coq 中mutual induction，证明lemma3 lemma4

--- 

# Induction

1. induction 分显式的induction 和隐式的induction
2. coq 是显式的induction。 Agda是隐式的induction

<br/>

## 什么时候要 induction

<br/>

1. 可以随便induction（大不了不用induction引入的条件）

---

# Summary

- Agda 可以写通用程序
- Agda 与普通编程语言一个显著的不同是要求函数的可终止性
- 证明可终止性可以利用定义的induction，或者性质（长度）的下降
- Agda 的termination checker 比 Coq 的智能
- Agda 中 尽量使用 with 。 mutual 会给后续的证明带来不便
- Agda 的自动补全失效时，可以手工加上隐藏参数，帮助Agda推导

---

# Reference

[--termination-depth=N](https://wiki.portal.chalmers.se/agda/ReferenceManual/Pragmas)

[software foudation](https://softwarefoundations.cis.upenn.edu/vfa-current/index.html)

[`Function` in Coq](https://github.com/gtanzer/sort)

[mergesort in Agda](https://stackoverflow.com/questions/17910737/termination-check-on-list-merge/17912550#17912550)

