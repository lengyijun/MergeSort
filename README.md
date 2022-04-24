# MergeSort

Agda : 2.6.2.1

agda-stdlib-1.7.1

4 way to prove correctness
1 way to prove permutation

## Definition of merge and proof of correctness
MergeSort.agda : single definition, single correctness

single-mutual.agda : single definition, mutual correctness

mutual-mutual.agda : mutual definition, mutual correctness

<table><thead><tr><th></th><th colspan="2">Agda</th><th colspan="2">Coq</th></tr></thead><tbody><tr><td></td><td>use `with` to <br>define merge</td><td>define merge <br>mutually</td><td>Fixpoint</td><td>function</td></tr><tr><td>nested<br>recursion</td><td>?</td><td>?</td><td>ok</td><td>todo</td></tr><tr><td>mutual<br>recursion</td><td>single-mutual</td><td>mutual-mutual</td><td>todo</td><td>todo</td></tr><tr><td>length + length</td><td>length-decrease</td><td>mutual-length-decrease</td><td>ok</td><td>todo</td></tr><tr><td>other tactic</td><td>with</td><td>-</td><td>-</td><td>functional induction</td></tr></tbody></table>
