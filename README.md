# MergeSort

Agda : 2.6.2.1

agda-stdlib-1.7.1

4 way to prove correctness
1 way to prove permutation

## Definition of merge and proof of correctness
MergeSort.agda : single definition, single correctness

single-mutual.agda : single definition, mutual correctness

mutual-mutual.agda : mutual definition, mutual correctness

<table class="tg">
<thead>
  <tr>
    <th class="tg-0pky"></th>
    <th class="tg-c3ow" colspan="2">Agda</th>
    <th class="tg-0pky" rowspan="2">Coq</th>
  </tr>
  <tr>
    <th class="tg-0pky"></th>
    <th class="tg-0pky">merge <br>single definition</th>
    <th class="tg-0pky">merge <br>mutual defintion</th>
  </tr>
</thead>
<tbody>
  <tr>
    <td class="tg-0pky">nested<br>recursion</td>
    <td class="tg-c3ow">?</td>
    <td class="tg-c3ow">?</td>
    <td class="tg-c3ow">ok</td>
  </tr>
  <tr>
    <td class="tg-0pky">mutual<br>recursion</td>
    <td class="tg-c3ow">single-mutual</td>
    <td class="tg-c3ow">mutual-mutual</td>
    <td class="tg-c3ow">todo</td>
  </tr>
  <tr>
    <td class="tg-0pky">length + length</td>
    <td class="tg-c3ow">length-decrease</td>
    <td class="tg-c3ow">mutual-length-decrease</td>
    <td class="tg-c3ow">ok</td>
  </tr>
</tbody>
</table>
