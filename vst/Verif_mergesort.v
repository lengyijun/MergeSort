Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import vst.mergesort.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Export Coq.Lists.List.
Require Export Coq.Arith.Arith.
Require Import Program.Wf.

Program Fixpoint merge (x : list Z) (y : list Z) {measure (length x + length y)} : list Z :=
  match x with
  | x1 :: xs =>
    match y with
      | y1 :: ys => if x1 <=? y1
        then x1::(merge xs y)
        else y1::(merge x ys)
      | _ => x
    end
  | _ => y
  end.
Next Obligation.
  apply Nat.add_le_lt_mono; auto.
Qed.

(*
(* useless *)
Lemma merge_l :  forall (xs : list Z)(y : Z)(ys : list Z),
    (forall i,  Nat.lt i (length xs) -> nth i xs 0 <= y )
 -> merge xs (y :: ys) = xs ++ (y :: ys).
Proof.
induction xs.
simpl.
intros.
unfold merge; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func; auto.

intros.
unfold merge; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.

assert (G := H 0%nat).
simpl in G.
assert ( a <= y).
apply G; lia.

remember (a <=? y).
destruct b.
f_equal.
apply IHxs.
intros.
specialize (H (S i)).
simpl in H.
apply H; auto.
lia.

lia.
Qed.
*)


(*
Lemma merge_r :  forall (xs : list Z)(y : Z)(ys : list Z),
    (forall i,  Nat.lt i (length xs) -> nth i xs 0 <= y )
 -> merge (y :: ys) xs = xs ++ (y :: ys).
Proof.
induction xs.
simpl.
intros.
unfold merge; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func; auto.

intros.
unfold merge; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.

assert (G := H 0%nat).
simpl in G.
assert ( a <= y).
apply G; lia.

remember (y <=? a).
destruct b.
assert ( y = a). { lia. }
subst.
f_equal.
unfold merge in IHxs.
clear Heqb H0 G.

apply IHxs.
intros.
specialize (H (S i)).
simpl in H.
apply H; auto.
lia.
Qed.
*)

(*
(* useless *)
Lemma merge_firstn_l :  forall (j : nat)(xs : list Z)(y : Z)(ys : list Z),
    Nat.le j (length xs)
 -> (forall i,  Nat.lt i j -> nth i xs 0 <= y )
 -> merge xs (y :: ys) = firstn j xs ++ merge (skipn j xs) (y :: ys).
Proof.
induction j.
intuition.

intros.
destruct xs; simpl in H.
inv H.
simpl.
unfold merge at 1; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.

remember (z <=? y).
destruct b.
f_equal.
apply IHj.
lia.
intros.
specialize (H0 (S i)).
simpl in H0.
apply H0; lia.

specialize (H0 0%nat).
simpl in H0.
assert (z <= y).
apply H0.
lia.
lia.
Qed.
*)


(*
Lemma merge_firstn_r :  forall (j : nat)(xs : list Z)(y : Z)(ys : list Z),
    Nat.le j (length xs)
 -> (forall i,  Nat.lt i j -> nth i xs 0 <= y )
 -> merge (y :: ys) xs = firstn j xs ++ merge (y :: ys) (skipn j xs) .
Proof.
induction j.
intuition.

intros.
destruct xs; simpl in H.
inv H.
simpl.
unfold merge at 1; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.

remember (y <=? z).
destruct b.

- specialize (H0 0%nat).
simpl in H0.
assert (z <= y).
apply H0.
lia.
assert (z = y). { lia. }
subst.
f_equal.

- f_equal.
  unfold merge in IHj at 1.
apply IHj.
lia.
intros.
specialize (H0 (S i)).
simpl in H0.
apply H0; lia.
Qed.
*)


  
Lemma merge_nil_l : forall xs , merge [] xs = xs .
Proof.
  intros.
  unfold merge ; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func; auto.
Qed.

Lemma merge_nil_r : forall xs , merge xs [] = xs .
Proof.
  intros.
  destruct xs.
  unfold merge ; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func; auto.
  unfold merge ; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func; auto.
Qed.  

Inductive sorted: list Z -> Set :=
| sorted_nil:
    sorted nil 
| sorted_1: forall x,
    sorted (x::nil)
| sorted_cons: forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x::y::l).

Lemma sorted_inv : forall (xs : list Z)(a : Z),
    sorted (a :: xs) -> sorted xs.
Proof.           
  intros.
  inv H; auto.
  constructor.
Qed.  

Lemma sorted_firstn_helper : forall (n : nat)(xs : list Z)(x : Z),
   sorted (x :: xs)
   ->  sorted (x :: firstn n xs).
Proof.
induction  n.
intros.
rewrite firstn_O.
constructor.

induction xs.
intros.
rewrite firstn_nil.
constructor.
intros.
simpl.
inv H.
constructor; auto.
Qed.

Lemma sorted_firstn : forall (n : nat)(xs : list Z),
   sorted xs
   ->  sorted (firstn n xs).          
Proof.
  induction n.
  intros.
  rewrite firstn_O.
  constructor.

  intros.
  inv H.
  rewrite firstn_nil; constructor.
  simpl;  rewrite firstn_nil; constructor.
  simpl.
  destruct n; simpl.
  constructor.
  constructor; auto.
  apply sorted_firstn_helper; auto.
Qed.


Lemma merge_float_l : forall (xs ys : list Z)(a : Z),
       sorted (a :: xs)
    -> sorted (a :: ys)
    -> merge (a :: xs) ys = a :: merge xs ys.  
Proof.
  intros.
  destruct ys.
  do 2 rewrite merge_nil_r; auto.

  unfold merge ; unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.

  inv H0.
  remember (a <=? z).
  destruct b.
  auto.
  lia.
Qed.

Lemma merge_float_r : forall (xs ys : list Z)(a : Z),
       sorted (a :: xs)
    -> sorted (a :: ys)
    -> merge xs (a :: ys) = a :: merge xs ys. 
Proof.
  intros.
  induction xs.
  do 2 rewrite merge_nil_l; auto.

  unfold merge ; unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.

  inv H.
  remember (a0 <=? a).        
  destruct b.  
  assert (a0 = a). { lia. }
  subst.
  f_equal.
  assert ( merge xs (a :: ys) = a :: merge xs ys ). { apply IHxs. auto. }
  unfold merge in H at 1.
  rewrite H.
  assert ( G := merge_float_l xs ys a H5 H0).
  unfold merge in G at 1.
  rewrite G.
  auto.
  auto.
Qed.


Lemma merge_float : forall (xs : list Z)(ys : list Z)(a : Z),
       sorted (a :: xs)
    -> sorted (a :: ys)
    -> merge xs (a :: ys) = merge (a :: xs) ys.
Proof.
  intros.
  rewrite (merge_float_l xs ys a H H0).
  rewrite (merge_float_r xs ys a H H0).
  auto.
Qed.


Lemma merge_firstn_r :  forall (ys xs: list Z)(j : nat),
    Nat.le j (length ys)
    -> firstn j ys = firstn j (merge xs ys)
    -> sorted xs
    -> sorted ys
    -> merge xs ys = firstn j ys ++ merge xs (skipn j ys) .
Proof.
  induction ys.
  intros.
  rewrite firstn_nil.
  rewrite skipn_nil.
  simpl; auto.

  induction xs.
  intros.
  repeat rewrite merge_nil_l.
  rewrite firstn_skipn; auto.
  
  destruct j; intros.
  simpl; auto.

  unfold merge ; unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func; auto.
  unfold merge in H0; unfold merge_func in H0;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0; auto.

  remember (a0 <=? a). 
  destruct b; inv H0; f_equal.

  assert (G := merge_float xs ys a0 H1 H2).
  unfold merge in G.
  rewrite G.
  apply IHys; auto; try lia.
  simpl in H; lia.
  rewrite H5.
  unfold merge.
  rewrite G; auto.
  eapply sorted_inv; apply H2.

  apply IHys; try lia; auto.
  simpl in H; lia.
  eapply sorted_inv; apply H2.
Qed.
    
Lemma merge_append_l : forall (ys xs: list Z)(j : nat),
    Nat.le j (length xs)
 -> firstn (j + length ys) (merge xs ys) = merge (firstn j xs) ys
 -> sorted xs
 -> sorted ys
 -> merge xs ys = merge (firstn j xs) ys ++ skipn j xs.
Proof.
induction ys.
intros.
do 2 rewrite merge_nil_r.
rewrite firstn_skipn; auto.

induction xs.
intros.
rewrite sublist.skipn_nil.
rewrite firstn_nil.
rewrite app_nil_r; auto.

destruct j; intros; simpl in *.
unfold merge in H0 at 2; unfold merge_func in H0;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
unfold merge ; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
unfold merge in H0; unfold merge_func in H0;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
remember (a0 <=? a).
destruct b.
inv H0. f_equal.
rewrite H5.
assert (G := merge_float xs ys a H1 H2).
unfold merge in G at 1.
rewrite G.
specialize (IHys (a :: xs) 0%nat).
simpl in IHys.
rewrite merge_nil_l in IHys.
apply IHys.
lia.
rewrite <- (merge_float xs ys a H1 H2).
auto.
auto.
eapply sorted_inv; apply H2.

f_equal.
specialize (IHys (a0 :: xs) 0%nat).
simpl in IHys.
unfold merge in IHys at 4; unfold merge_func in IHys;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in IHys; simpl in IHys; fold merge_func in IHys.
unfold merge in IHys at 3.
apply IHys.
lia.
unfold merge at 2; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
inv H0.
rewrite H4.
auto.
auto.
eapply sorted_inv; apply H2.

unfold merge ; unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
unfold merge_func at 3;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
unfold merge in H0 ; unfold merge_func in H0;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
unfold merge_func in H0 at 3;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
remember (a0 <=? a).
destruct b; simpl; f_equal.

- apply IHxs.
lia.
inv H0.
auto.
eapply sorted_inv; apply H1.
auto.

- specialize (IHys (a0 :: xs) (S j)).
simpl in IHys.
apply IHys.
lia.
inv H0.

assert (Nat.add j (S (Datatypes.length ys)) = S(Nat.add j (Datatypes.length ys))).
{ lia. }
rewrite H0 in H4.
simpl in H2.
auto.
auto.
eapply sorted_inv; apply H2.
Qed.


Lemma merge_append_r : forall (ys : list Z)(xs : list Z)(j : nat),
    Nat.le j (length xs)
    -> firstn (j + length ys) (merge ys xs) = merge ys (firstn j xs)
    -> sorted xs
    -> sorted ys
    -> merge ys xs = merge ys (firstn j xs) ++ skipn j xs.
Proof.
induction ys.
intros.
do 2 rewrite merge_nil_l.
rewrite firstn_skipn; auto.

induction xs.
intros.
rewrite sublist.skipn_nil.
rewrite firstn_nil.
rewrite app_nil_r; auto.

destruct j; simpl; intros.
rewrite merge_nil_r in H0.

unfold merge; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
unfold merge in H0; unfold merge_func in H0;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
remember (a <=? a0).
destruct b.
- f_equal.
  specialize (IHys (a0 :: xs) 0%nat).
  simpl in IHys.
  rewrite merge_nil_r in IHys.
  apply IHys.
  lia.
  inv H0. rewrite H4. auto.
  auto.
  eapply sorted_inv; apply H2.

- inv H0. 
  lia.

-  unfold merge; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
 unfold merge_func at 3;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
unfold merge in H0; unfold merge_func in H0;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
 unfold merge_func in H0 at 3;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.

 remember (a <=? a0).
destruct b; simpl; f_equal.
+  
apply (IHys (a0 :: xs) (S j)).
simpl. lia.
inv H0.  
simpl.
assert ( ( Nat.add j  (S (Datatypes.length ys))) = S(j + Datatypes.length ys) ).
{ lia. }
rewrite H0 in H4.
simpl in H4.
auto.
auto.
eapply sorted_inv; apply H2.

+ inv H0.
rewrite H4.
unfold merge in IHxs at 3 4.
apply IHxs.
lia.
auto.
eapply sorted_inv; apply H1.
auto.
Qed.

Lemma nat_add0 : forall (x : nat), Nat.add x 0%nat = x.
Proof. lia. Qed.

(*
Lemma merge_jiting : forall(i0 i: nat)(xs ys : list Z)(a0 : Z),
    firstn i xs = firstn i (merge xs (a0 :: ys))
 -> Nat.le i (Datatypes.length xs)
 -> sorted xs
 -> sorted (a0 :: ys)
 -> Nat.lt i0 i
 -> nth i0 xs 0 <= a0.
Proof.
  induction i0; intros; destruct xs.
  simpl in H0.
  destruct i; lia.
  simpl.
  unfold merge in H;  unfold merge_func in H;
    rewrite Wf.WfExtensionality.fix_sub_eq_ext in H; simpl in H; fold merge_func in H.
  remember (z <=? a0).
  destruct b.
  lia.
  destruct i; simpl in H.
  inv H3.
  inv H; lia.
  simpl in H0; lia.
  simpl.
  destruct i.
  lia.
  simpl in *.
  apply (IHi0 i xs ys a0); try lia; auto.
  unfold merge in H;  unfold merge_func in H;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext in H; simpl in H; fold merge_func in H.
  remember (z <=? a0).
  destruct b; inv H; auto.

  rewrite (merge_float xs ys a0 H1 H2).
  auto.
  eapply sorted_inv; apply H1.
Qed.    
*)




Lemma merge_invariant : forall (xs ys: list Z) (i j : nat),
       Nat.lt i (length xs)
    -> Nat.lt j (length ys)           
    -> merge (firstn i xs) (firstn j ys) = firstn (i + j) (merge xs ys)
    -> sorted xs
    -> sorted ys
    -> merge xs ys = merge (firstn i xs) (firstn j ys) ++ merge (skipn i xs) (skipn j ys).
Proof.
  intro. intro.
 generalize (lt_n_Sn (length xs + length ys)).        
remember ( S (Datatypes.length xs + Datatypes.length ys)%nat ).
clear Heqn.
generalize xs ys. clear xs ys.
induction n.
{
  intros.
  assert ((Datatypes.length xs + Datatypes.length ys >= 0)%nat ).
  { list_solve. }
  lia.
}

intros.
destruct xs. {
  rewrite firstn_nil.
  rewrite skipn_nil.
  repeat rewrite merge_nil_l.
  rewrite firstn_skipn; auto.
}
destruct ys. {
    rewrite firstn_nil.
  rewrite skipn_nil.
  repeat rewrite merge_nil_r.
  rewrite firstn_skipn; auto.
}
destruct i. {
  simpl in *.
  rewrite merge_nil_l in *.
  apply merge_firstn_r; auto; try lia.
  simpl; lia. 
}
destruct j. {
  simpl.
  simpl in H2.
  rewrite merge_nil_r in H2.
  assert (Nat.add i 0 = i). { lia. }
  rewrite H5 in H2.
  unfold merge in H2;  unfold merge_func in H2;
         rewrite Wf.WfExtensionality.fix_sub_eq_ext in H2; simpl in H2; fold merge_func in H2.
             unfold merge ;  unfold merge_func;
               rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
             simpl in H.
             remember (z <=? z0).
             destruct b; inv H2; f_equal.

      specialize (IHn xs (z0 :: ys)).
      assert ( (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat ).
      { simpl. lia. }
      specialize (IHn H2 i 0%nat).
      simpl in IHn.
      rewrite merge_nil_r in IHn.
      apply IHn; auto; try lia.
      simpl in H0; lia.
      rewrite H5; auto.
      eapply sorted_inv; apply H3.


      specialize (IHn xs (z0 :: ys)).
      assert ((Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat ).
      {simpl. lia. }
      specialize (IHn H2 i 0%nat ).
      simpl in IHn.
      assert (G := merge_float xs ys z0 H3 H4).
      unfold merge in G at 2.
      rewrite <- G.
      rewrite merge_nil_r in IHn.
      apply IHn; auto; try lia.
}

simpl in *.
unfold merge in H2;  unfold merge_func in H2;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H2; simpl in H2; fold merge_func in H2.
unfold merge_func in H2 at 3;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H2; simpl in H2; fold merge_func in H2.     
unfold merge ;  unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
unfold merge_func at 3;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.

 remember (z <=? z0). 
 destruct b; inv H2; simpl; f_equal.

 specialize (IHn xs (z0 :: ys)).
 assert ( (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat ).
 { simpl. lia. }
 specialize (IHn H2 i (S j) ).
 apply IHn; auto; try lia.
 eapply sorted_inv; apply H3.

  specialize (IHn (z :: xs) ys).
  assert ( (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat ).
  { simpl. lia. }
  specialize (IHn H2 (S i) j H0).
  apply IHn; auto; try lia.
  assert ( Nat.add i (S j) = S (Nat.add i  j)). { lia. }
  rewrite H5 in H6.
  simpl in H6.
  auto.
  eapply sorted_inv; apply H4.
Qed.


Lemma merge_invariant_l : forall (xs ys: list Z) (i j k : nat),
       Nat.lt i (length xs)
    -> Nat.lt j (length ys)
    -> Nat.le i k
    -> merge (firstn i xs) (firstn j ys) = firstn (i + j) (merge xs ys)
    -> sorted xs
    -> sorted ys
    -> merge (firstn i xs) (firstn j ys) = firstn (i + j) (merge (firstn k xs) ys) .
Proof.
  intro. intro.
 generalize (lt_n_Sn (length xs + length ys)).        
 remember ( S (Datatypes.length xs + Datatypes.length ys)%nat ).
 clear Heqn.
generalize xs ys. clear xs ys.
induction n.
intros.
{
    intros.
  assert ((Datatypes.length xs + Datatypes.length ys >= 0)%nat ).
  { list_solve. }
  lia.
}

intros.
destruct xs.
{
  repeat rewrite firstn_nil in *.
  repeat rewrite merge_nil_l in *.
  auto.
}
destruct ys.
{
  simpl in H1.
  destruct j; lia.
}

destruct i.
{ simpl in *.
  rewrite merge_nil_l in *.
  destruct j; simpl; auto.
  destruct k; simpl; auto.
  simpl in H3.
   unfold merge;  unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func. 
    unfold merge in H3;  unfold merge_func in H3;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext in H3; simpl in H3; fold merge_func in H3.  
    remember (z <=? z0).
    destruct b; inv H3; f_equal.
    specialize (IHn (z :: xs) ys).
    assert ( (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat ).
    { simpl. lia. }
    specialize (IHn H3 0%nat j (S k)).
    simpl in IHn.
    rewrite merge_nil_l in IHn.
    assert (G := merge_float (firstn k xs) ys z).
    assert ( merge (firstn k xs) (z :: ys) = merge (z :: firstn k xs) ys) .
    apply G; auto.
    apply sorted_firstn_helper; auto.
    rewrite <- H6 in IHn.
    apply IHn; auto; try lia.
    rewrite H8; f_equal.
    apply merge_float; auto.
    eapply sorted_inv; apply H5.

    specialize (IHn (z :: xs) ys).
    assert ( (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat ).
    { simpl. lia. }
    specialize (IHn H3 0%nat j (S k)).
    apply IHn; auto; try lia.
    eapply sorted_inv; apply H5.
    
}
{
  destruct j.
  rewrite firstn_O in *.
  rewrite merge_nil_r in *.
    assert (H60 : Nat.add (S i)  0 = S i).
  { lia. }
  destruct k. inv H2.

  rewrite H60 in *.
  simpl in *.
   unfold merge;  unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func. 
    unfold merge in H3;  unfold merge_func in H3;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext in H3; simpl in H3; fold merge_func in H3.  
    remember (z <=? z0).
    destruct b; inv H3; f_equal.

    specialize (IHn xs (z0 :: ys)).

    assert ( (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat ).
    { simpl. lia. }
specialize (IHn H3 i 0%nat k).
    simpl in IHn.
    rewrite merge_nil_r in IHn.
    assert ( H70 : Nat.add i 0 = i). { lia. }
    rewrite H70 in IHn.
    apply IHn; auto; try lia.
    eapply sorted_inv; apply H4.
    lia.

    simpl in *.
    destruct k.
    lia.

    simpl.
       unfold merge;  unfold merge_func;
         rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
       unfold merge_func at 3;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func. 
    unfold merge in H3;  unfold merge_func in H3;
      rewrite Wf.WfExtensionality.fix_sub_eq_ext in H3; simpl in H3; fold merge_func in H3.
      unfold merge_func in H3 at 3;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext in H3; simpl in H3; fold merge_func in H3.  
    remember (z <=? z0).
    destruct b; inv H3; f_equal.
    specialize (IHn xs (z0 :: ys)).
    assert ( (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat  ).
    { simpl. lia. }
    specialize ( IHn H3 i (S j) k).
    apply IHn; auto; try lia.
    eapply sorted_inv; apply H4.

    specialize (IHn (z :: xs) ys ).
    assert (  (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat ).
    { simpl. lia. }
    specialize (IHn H3 (S i) j (S k)).
    assert (H70 : (Nat.add (S i) j) = Nat.add i (S j)). { lia. }
    rewrite H70 in IHn.
    simpl in IHn.
    apply IHn; auto; try lia.
    eapply sorted_inv; apply H5.
}

Qed.


Lemma skipn_length (n : nat) :
  forall {A} (l : list A), length (skipn n l) = Nat.sub (length l) n.
Proof.
  intros A.
  induction n.
  - intros l; simpl; rewrite Nat.sub_0_r; reflexivity.
  - destruct l; simpl; auto.
Qed.

Program Fixpoint mergesort (x : list Z) {measure (length x)}: list Z :=
  match x with
  | nil => nil
  | x :: nil => x :: nil
  | x :: y :: nil => if x <? y
    then (x :: y :: nil)
    else (y :: x :: nil)
  | x :: y :: z :: rest => 
    let a := (x :: y :: z :: rest) in 
    let p := (Nat.div2 (length a)) in
    merge (mergesort (firstn p a)) (mergesort (skipn p a))
  end.
Next Obligation.
  rewrite firstn_length.
  simpl.
  apply lt_n_S.
  apply Nat.min_lt_iff.
  left.
  destruct (length rest).
  auto.
  apply lt_n_S.
  destruct n.
  auto.
  rewrite Nat.lt_div2.
  auto.
  apply Nat.lt_0_succ.
Qed.
Next Obligation.
  rewrite skipn_length.
  simpl.
  destruct (length rest).
  auto.
  destruct Nat.div2.
  auto.
  rewrite Nat.lt_succ_r.
  rewrite Nat.le_succ_r.
  left.
  rewrite Nat.le_succ_r.
  left.
  rewrite Nat.le_sub_le_add_r.
  apply le_plus_l.
Qed.



  
  
Lemma merge_Zlength : forall l1 , forall l2 , Zlength (merge l1 l2 ) = Zlength l1 + Zlength l2.
Proof.
  induction l1.
  intros.
  intuition.

  induction l2.
  intuition.

  unfold merge;  unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
  destruct (a <=? a0); simpl; do 3 rewrite Zlength_cons.

  specialize (IHl1 (a0 :: l2)). 
  unfold merge in IHl1.
  rewrite IHl1.
  intuition.

  unfold merge in IHl2.
  rewrite IHl2.
  intuition.
Qed.

Lemma sorted_mergesort : forall l, sorted (mergesort l).
Proof.
Admitted.

Lemma mergesort_length : forall l,  length (mergesort l ) = length l.
Proof.
  intro.
 generalize (lt_n_Sn (length l)).
remember (S (length l)).
clear Heqn.
generalize l. clear l.
induction n; intros.
destruct l; simpl in *; auto.
inv H.

destruct l.
simpl; auto.
destruct l.
simpl; auto.
destruct l.
unfold mergesort.
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold mergesort.
destruct (z <? z0); simpl; auto.

unfold mergesort.
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold mergesort.
Admitted.


Lemma mergesort_zlength : forall l,  Zlength (mergesort l ) = Zlength l.
Proof.
intros.
do 2 rewrite Zlength_correct.
f_equal.
apply mergesort_length.
Qed.

Definition my_mergesort_spec : ident * funspec :=
 DECLARE _my_mergesort
 WITH p: val,  sh : share, il: list Z, gv: globals
 PRE [ tptr tuint , tint ] 
    PROP (readable_share sh;
          0 < Zlength il <= Int.max_signed) 
    PARAMS (p; Vint (Int.repr (Zlength il)) )
    GLOBALS(gv) 
    SEP  (data_at sh (tarray tuint (Zlength il)) (map Vint (map Int.repr il)) p;
          mem_mgr gv)
 POST [ tvoid ] 
    PROP ( ) RETURN ()
    SEP (data_at sh (tarray tuint (Zlength (mergesort il))) (map Vint (map Int.repr (mergesort il))) p;
         mem_mgr gv).


Definition Gprog : funspecs :=
  ltac:(with_library prog [
             my_mergesort_spec                                    
 ]). 

Lemma div2_le : forall z, z >= 0 -> Z.div2 z <= z .
Proof.
intros.
unfold Z.div2.
destruct z.
- lia.
- destruct p; unfold Pos.div2; lia.
- contradiction.
Qed.

Lemma div2_le2 : forall z, z > 0 -> Z.div2 z < z .
Proof.
intros.
unfold Z.div2.
destruct z.
- lia.
- destruct p; unfold Pos.div2; lia.
- discriminate.
Qed.

Lemma z2n : forall x : Z , 0 < x <= Int.max_signed -> Int.divs (Int.repr x) (Int.repr 2) = Int.repr (Z.div2 x).
Proof.
  unfold Int.divs.
  intros.
  rewrite Int.signed_repr; try rep_lia.
  rewrite Int.signed_repr; try rep_lia.
  f_equal.
  rewrite Zdiv2_div.
  apply Zquot.Zquot_Zdiv_pos; lia.
Qed.


Lemma body_my_mergesort: semax_body Vprog Gprog f_my_mergesort my_mergesort_spec.
Proof.
  start_function.
  forward_if (Zlength il > 1).
  {
    forward.
    destruct il.
    rewrite Zlength_nil in H. inv H0. 
    destruct il. {
      rewrite mergesort_zlength.
      unfold mergesort.
      simpl.
      entailer!.
    }  {
      do 2 rewrite Zlength_cons in H0.
      assert (0 <= Zlength il ).
      apply Zlength_nonneg.
      assert (Z.succ (Z.succ (Zlength il)) >= 2). lia.
      rewrite H0 in H5. contradiction.
    }
  }
  {
    forward.
    entailer!.
  }
  forward.
  entailer!.
  destruct H4.
  inv H5.
  forward.
  forward.

  assert (H70 : Z.div2 (Zlength il) <= Zlength il). {
    apply  div2_le .
    lia.
  }

  assert (H71:  (Z.min (Z.div2 (Zlength il)) (Zlength il)) = Z.div2 (Zlength il) ) .
  { apply Z.min_l.
    apply div2_le. lia. }

  assert (H80 : (Z.max (Z.div2 (Zlength il)) 0) = Z.div2 (Zlength il) ).
  apply Zmax_left.
  assert (H81 : 0 <= Z.div2 (Zlength il)). {
    apply Z.div2_nonneg. lia. }
  lia.

  rewrite <- (firstn_skipn (Z.to_nat (Z.div2 (Zlength il))) il ) at 5.
  rewrite map_app.
  rewrite map_app.
  rewrite (split2_data_at_Tarray_app  (Z.div2 (Zlength il))).


  (* mergesort  1*)
  (* forward_call (p , sh , firstn (Nat.div2 (length il) ) il, gv). *)
  forward_call (p , sh , firstn (Z.to_nat (Z.div2 (Zlength il))) il, gv).

  { 
    entailer!; simpl.
    rewrite Zlength_solver.Zlength_firstn_to_nat.
    rewrite H80.
    rewrite H71.
    rewrite  z2n; auto. 
  }
  
  {  
    rewrite Zlength_solver.Zlength_firstn_to_nat.
    rewrite H80. rewrite H71.
    entailer!. 
  }

 { 
    rewrite Zlength_solver.Zlength_firstn_to_nat.
    rewrite H80. rewrite H71.
    rewrite Zdiv2_div .
    split; try rep_lia.
    apply Z.div_str_pos; rep_lia.
 }

 remember (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)) as l1.

  (* mergesort 2 *)
  forward_call ( (field_address0 (tarray tuint (Zlength il)) (SUB Z.div2 (Zlength il)) p) , sh , skipn (Z.to_nat (Z.div2 (Zlength il))) il, gv).
  {
    unfold Int.divs.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Zquot.Zquot_Zdiv_pos; auto; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Zquot.Zquot_Zdiv_pos; auto; try rep_lia.     
  }
  { 
    entailer!.
    simpl.
    f_equal.

    unfold Int.divs.
    rewrite sem_add_pi'; auto.
    rewrite field_address0_clarify; auto.
    (*  rewrite field_address0_offset. *)
    f_equal; simpl.  
    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Zdiv2_div .
    rewrite Zquot.Zquot_Zdiv_pos; lia.

    rewrite Zquot.Zquot_Zdiv_pos.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.

    do 2 f_equal.
    unfold Int.sub; unfold Int.divs.
    rewrite Int.unsigned_repr; try rep_lia.
    rewrite Int.unsigned_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Zlength_solver.Zlength_skipn_to_nat.            
    rewrite Zmax_left; try rep_lia.  
    rewrite Zmax_left; try rep_lia.
    rewrite Zdiv2_div .
    rewrite Zquot.Zquot_Zdiv_pos; auto; try rep_lia.

    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Zquot.Zquot_Zdiv_pos; try rep_lia.              
  }

  {
    rewrite Zlength_solver.Zlength_skipn_to_nat.  
    rewrite Zmax_left; try rep_lia.  
    rewrite Zmax_left; try rep_lia.
    entailer!.
  }

  { 
    rewrite Zlength_solver.Zlength_skipn_to_nat. 
    rewrite Zmax_left; try rep_lia.  
    rewrite Zmax_left; try rep_lia.
    split; try rep_lia.
    assert ( Z.div2 (Zlength il) < Zlength il). {apply div2_le2. lia. }
    rep_lia.
  }

  forward_call ( tarray tuint (Zlength il), gv).
  simpl; rewrite Zmax_right; rep_lia.
  
  Intro t.
  destruct ( eq_dec t nullval ).
  forward_if False.
  forward_call. inv H2. congruence.

  forward_if True.
  congruence.
  forward.
  entailer.
  Intros.
  forward.
  forward.
  forward.

  do 2 rewrite mergesort_zlength.
  rewrite Zlength_solver.Zlength_firstn_to_nat. 
  rewrite Zmax_left; try rep_lia.
  rewrite Z.min_l; try rep_lia.
  rewrite Zlength_solver.Zlength_skipn_to_nat.
  rewrite Zmax_left; try rep_lia.
  rewrite Zmax_left; try rep_lia.

  assert (0 < Z.div2 (Zlength il)). {
    remember (Zlength il).
    destruct z; try lia.
    unfold Z.div2.
    destruct p0; lia.
  }

  assert ( Z.div2 (Zlength il) < Zlength il ). {
    apply div2_le2; lia.
  }

  unfold Int.divs.
  rewrite Int.signed_repr; try rep_lia.
  rewrite Int.signed_repr; try rep_lia.
  rewrite Zquot.Zquot_Zdiv_pos; auto; try rep_lia.

      assert (
  data_at sh (tarray tuint (Zlength il - Z.div2 (Zlength il)))
    (map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))
    (field_address0 (tarray tuint (Zlength il)) (SUB Z.div2 (Zlength il)) p) *
  data_at sh (tarray tuint (Z.div2 (Zlength il)))
    (map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)))) p
  |-- data_at sh (tarray tuint (Zlength il))
        (map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))) ++
         map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))) p
    ).
  {
    rewrite (split2_data_at_Tarray_app (Z.div2 (Zlength il))).
    entailer!.
    do 2 rewrite Zlength_map.
    rewrite mergesort_zlength.
      rewrite Zlength_solver.Zlength_firstn_to_nat. 
      rewrite H80.
      rewrite H71. auto.

      do 2 rewrite Zlength_map.
          rewrite mergesort_zlength.
      rewrite Zlength_solver.Zlength_skipn_to_nat.       
      rewrite H80.
      rewrite Zmax_left; rep_lia.
  }
  
  remember (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)) as l2.

  forward_loop (
     EX i, EX j, EX k,
     PROP(0 <= i < Z.div2 (Zlength il);
          Z.div2 (Zlength il) <= j < Zlength il;
          0 <= k < Zlength il;
          Z.add k (Z.div2 (Zlength il)) = Z.add i j;
          firstn (Z.to_nat (i + (j - Z.div2 (Zlength il)))) (merge l1 l2) =
          merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Z.div2 (Zlength il))) l2) )
     LOCAL (temp _k (Vint (Int.repr k));
            temp _j (Vint (Int.repr j));
            temp _i (Vint (Int.repr i));
            temp _t t;
            temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
            temp _arr1 p;
            temp _p (Vint (Int.repr (Zlength il / 2)));
            gvars gv; 
            temp _arr p;
            temp _len (Vint (Int.repr (Zlength il)))
       )
       
     SEP (mem_mgr gv;
          malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
                (map Vint (map Int.repr (merge
                (sublist 0 i l1)
                (sublist 0 (j - (Zlength il / 2)) l2 )))
                ++  Zrepeat (default_val tuint) (Zlength il - k)) t;
      data_at sh (tarray tuint (Zlength il))
          ((map Vint (map Int.repr l1 )) ++
           (map Vint (map Int.repr l2 )))
              p
         )
    )
    break:
    (
     EX i, EX j, EX k,
      PROP( i = Z.div2 (Zlength il) \/ j <= Zlength il;
            0 <= k <= Zlength il;
            Z.add k (Z.div2 (Zlength il)) = Z.add i j;
            firstn (Z.to_nat (i + (j - Z.div2 (Zlength il)))) (merge l1 l2) =
            merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j -  (Zlength il) / 2 )) l2)
          )
     LOCAL (temp _k (Vint (Int.repr k));
            temp _j (Vint (Int.repr j));
            temp _i (Vint (Int.repr i));
            temp _t t;
            temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
            temp _arr1 p;
            temp _p (Vint (Int.repr (Zlength il / 2)));
            gvars gv; 
            temp _arr p;
            temp _len (Vint (Int.repr (Zlength il))))
     
     SEP (mem_mgr gv;
          malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
                (map Vint (map Int.repr (merge
                (sublist 0 i l1 )
                (sublist 0 (j - (Zlength il /2)) l2 )))
                ++  Zrepeat (default_val tuint) (Zlength il - k)) t;
      data_at sh (tarray tuint (Zlength il))
          ((map Vint (map Int.repr l1 )) ++
           (map Vint (map Int.repr l2 )))
              p
         )
    ).
  
  Exists 0.
  Exists ((Zlength il) / 2).
  Exists 0.
  sep_apply H3.
  rewrite data_at__tarray.
  rewrite sublist_nil.
  assert ((Zlength il / 2 - Zlength il / 2) = 0 ). { lia. }
  rewrite H4.
  entailer!.
  rewrite Zdiv2_div; rewrite H4; simpl; rewrite merge_nil_r; auto.
  simpl; entailer!.
  
  Intro i. Intro j. Intro k. Intros.
  
  forward_if (
     PROP ( )
     LOCAL (temp _k (Vint (Int.repr k));
            temp _j (Vint (Int.repr j));
            temp _i (Vint (Int.repr i));
            temp _t t;
            temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
            temp _arr1 p;
            temp _p (Vint (Int.repr (Zlength il / 2)));
            gvars gv; 
            temp _arr p;
            temp _len (Vint (Int.repr (Zlength il)));
            temp _t'2 (Val.of_bool true)
           )
     
     SEP (mem_mgr gv;
          malloc_token Ews (tarray tuint (Zlength il)) t;
               data_at Ews (tarray tuint (Zlength il))
                (map Vint (map Int.repr (merge
                (sublist 0 i l1)
                (sublist 0 (j - (Zlength il /2)) l2)))
                ++  Zrepeat (default_val tuint) (Zlength il - k)) t;
      data_at sh (tarray tuint (Zlength il))
          ((map Vint (map Int.repr l1 )) ++
           (map Vint (map Int.repr l2 )))
              p
         )
    ).

  forward.
  entailer!.
  {
    f_equal.
    unfold Int.lt.
    rewrite Int.signed_repr; try rep_lia.
    rewrite Int.signed_repr; try rep_lia.
    destruct (zlt j (Zlength il)).
    auto.
    lia. 
  }

  auto. 
  
  forward.
  entailer!.
  auto.
  
  forward_if True.
  forward.
  entailer!.
  discriminate.
  abbreviate_semax; Intros.

  forward.
  entailer!.
  list_solve.

  forward.
  entailer!.
 list_solve.

 (*  分类讨论 _t'5 <= _t'6 *)
 
 remember ((Znth i
          (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il) ++
          mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))
           <=?
          (Znth j
               (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il) ++
                mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il) ))
          ).
destruct b.


  forward_if (
     PROP ( )
     LOCAL (temp _k (Vint (Int.repr k));
            temp _j (Vint (Int.repr j));
            temp _i (Vint (Int.repr (i + 1)));
            temp _t t;
            temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
            temp _arr1 p;
            temp _p (Vint (Int.repr (Zlength il / 2)));
            gvars gv; 
            temp _arr p;
            temp _len (Vint (Int.repr (Zlength il)));
            temp _t'2 (Val.of_bool true)
           )
     
     SEP (mem_mgr gv;
          malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
                (map Vint (map Int.repr (merge
                (sublist 0 (i + 1) (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)))
                (sublist 0 (j - (Zlength il /2)) (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))))
                ++  Zrepeat  (default_val tuint) (Zlength il - (k + 1))) t;
      data_at sh (tarray tuint (Zlength il))
          ((map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)))) ++
           (map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))))
              p
         )
    ).

  forward.
  forward.
  forward.
  entailer!.

  rewrite upd_Znth_app2.
  repeat rewrite Zlength_map.
  rewrite merge_Zlength.
  repeat rewrite Zlength_sublist.
  assert ( H50 : (k - (i - 0 + (j - Zlength il / 2 - 0))) = 0). { lia. }
  rewrite H50; clear H50.
  rewrite Znth_app1.
  assert ( H50 : (Zlength il - k) =  1 + (Zlength il - (k + 1)) ). { lia. }
  rewrite H50; clear H50.
  rewrite <- (Zrepeat_app 1).
  rewrite <- cons_Zrepeat_1_app.
  rewrite upd_Znth0.

   remember (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)) as l1.
   remember (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)) as l2.

   assert (i < Zlength l1). {
      rewrite   Heql1.
      rewrite mergesort_zlength.
      rewrite Zlength_firstn.
      rewrite Z.max_r; lia.
   }
   assert (Zlength l2 = Zlength il - Zlength il / 2 ). {
     rewrite   Heql2.
           rewrite mergesort_zlength.
      rewrite Zlength_skipn.
      rewrite Z.max_r; lia.
   }
   
   assert (
  (merge (sublist 0 i l1) (sublist 0 (j - Zlength il / 2) l2)) ++
      Znth i l1 :: []
    =
   merge (sublist 0 (i + 1) l1) (sublist 0 (j - Zlength il / 2) l2)
     ).
   {
     assert (merge l1 l2 =
             merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Zlength il /2)) l2)
                   ++
             merge (skipn (Z.to_nat i) l1) (skipn (Z.to_nat (j - Zlength il /2 )) l2)
            ).
     apply merge_invariant.
     rewrite  Zlength_correct in H20.
     apply Nat2Z.inj_lt; rewrite Z2Nat_id'.
     rewrite Z.max_r; lia.

       apply Nat2Z.inj_lt.
       rewrite Z2Nat_id'.
           rewrite Z.max_r; try lia.
           rewrite <- Zlength_correct.
           rep_lia.

           clear H15.
             rewrite Zdiv2_div in H8.
             rewrite <- H8.
             f_equal; rep_lia.
            rewrite   Heql1; apply sorted_mergesort.
            rewrite   Heql2; apply sorted_mergesort.
                             rewrite Z2Nat.inj_add in H8; try lia.
     assert (G := merge_invariant_l l1 l2  (Z.to_nat i) (Z.to_nat (j - Zlength il / 2)) (Z.to_nat i + 1) ).
     assert ( merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Zlength il / 2)) l2) =
      firstn (Z.to_nat i + Z.to_nat (j - Zlength il / 2)) (merge (firstn (Z.to_nat i + 1) l1) l2) ).
     apply G.
     
   apply Nat2Z.inj_lt; rewrite Z2Nat_id'.
   rewrite Z.max_r.
     rewrite <- Zlength_correct. lia.
 lia.

    apply Nat2Z.inj_lt; rewrite Z2Nat_id'.
   rewrite Z.max_r.
     rewrite <- Zlength_correct. lia.
 lia.
 lia.
  rewrite Zdiv2_div in H8; auto.
            rewrite   Heql1; apply sorted_mergesort.
            rewrite   Heql2; apply sorted_mergesort.

   }
