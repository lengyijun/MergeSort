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
       firstn (length ys + j) (merge ys xs) = merge ys (firstn j xs)
    -> Nat.le j (length xs)
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
rewrite merge_nil_r in H.

unfold merge; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
unfold merge in H; unfold merge_func in H;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H; simpl in H; fold merge_func in H.
remember (a <=? a0).
destruct b.
- f_equal.
  specialize (IHys (a0 :: xs) 0%nat).
  simpl in IHys.
  rewrite merge_nil_r in IHys.
  apply IHys; auto; try lia.
  inv H. rewrite H4. auto.
  eapply sorted_inv; apply H2.

- inv H. 
  lia.

-  unfold merge; unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
 unfold merge_func at 3;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
unfold merge in H; unfold merge_func in H;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H; simpl in H; fold merge_func in H.
 unfold merge_func in H at 3;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H; simpl in H; fold merge_func in H.

 remember (a <=? a0).
destruct b; simpl; f_equal.
+  
apply (IHys (a0 :: xs) (S j)); auto.
inv H.  
simpl.
auto.
eapply sorted_inv; apply H2.

+ inv H.
rewrite H4.
unfold merge in IHxs at 3 4.
apply IHxs; auto; try lia.
simpl.
assert ( G: ( Nat.add (Datatypes.length ys) (S j)) = S (Nat.add (Datatypes.length ys) j ) ).
{ lia. }
rewrite G in H4.
auto.
eapply sorted_inv; apply H1.
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
       merge (firstn i xs) (firstn j ys) = firstn (i + j) (merge xs ys)
    -> Nat.le i (length xs)
    -> Nat.le j (length ys)           
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
}
destruct j. {
  simpl.
  simpl in H0.
  rewrite merge_nil_r in H0.
  assert (Nat.add i 0 = i). { lia. }
  rewrite H5 in H0.
  unfold merge in H0;  unfold merge_func in H0;
         rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
             unfold merge ;  unfold merge_func;
               rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
             simpl in H.
             remember (z <=? z0).
             destruct b; inv H0; f_equal.

      specialize (IHn xs (z0 :: ys)).
      assert ( (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat ).
      { simpl. lia. }
      specialize (IHn H0 i 0%nat).
      simpl in IHn.
      rewrite merge_nil_r in IHn.
      apply IHn; auto; try lia.
      rewrite H7; f_equal; try lia.
      simpl in H1; lia.
      eapply sorted_inv; apply H3.


      specialize (IHn xs (z0 :: ys)).
      assert (H20 : (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat ).
      {simpl. lia. }
      specialize (IHn H20 i 0%nat ).
      simpl in IHn.
      assert (G := merge_float xs ys z0 H3 H4).
      unfold merge in G at 2.
      rewrite <- G.
      rewrite merge_nil_r in IHn.
      apply IHn; auto; try lia.
}

simpl in *.
unfold merge in H0;  unfold merge_func in H0;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
unfold merge_func in H0 at 3;
rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.     
unfold merge ;  unfold merge_func;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
unfold merge_func at 3;
rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.

 remember (z <=? z0). 
 destruct b; inv H0; simpl; f_equal.

 specialize (IHn xs (z0 :: ys)).
 assert ( H20 : (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat ).
 { simpl. lia. }
 specialize (IHn H20 i (S j) ).
 apply IHn; auto; try lia.
 eapply sorted_inv; apply H3.

  specialize (IHn (z :: xs) ys).
  assert ( H20 : (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat ).
  { simpl. lia. }
  specialize (IHn H20 (S i) j).
  apply IHn; auto; try lia.
  assert ( H30 : Nat.add i (S j) = S (Nat.add i  j)). { lia. }
  rewrite H30 in H6.
  simpl in H6.
  auto.
  eapply sorted_inv; apply H4.
Qed.

(*
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
  simpl in H0.
  destruct i; lia.
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


Lemma merge_invariant_r : forall (xs ys: list Z) (i j k : nat),
       Nat.lt i (length xs)
    -> Nat.lt j (length ys)
    -> Nat.le j k
    -> merge (firstn i xs) (firstn j ys) = firstn (i + j) (merge xs ys)
    -> sorted xs
    -> sorted ys
    -> merge (firstn i xs) (firstn j ys) = firstn (i + j) (merge xs (firstn k ys)) .                                                                                                          
Proof.
  intro. intro.
 generalize (lt_n_Sn (length xs + length ys)).     
 remember ( S (Datatypes.length xs + Datatypes.length ys)%nat ).
 clear Heqn.
generalize xs ys. clear xs ys.
induction n; intros.

{
   assert ((Datatypes.length xs + Datatypes.length ys >= 0)%nat ).
  { list_solve. }
  lia. 
}

destruct xs.
{
  simpl in H0. 
  destruct j; lia.
}
destruct ys.
{
  simpl in H1.
  destruct i; lia.
}

destruct k.
destruct j; try lia.
simpl. 
repeat rewrite merge_nil_r.
assert ( H9 : i = Nat.add i 0). { lia. }
rewrite <- H9; auto.

destruct i; destruct j; simpl in *.
rewrite merge_nil_l in *; auto.
rewrite merge_nil_l in *.
       unfold merge;  unfold merge_func;
         rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
    unfold merge in H3;  unfold merge_func in H3;
      rewrite Wf.WfExtensionality.fix_sub_eq_ext in H3; simpl in H3; fold merge_func in H3.
remember (z <=? z0).
destruct b; inv H3; f_equal.
specialize (IHn (z :: xs) ys).
assert ( (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat ).
{ simpl. lia. }
specialize (IHn H3 0%nat j k).
simpl in IHn.
rewrite merge_nil_l in IHn.
assert ( G  := merge_float xs (firstn k ys) z).
unfold merge in  G at 1.
rewrite G; auto.
apply IHn; auto; try lia.
rewrite H8.
assert (M := merge_float xs ys z).
unfold merge in M at 1.
rewrite M; auto.
eapply sorted_inv; apply H5.
apply sorted_firstn_helper; auto.

specialize (IHn (z :: xs) ys).
assert  (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat .
{ simpl. lia. }
specialize (IHn H3 0%nat j k).
apply IHn; auto; try lia.
eapply sorted_inv ; apply H5.


rewrite merge_nil_r in *.
       unfold merge;  unfold merge_func;
         rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
    unfold merge in H3;  unfold merge_func in H3;
      rewrite Wf.WfExtensionality.fix_sub_eq_ext in H3; simpl in H3; fold merge_func in H3.
remember (z <=? z0).
destruct b; inv H3; f_equal.
specialize ( IHn xs (z0 :: ys) ).
assert ( (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat ).
{ simpl. lia. }
specialize (IHn H3 i 0%nat (S k)).
simpl in IHn.
rewrite merge_nil_r in IHn.
apply IHn; auto; try lia.
eapply sorted_inv; apply H4.

specialize (IHn xs (z0 :: ys)).
assert ( (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat  ).
{ simpl; lia. }
specialize (IHn H3 i 0%nat (S k)).
simpl in IHn.
rewrite merge_nil_r in IHn.
assert (G := merge_float xs (firstn k ys) z0).
unfold merge in G at 2.
rewrite <- G; auto.
apply IHn; auto ; try lia.
apply sorted_firstn_helper; auto.

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
assert (  (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat).
{ simpl; lia. }
specialize (IHn H3 i (S j) (S k)).
simpl in IHn.
apply IHn; auto; try lia.
eapply sorted_inv; apply H4.

specialize (IHn (z :: xs) ys).
assert (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat .
{ simpl; lia. }
specialize (IHn H3 (S i) j k).
   assert (H70 : (Nat.add (S i) j) = Nat.add i (S j)). { lia. }
    rewrite H70 in IHn.
    simpl in IHn.
    apply IHn; auto; try lia.
    eapply sorted_inv; apply H5.
Qed.
 *)


Lemma merge_invariant_lr : forall (xs ys: list Z) (i j p q : nat),
       merge (firstn i xs) (firstn j ys) = firstn (i + j) (merge xs ys)
    -> Nat.le i (length xs)
    -> Nat.le j (length ys)
    -> Nat.le i p
    -> Nat.le j q
    -> sorted xs
    -> sorted ys
    -> merge (firstn i xs) (firstn j ys) = firstn (i + j) (merge (firstn p xs) (firstn q ys)) .
Proof.
  intro. intro.
 generalize (lt_n_Sn (length xs + length ys)).     
 remember ( S (Datatypes.length xs + Datatypes.length ys)%nat ).
 clear Heqn.
generalize xs ys. clear xs ys.
induction n; intros.

{
   assert ((Datatypes.length xs + Datatypes.length ys >= 0)%nat ).
  { list_solve. }
  lia. 
}

destruct xs.
{
  simpl in H1.
  destruct i; try lia.
  repeat rewrite firstn_nil.
  repeat rewrite merge_nil_l.
  rewrite firstn_firstn.
  rewrite Nat.min_l; try lia.
  f_equal; lia.
}
destruct ys.
{
  simpl in H2.
  destruct j; try lia.
  repeat rewrite firstn_nil.
  repeat rewrite merge_nil_r.
  rewrite firstn_firstn.
  rewrite Nat.min_l; try lia.
  f_equal; lia.
}
destruct p.
destruct i; try lia.
simpl.
repeat rewrite merge_nil_l in *.
destruct q; destruct j; try lia; simpl; auto; f_equal.

assert (H7 : Nat.add 0 (S j) = S j). { lia. }
rewrite H7 in H0.
    unfold merge in H0;  unfold merge_func in H0;
      rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
remember (z <=? z0).
destruct b; inv H0; simpl in *.  

specialize (IHn (z :: xs) ys).
assert ( G: (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat ).
{ simpl; lia.}
specialize (IHn G 0%nat j 0%nat q).
simpl in IHn; repeat rewrite merge_nil_l in IHn.
apply IHn; auto; try lia.
rewrite H10; f_equal.
apply merge_float; auto.
eapply sorted_inv; apply H6.

specialize (IHn (z :: xs) ys).
assert (G : (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat ).
{ simpl; lia.}
specialize (IHn G 0%nat j 0%nat q).
apply IHn; auto; try lia.
eapply sorted_inv; apply H6.

destruct q; destruct j; try lia; destruct i; simpl in *.
repeat rewrite merge_nil_r in *; auto.
rewrite merge_nil_r in *; f_equal.
    unfold merge in H0;  unfold merge_func in H0;
      rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
remember ( z <=? z0 ).
destruct b; inv H0.

specialize (IHn xs (z0 :: ys)).
assert ( G: (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat ).
{ simpl ; lia. }
specialize (IHn G i 0%nat p 0%nat).

assert ( H10 : Nat.add i 0 = i). { lia. }
rewrite H10 in *.
simpl in IHn.
repeat rewrite merge_nil_r in IHn.
apply IHn; auto; try lia.
eapply sorted_inv; apply H5.
lia.
rewrite merge_nil_r; auto.
rewrite merge_nil_r in *.
    unfold merge in H0;  unfold merge_func in H0;
      rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
       unfold merge;  unfold merge_func;
         rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
remember ( z <=? z0 ).
destruct b; inv H0; f_equal.

specialize (IHn xs (z0 :: ys)).
assert ( G: (Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat ).
{ simpl; lia. }
specialize (IHn G i 0%nat p (S q)).
simpl in IHn.
rewrite merge_nil_r in IHn.
apply IHn ; auto; try lia.
eapply sorted_inv; apply H5.

lia.

rewrite merge_nil_l in *.
    unfold merge in H0;  unfold merge_func in H0;
      rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
       unfold merge;  unfold merge_func;
         rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
remember ( z <=? z0 ).

specialize (IHn (z :: xs) ys ).
assert (H20 :  (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat ).
{ simpl ; lia. }
specialize (IHn H20 0%nat j (S p) q).
simpl in IHn.
rewrite merge_nil_l in IHn.
destruct b; inv H0; f_equal.

assert (G := merge_float (firstn p xs) (firstn q ys) z).
unfold merge in G at 1.
rewrite G.
apply IHn; auto; try lia.
rewrite H9; f_equal.
apply merge_float; auto.
eapply sorted_inv ; apply H6.
apply sorted_firstn_helper; auto.
apply sorted_firstn_helper; auto.


apply IHn; auto; try lia.
eapply sorted_inv; apply H6.

    unfold merge in H0;  unfold merge_func in H0;
      rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0; fold merge_func in H0.
     unfold merge_func in H0 at 3; 
      rewrite Wf.WfExtensionality.fix_sub_eq_ext in H0; simpl in H0 ;fold merge_func in H0.
       unfold merge;  unfold merge_func;
         rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
 unfold merge_func at 3;
         rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
remember (z <=? z0).
destruct b; inv H0; f_equal.

specialize (IHn xs (z0 :: ys)).
assert  (G : ( Datatypes.length xs + Datatypes.length (z0 :: ys) < n)%nat) .
{ simpl; lia. }
specialize (IHn G i (S j) p (S q)).
apply IHn; auto; try lia.
eapply sorted_inv; apply H5.

specialize (IHn (z :: xs) ys).
assert ( G : (Datatypes.length (z :: xs) + Datatypes.length ys < n)%nat ) .
{ simpl; lia. }
specialize (IHn G (S i) j (S p) q).
   assert (H70 : (Nat.add (S i) j) = Nat.add i (S j)). { lia. }
rewrite H70 in IHn.
simpl in IHn.
apply IHn; auto; try lia.
eapply sorted_inv ; apply H6.
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
  | x :: y :: nil => if x <=? y
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

Lemma mergesort_refl : forall (x : list Z) , mergesort x =
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
Proof.
intros.
destruct x.
- intuition.
- destruct x.
  intuition.
destruct x.
intuition.
simpl.
unfold mergesort at 1.
rewrite fix_sub_eq. repeat fold mergesort.
repeat f_equal.
intuition.
repeat f_equal.
intros.
destruct x0.
auto.
destruct x0.
auto.
destruct x0.
auto.
intuition.
Qed.

Lemma mergesort_1 : forall x, mergesort [x] = [x].
Proof.
intros.
 unfold mergesort;   unfold merge;  unfold merge_func;                                                                                                             
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl.
auto.
Qed. 

Lemma Zdiv2_Natdiv2 : forall x : Z , x > 0 -> Z.to_nat (Z.div2 x) = Nat.div2 (Z.to_nat x).
Proof.
  intros.
rewrite Nat.div2_div.  
rewrite  Zdiv2_div.
rewrite Z2Nat.inj_div; auto; lia.
Qed.

Lemma mergesort_merge : forall il ,  merge
    (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))
    (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)) = mergesort il.
Proof.
intros.
rewrite  (mergesort_refl il).
destruct il; auto.
destruct il; auto.
destruct il.

repeat rewrite mergesort_1.
unfold merge; unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func; intuition.

simpl; f_equal; f_equal; rewrite Zdiv2_Natdiv2.
rewrite ZtoNat_Zlength.
simpl; auto.

rewrite Zlength_cons; rep_lia.

rewrite ZtoNat_Zlength.
simpl; auto.

rewrite Zlength_cons; rep_lia.
Qed.


Lemma merge_length : forall l1 , forall l2 , length (merge l1 l2 ) = Nat.add (length l1) (length l2).
Proof.
  induction l1.
  intros.
  intuition.

  induction l2.
  intuition.
    unfold merge;  unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
  destruct (a <=? a0); simpl; f_equal.

  specialize (IHl1 (a0 :: l2)). 
  unfold merge in IHl1.
  rewrite IHl1.
  intuition.

  unfold merge in IHl2.
  rewrite IHl2.
  simpl.
  intuition.
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
destruct l; lia.

rewrite <- mergesort_merge.
destruct l.
simpl; auto.
destruct l.
simpl; auto.
destruct l; simpl.
repeat rewrite mergesort_1.
rewrite merge_length; intuition.


simpl in H.
rewrite merge_length.
rewrite IHn.
rewrite IHn.
rewrite firstn_length.
rewrite skipn_length.
assert ( (Z.to_nat (Z.div2 (Zlength (z :: z0 :: z1 :: l))) <= Datatypes.length (z :: z0 :: z1 :: l))%nat ).
{ simpl.
rewrite  Zdiv2_Natdiv2.
rewrite ZtoNat_Zlength; simpl.
destruct (Datatypes.length l); try lia.
destruct n0.
simpl; try lia.
assert (G := Nat.le_div2 n0); rep_lia.
rewrite Zlength_cons; rep_lia.
}
{
  repeat  rewrite  Zdiv2_Natdiv2.
  rewrite ZtoNat_Zlength; simpl; f_equal.
  rewrite Nat.min_l.
  destruct  (Datatypes.length l); try lia.
  simpl; f_equal.
  remember (Nat.div2 n0 ).
destruct n1; try lia.
destruct n1; try lia.
simpl; repeat f_equal.


assert (Nat.lt n1 n0).
destruct n0.
simpl in *; lia.
assert (G := Nat.le_div2 n0); rep_lia.
rep_lia.

destruct (Datatypes.length l); try lia.
destruct n0.
simpl; lia.
assert (G := Nat.le_div2 n0); rep_lia.

rewrite Zlength_cons; rep_lia.
}


rewrite skipn_length; rewrite  Zdiv2_Natdiv2.
rewrite ZtoNat_Zlength; simpl.
destruct (length l); try lia.
remember (Nat.div2 n0).
destruct n1; lia.

rewrite Zlength_cons; rep_lia.

rewrite firstn_length; repeat rewrite  Zdiv2_Natdiv2.
repeat rewrite ZtoNat_Zlength.
rewrite Nat.min_l.
simpl.
destruct  (Datatypes.length l); try lia.
destruct n0.
simpl; lia.
assert (G := Nat.le_div2 n0); rep_lia.

simpl.
destruct  (Datatypes.length l); try lia.
destruct n0.
simpl; lia.
assert (G := Nat.le_div2 n0); rep_lia.

rewrite Zlength_cons; rep_lia.
Qed.

Lemma mergesort_Zlength : forall l,  Zlength (mergesort l ) = Zlength l.
Proof.
intros.
do 2 rewrite Zlength_correct.
f_equal.
apply mergesort_length.
Qed.

Lemma mergesort_permutation : forall l , Permutation l (mergesort l).
Proof. Admitted.

Definition my_mergesort_spec : ident * funspec :=
 DECLARE _my_mergesort
 WITH p: val,  sh : share, il: list Z, gv: globals
 PRE [ tptr tuint , tint ] 
    PROP ( writable_share sh;
          0 < Zlength il <= Int.max_signed;
          Forall (fun x => 0 <= x <= Int.max_unsigned) il) 
    PARAMS (p; Vint (Int.repr (Zlength il)) )
    GLOBALS(gv) 
    SEP  (data_at sh (tarray tuint (Zlength il)) (map Vint (map Int.repr il)) p;
          mem_mgr gv)
 POST [ tvoid ] 
    PROP ( ) RETURN ()
    SEP (data_at sh (tarray tuint (Zlength (mergesort il))) (map Vint (map Int.repr (mergesort il))) p;
         mem_mgr gv).

Definition memcpy_spec :=
  DECLARE _memcpy
  WITH qsh : share, psh: share, p: val, q: val,  contents: list Z
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (readable_share qsh; writable_share psh; Zlength contents <= Int.max_unsigned)
    PARAMS ( p ; q ; Vlong (Int64.repr (4 * Zlength contents)))
    SEP (data_at qsh (tarray tuint (Zlength contents)) (map Vint (map Int.repr contents)) q;
         memory_block psh (4 * Zlength contents) p)
  POST [ tptr tvoid ]
     PROP() LOCAL(temp ret_temp p)
     SEP(data_at qsh (tarray tuint (Zlength contents)) (map Vint (map Int.repr contents)) q;
         data_at psh (tarray tuint (Zlength contents)) (map Vint (map Int.repr contents)) p).

Definition Gprog : funspecs :=
  ltac:(with_library prog [
             my_mergesort_spec ; memcpy_spec
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
    rewrite Zlength_nil in H1. inv H1. 
    destruct il. {
      rewrite mergesort_Zlength.
      unfold mergesort.
      simpl.
      entailer!.
    }  {
      do 2 rewrite Zlength_cons in H1.
      assert (0 <= Zlength il ).
      apply Zlength_nonneg.
      assert (Z.succ (Z.succ (Zlength il)) >= 2). lia.
      rewrite H1 in H6. contradiction.
    }
  }
  {
    forward.
    entailer!.
  }
  forward.
  entailer!.
  destruct H5.
  inv H6.
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
    split.
    split; try rep_lia.
    apply Z.div_str_pos; rep_lia.
    {
      apply Forall_firstn; auto.
    }
 }

 remember (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)) as l1.

  assert ( H75:  Zlength l1 = Zlength il / 2 ). {
    rewrite Heql1.
    rewrite mergesort_Zlength.
    rewrite Zlength_firstn.
    lia.
  }

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
    split.
    split; try rep_lia.
    assert ( Z.div2 (Zlength il) < Zlength il). {apply div2_le2. lia. }
    rep_lia.
    {  apply Forall_skipn; auto. }
  }

  forward_call ( tarray tuint (Zlength il), gv).
  simpl; rewrite Zmax_right; rep_lia.
  
  Intro t.
  destruct ( eq_dec t nullval ).
  forward_if False.
  forward_call. inv H3. congruence.

  forward_if True.
  congruence.
  forward.
  entailer.
  Intros.
  forward.
  forward.
  forward.

  do 2 rewrite mergesort_Zlength.
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
    rewrite mergesort_Zlength.
      rewrite Zlength_solver.Zlength_firstn_to_nat. 
      rewrite H80.
      rewrite H71. auto.

      do 2 rewrite Zlength_map.
          rewrite mergesort_Zlength.
      rewrite Zlength_solver.Zlength_skipn_to_nat.       
      rewrite H80.
      rewrite Zmax_left; rep_lia.
  }
  
  remember (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)) as l2.
  assert (H76 : Zlength l2 = Zlength il - Zlength il / 2 ). {
    rewrite Heql2.
    rewrite mergesort_Zlength.
    rewrite Zlength_skipn.
    lia.
  }

  forward_loop (
     EX i, EX j, EX k,
     PROP(0 <= i <= Z.div2 (Zlength il);
          Z.div2 (Zlength il) <= j <= Zlength il;
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
                (firstn (Z.to_nat i) l1)
                (firstn (Z.to_nat (j - (Zlength il / 2))) l2 )))
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
      PROP( (i = Z.div2 (Zlength il) /\ Z.div2 (Zlength il) <= j < Zlength il) \/
            (j = Zlength il /\ 0 <= i < Z.div2 (Zlength il));
            0 <= k < Zlength il;
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
                (firstn (Z.to_nat i) l1 )
                (firstn (Z.to_nat (j - (Zlength il /2))) l2 )))
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
  sep_apply H4.
  rewrite data_at__tarray.
(*  rewrite sublist_nil. *)
  assert ((Zlength il / 2 - Zlength il / 2) = 0 ). { lia. }
  rewrite H5.
  entailer!.
  rewrite Zdiv2_div; rewrite H5; simpl; rewrite merge_nil_r; auto.
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
            temp _t'2 (Val.of_bool ((Z.ltb i (Zlength il /2) ) && (Z.ltb j (Zlength il))))
           )
     
     SEP (mem_mgr gv;
          malloc_token Ews (tarray tuint (Zlength il)) t;
               data_at Ews (tarray tuint (Zlength il))
                (map Vint (map Int.repr (merge
                (firstn (Z.to_nat i) l1)
                (firstn (Z.to_nat (j - (Zlength il /2))) l2)))
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
    destruct (zlt j (Zlength il)); lia.
  }
  
  forward.
  entailer!.
  
  {
    assert (i <? Zlength il /2 = false). {
      apply Z.ltb_ge; lia.
    }
    rewrite H19.
    simpl.
    auto.
  }
  
  forward_if   (PROP ( i < Zlength il /2 ;
                       j < Zlength il )
     LOCAL (temp _k (Vint (Int.repr k)); temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i));
     temp _t t;
     temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
     temp _arr1 p; temp _p (Vint (Int.repr (Zlength il / 2))); gvars gv; 
     temp _arr p; temp _len (Vint (Int.repr (Zlength il)));
     temp _t'2 (Val.of_bool ((i <? Zlength il / 2) && (j <? Zlength il))))
     SEP (mem_mgr gv; malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
       (map Vint
          (map Int.repr (merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Zlength il / 2)) l2))) ++
        Zrepeat (default_val tuint) (Zlength il - k)) t;
     data_at sh (tarray tuint (Zlength il))
             (map Vint (map Int.repr l1) ++ map Vint (map Int.repr l2)) p)).
  
  forward.
  entailer!.
  forward.

  assert ((i <? Zlength il / 2) = false \/  (j <? Zlength il) = false ).
  {
    apply andb_false_iff; auto.
  }
  destruct H11.
  assert (i = Zlength il /2). { lia. }
  Exists i. Exists j. Exists k. entailer!.
  rewrite H9.
  f_equal.
  rewrite  Zdiv2_div; auto.

  assert (j = Zlength il). { lia. }
  Exists i. Exists j. Exists k. entailer!.
  rewrite H9.
  f_equal.
  rewrite  Zdiv2_div; auto.


 
  abbreviate_semax; Intros.

  forward.
  entailer!.
  list_solve.

  forward.
  entailer!.
  list_solve.

 (*  分类讨论 _t'5 <= _t'6 *)

 remember ((Znth i (l1 ++ l2) )
           <=?
          (Znth j (l1 ++ l2))
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
            temp _t'2 (Val.of_bool ((i <? Zlength il / 2) && (j <? Zlength il)))
           )
     
     SEP (mem_mgr gv;
          malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
                (map Vint (map Int.repr (merge
                (firstn (Z.to_nat (i + 1)) l1 )
                (firstn (Z.to_nat (j - (Zlength il /2))) l2 )))
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
  rewrite Znth_app1.
  assert ( H60 : (Zlength il - k) =  1 + (Zlength il - (k + 1)) ). { lia. }
  rewrite H60; clear H60.
  rewrite <- (Zrepeat_app 1).
  rewrite <- cons_Zrepeat_1_app.

   remember (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)) as l1.
   remember (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)) as l2.

   assert (H66 : i < Zlength l1). {
      rewrite   Heql1.
      rewrite mergesort_Zlength.
      rewrite Zlength_firstn.
      rewrite Z.max_r; lia.
   }
   assert (H67 : Zlength l2 = Zlength il - Zlength il / 2 ). {
     rewrite Heql2.
     rewrite mergesort_Zlength.
     rewrite Zlength_skipn.
     rewrite Z.max_r; lia.
   }

  repeat rewrite Zlength_firstn.
  rewrite Z.max_r; try lia.
  rewrite Z.min_l; try lia.
  rewrite Z.max_r; try lia.
  rewrite Z.min_l; try lia.
  assert ( H40 : (k - (i + (j - Zlength il / 2))) = 0  ). { lia. }
  rewrite H40.
  rewrite upd_Znth0.
  
   
assert ( H50 :
  (merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Zlength il / 2)) l2)) ++
      Znth i l1 :: []
    =
   merge (firstn (Z.to_nat (i + 1)) l1) (firstn (Z.to_nat (j - Zlength il / 2)) l2)
  ).
{

  assert (H30 : [Znth i l1] = skipn (Z.to_nat i) (firstn (Z.to_nat (i + 1)) l1)).
  {
    rewrite <- sublist_skip; auto; try lia.
    rewrite Zlength_solver.Zlength_firstn_to_nat.
    rewrite Z.max_l; try lia.
    rewrite Z.min_l; try lia.
    rewrite (sublist_len_1 i); auto; try lia.
    rewrite Znth_firstn; auto; try lia.
    rewrite Zlength_solver.Zlength_firstn_to_nat.
    rewrite Z.max_l; try lia.
  }

  rewrite H30.
  symmetry.
   
  assert (M := merge_append_l  (firstn  (Z.to_nat (j - Zlength il / 2)) l2)  (firstn (Z.to_nat (i + 1)) l1) (Z.to_nat i) ).
  assert (H50: (firstn (Z.to_nat i) (firstn (Z.to_nat (i + 1)) l1)) = firstn (Z.to_nat i) l1 ).
  { rewrite firstn_firstn.
    rewrite Nat.min_l ; auto; try lia.
  }
  rewrite H50 in M.
  apply M.

  rewrite firstn_length.
  rewrite Nat.min_l; try lia.
  rewrite <- ZtoNat_Zlength; lia.

  rewrite firstn_length.
  rewrite Nat.min_l; try lia.

  symmetry.
  assert (G := merge_invariant_lr l1 l2 (Z.to_nat i) (Z.to_nat (j - Zlength il / 2))  (Z.to_nat (i + 1))  (Z.to_nat (j - Zlength il / 2)) ).
  apply G; auto; try lia.

  
  rewrite Zdiv2_div in H9.
  rewrite <- H9.
  f_equal; lia.
  
  apply Nat2Z.inj_le; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia.
  lia.

  apply Nat2Z.inj_le; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia.
  lia.


  rewrite Heql1; apply sorted_mergesort.
  rewrite Heql2; apply sorted_mergesort.   

  apply Nat2Z.inj_le; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia.
  lia.

  apply sorted_firstn; rewrite Heql1; apply sorted_mergesort.
  apply sorted_firstn; rewrite Heql2; apply sorted_mergesort.
}
rewrite  <- H50.
repeat rewrite map_app.

simpl; list_solve.

lia.
lia.

repeat rewrite Zlength_map.
rewrite mergesort_Zlength.
rewrite Zlength_firstn.
lia.

repeat rewrite mergesort_Zlength.
repeat rewrite Zlength_map.
repeat rewrite merge_Zlength.
repeat rewrite Zlength_firstn.
repeat rewrite mergesort_Zlength.
repeat rewrite Zlength_skipn.
repeat rewrite Zlength_Zrepeat.
repeat rewrite Zlength_firstn.
lia.

lia.

unfold both_int in H12.
unfold sem_cast_i2i in H12.
rewrite Znth_app1 in H12.
rewrite (Znth_map i) in H12.
rewrite Znth_app2 in H12.
rewrite Znth_map in H12.
simpl in H10.

rewrite Znth_app1 in Heqb.
rewrite Znth_app2 in Heqb.
repeat rewrite Zlength_map in H12.

assert (G := typed_false_of_bool _ H12).
unfold negb in G.

remember (Int.ltu (Znth (j - Zlength l1) (map Int.repr l2)) (Znth i (map Int.repr l1)) ).
destruct b; try inv G.

symmetry in Heqb0.
assert ( M := ltu_inv _ _ Heqb0).

rewrite Znth_map in M.
rewrite Znth_map in M.
rewrite Int.unsigned_repr in M.
rewrite Int.unsigned_repr in M.
lia.

apply sublist.Forall_Znth.
rewrite mergesort_Zlength.
rewrite Zlength_firstn; rep_lia.
eapply Permutation_Forall. apply mergesort_permutation.
  apply Forall_firstn; auto.

 apply sublist.Forall_Znth.
repeat rewrite mergesort_Zlength. 
rewrite Zlength_skipn.
rewrite Zlength_firstn.
rep_lia.

eapply Permutation_Forall. apply mergesort_permutation.
  apply Forall_skipn; auto.

  rewrite mergesort_Zlength.
  rewrite Zlength_firstn.
  rep_lia.

  repeat rewrite mergesort_Zlength. 
rewrite Zlength_skipn.
rewrite Zlength_firstn.
rep_lia.

rewrite <- Heqb0 in H14.
inv H14.

rep_lia.
rep_lia.
repeat rewrite Zlength_map; rep_lia.
repeat rewrite Zlength_map; rep_lia.
repeat rewrite Zlength_map; rep_lia.
repeat rewrite Zlength_map; rep_lia.

forward.
Exists (i + 1). Exists j. Exists (k + 1).
entailer!.

   remember (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)) as l1.       
   remember (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)) as l2.


   assert ( H90 : (Z.to_nat (i + 1 + (j - Z.div2 (Zlength il)))) =  Nat.add ( Z.to_nat (i + (j - Z.div2 (Zlength il))))  1%nat ).
{ lia. }
rewrite H90.

assert ( H91 :  (Z.to_nat (i + (j - Z.div2 (Zlength il)))) =  Nat.add (Z.to_nat i)  (Z.to_nat (j - Z.div2 (Zlength il))) ).
{ lia. }
rewrite H91 in H9.
symmetry in H9.

assert (G := merge_invariant _ _ _ _ H9 ).
assert (
 H92 : merge l1 l2 =
      merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Z.div2 (Zlength il))) l2) ++
      merge (skipn (Z.to_nat i) l1) (skipn (Z.to_nat (j - Z.div2 (Zlength il))) l2)
  ).
{
  apply G.
    apply Nat2Z.inj_le; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia. 
  lia. 

      apply Nat2Z.inj_le; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia. 
  lia. 

  rewrite Heql1; apply sorted_mergesort.
    rewrite Heql2; apply sorted_mergesort.
}

rewrite <- sublist.firstn_app.
rewrite H92 at 2.
rewrite skipn_app.

assert ( H93 :  (i + (j - Z.div2 (Zlength il))) = Zlength (merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Z.div2 (Zlength il))) l2)) ).
{
  rewrite merge_Zlength.
  repeat rewrite Zlength_firstn.
  lia.
}
rewrite H93 at 2.
rewrite ZtoNat_Zlength.
rewrite skipn_exact_length.
simpl.
rewrite H93.
rewrite ZtoNat_Zlength.
assert ( H94:
Nat.sub (Datatypes.length
         (merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Z.div2 (Zlength il))) l2))) 
       (Datatypes.length
         (merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Z.div2 (Zlength il))) l2))) = 0%nat
  ).
{ lia. }
rewrite H94.
rewrite skipn_O.



assert (H95 := merge_invariant_lr _ _ _ _ (Z.to_nat (i + 1)) (Z.to_nat (j - Z.div2 (Zlength il)))  H9 ).
assert (H96 :   merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Z.div2 (Zlength il))) l2) =
        firstn (Z.to_nat i + Z.to_nat (j - Z.div2 (Zlength il)))
               (merge (firstn (Z.to_nat (i + 1)) l1) (firstn (Z.to_nat (j - Z.div2 (Zlength il))) l2)) ).
{
  apply H95; try lia.
    apply Nat2Z.inj_le; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia. 
  lia. 

      apply Nat2Z.inj_le; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia. 
  lia. 

    rewrite Heql1; apply sorted_mergesort.
    rewrite Heql2; apply sorted_mergesort.
}

assert ( H97 : (firstn (Z.to_nat i) l1) = firstn (Z.to_nat i) (firstn (Z.to_nat (i + 1)) l1) ).
{
  rewrite firstn_firstn.
  rewrite Nat.min_l; auto; lia.
}
rewrite H97 in H96.
assert ( H98:
         (firstn (Z.to_nat (j - Z.div2 (Zlength il))) l2) =
       firstn (Z.to_nat (j - Z.div2 (Zlength il))) (firstn (Z.to_nat (j - Z.div2 (Zlength il))) l2)
  ).
{
  rewrite firstn_firstn.
  rewrite Nat.min_l; auto; lia.
}
rewrite H98 in H96 at 1.
assert (H99 := merge_invariant _ _ _ _ H96).
repeat rewrite firstn_firstn in H99.
rewrite Nat.min_l in H99; try lia.
rewrite Nat.min_l in H99; try lia.
rewrite H99; f_equal.
rewrite H9; f_equal.

rewrite firstn_length.
rewrite Nat.min_l; auto.

rewrite merge_length.
repeat rewrite <- ZtoNat_Zlength.
rep_lia.

repeat rewrite skipn_firstn.
assert ( H60 :  Nat.sub (Z.to_nat (j - Z.div2 (Zlength il))) (Z.to_nat (j - Z.div2 (Zlength il))) = 0%nat ).
{ lia. }
rewrite H60.
rewrite firstn_O.
rewrite merge_nil_r.
assert (H61 :  Nat.sub (Z.to_nat (i + 1)) (Z.to_nat i) = 1%nat ).
{ lia. }
rewrite H61.

rewrite sublist.skipn_cons.
rewrite (sublist.skipn_cons (Z.to_nat (j - Z.div2 (Zlength il)))).
unfold merge; unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
remember ( Znth (Z.of_nat (Z.to_nat i)) l1 <=? Znth (Z.of_nat (Z.to_nat (j - Z.div2 (Zlength il)))) l2 ).
destruct b; auto.
rewrite Znth_app1 in Heqb; try lia.
rewrite Znth_app2 in Heqb; try lia.
repeat rewrite ZifyInst.of_nat_to_nat_eq in Heqb0.
rewrite Z.max_r in Heqb0; try lia.
rewrite Z.max_r in Heqb0; try lia.
rewrite H75 in Heqb.
rewrite Zdiv2_div in Heqb0.
lia.


  apply Nat2Z.inj_lt; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia. 
  lia. 

      apply Nat2Z.inj_lt; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia. 
  lia. 

  rewrite firstn_length.
  rewrite Nat.min_l; try lia.

  rewrite <- ZtoNat_Zlength.
   apply Nat2Z.inj_le; rewrite Z2Nat_id'.
   rewrite Z.max_r; try lia.
   rewrite firstn_length.
   rewrite Nat.min_l; try lia.

    rewrite <- ZtoNat_Zlength.
    rep_lia.

    apply sorted_firstn; auto.
    rewrite Heql1; apply sorted_mergesort.
    apply sorted_firstn; auto.
    rewrite Heql2; apply sorted_mergesort.

    (* first branch finish *)

    (* second branch start *)



   assert ( H50 :
  (merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Zlength il / 2)) l2)) ++
      Znth  (j - Zlength il / 2) l2 :: []
    =
   merge (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Zlength il / 2 + 1)) l2)
  ).
{

  assert (H30 : [Znth  (j - Zlength il / 2)  l2] = skipn (Z.to_nat  (j - Zlength il / 2) ) (firstn (Z.to_nat ( j - Zlength il / 2 + 1)) l2)).
  {
    rewrite <- sublist_skip; auto; try lia.
    rewrite Zlength_solver.Zlength_firstn_to_nat.
    rewrite Z.max_l; try lia.
    rewrite Z.min_l; try lia.
    rewrite (sublist_len_1 ); auto; try lia.
    rewrite Znth_firstn; auto; try lia.
    rewrite Zlength_solver.Zlength_firstn_to_nat.
    rewrite Z.max_l; try lia.
  }

  rewrite H30.
  symmetry.
   
  assert (M := merge_append_r  (firstn (Z.to_nat i) l1) (firstn (Z.to_nat (j - Zlength il / 2 + 1)) l2) (Z.to_nat (j - Zlength il / 2)) ).
  assert (H50: (firstn (Z.to_nat (j - Zlength il /2)) (firstn (Z.to_nat (j - Zlength il / 2 + 1)) l2)) = firstn (Z.to_nat (j - Zlength il / 2)) l2 ).
  { rewrite firstn_firstn.
    rewrite Nat.min_l ; auto; try lia.
  }
  rewrite H50 in M.
  apply M.


  symmetry in H9.
  assert ( H40 : 
           Z.to_nat (i + (j - Z.div2 (Zlength il))) =
         Nat.add   (Z.to_nat i)  (Z.to_nat (j - Z.div2 (Zlength il)))
    ). { lia. }
  rewrite H40 in H9.
  assert (G := merge_invariant_lr _ _ _ _ (Z.to_nat i) (Z.to_nat (j - Zlength il / 2 + 1)) H9 ).
  symmetry.
   rewrite Zdiv2_div in G.
  rewrite G; f_equal; try lia.
  
  rewrite firstn_length.
  rewrite Nat.min_l; try lia.
  rewrite <- ZtoNat_Zlength; lia.


  apply Nat2Z.inj_le; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia.
  lia.

  apply Nat2Z.inj_le; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct. lia.
  lia.


  rewrite Heql1; apply sorted_mergesort.
  rewrite Heql2; apply sorted_mergesort.   

  apply Nat2Z.inj_le; rewrite Z2Nat_id'.
  rewrite Z.max_r.
  rewrite <- Zlength_correct.
  rewrite Zlength_firstn.
  lia.
  lia.

  apply sorted_firstn; rewrite Heql2; apply sorted_mergesort.
    apply sorted_firstn; rewrite Heql1; apply sorted_mergesort.
}

    

  forward_if (
     PROP ( )
     LOCAL (temp _k (Vint (Int.repr k));
            temp _j (Vint (Int.repr (j + 1)));
            temp _i (Vint (Int.repr i));
            temp _t t;
            temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
            temp _arr1 p;
            temp _p (Vint (Int.repr (Zlength il / 2)));
            gvars gv; 
            temp _arr p;
            temp _len (Vint (Int.repr (Zlength il)));
            temp _t'2 (Val.of_bool ((i <? Zlength il / 2) && (j <? Zlength il)))
           )
     
     SEP (mem_mgr gv;
          malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
                (map Vint (map Int.repr (merge
                (firstn (Z.to_nat i) l1 )
                (firstn (Z.to_nat (j - (Zlength il /2)) + 1) l2 )))
                ++  Zrepeat  (default_val tuint) (Zlength il - (k + 1))) t;
      data_at sh (tarray tuint (Zlength il))
          ((map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)))) ++
           (map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))))
              p
         )
    ).


unfold both_int in H12.       
unfold sem_cast_i2i in H12.    
rewrite Znth_app1 in H12.                                                                                                                                      
rewrite (Znth_map i) in H12. 
rewrite Znth_app2 in H12.   
rewrite Znth_map in H12.
repeat rewrite Zlength_map in H12.
simpl in H12.
assert (G := typed_true_of_bool _ H12).
unfold negb in G.
remember (Int.ltu (Znth (j - Zlength l1) (map Int.repr l2)) (Znth i (map Int.repr l1))) . 
destruct b; try inv G.
symmetry in Heqb0.
assert ( M := ltu_false_inv _ _ Heqb0).
rewrite Znth_map in M.
rewrite Znth_map in M.
rewrite Int.unsigned_repr in M.
rewrite Int.unsigned_repr in M.
list_solve.

apply sublist.Forall_Znth. 
rewrite mergesort_Zlength. 
rewrite Zlength_firstn; rep_lia.
eapply Permutation_Forall. apply mergesort_permutation.
apply Forall_firstn; auto.


apply sublist.Forall_Znth. 
rewrite mergesort_Zlength. 
rewrite Zlength_firstn; rep_lia.
eapply Permutation_Forall. apply mergesort_permutation.
apply Forall_skipn; auto.

rewrite mergesort_Zlength; rewrite Zlength_firstn; lia.
rewrite mergesort_Zlength; rewrite Zlength_firstn; lia.

repeat rewrite Zlength_map; lia.
repeat rewrite Zlength_map; lia.
repeat rewrite Zlength_map; lia.
repeat rewrite Zlength_map; lia.

forward; forward; forward. entailer!.

apply derives_refl'; f_equal.
{
  rewrite upd_Znth_app2; try lia.
  rewrite Znth_app2; try lia.
  repeat  rewrite Zlength_map; try lia.
  repeat rewrite merge_Zlength; try lia.
  repeat rewrite Zlength_firstn; try lia.
  rewrite Z.max_r.
  rewrite Z.max_r.
  rewrite Z.min_l.
  rewrite Z.min_l.
  assert ( H59: (k - (i + (j - Zlength il / 2))) = 0 ). { lia. }
  rewrite H59.

    assert ( H60 : (Zlength il - k) =  1 + (Zlength il - (k + 1)) ). { lia. }
  rewrite H60; clear H60. 
    rewrite <- (Zrepeat_app 1).
 rewrite <- cons_Zrepeat_1_app.    
 rewrite upd_Znth0.


assert (H51: Nat.add (Z.to_nat (j - Zlength il / 2)) 1 = (Z.to_nat (j - Zlength il / 2 + 1))).
{ lia. }
rewrite H51.
rewrite  <- H50.
repeat rewrite map_app.
simpl; list_solve.
lia.
lia.
lia.
lia.
lia.
lia.

repeat rewrite Zlength_map; lia.


repeat rewrite Zlength_map.
repeat rewrite merge_Zlength.
repeat rewrite Zlength_firstn.
repeat rewrite Zlength_Zrepeat.
repeat rewrite mergesort_Zlength.
repeat rewrite Zlength_firstn.
repeat rewrite Zlength_skipn.
lia.
lia.
}

forward.

Exists i. Exists (j + 1). Exists (k + 1).
entailer!.
assert ( H51 : (Z.to_nat (j + 1 - Z.div2 (Zlength il))) =  (Z.to_nat (j - Zlength il / 2 + 1)) ).
{ lia. }
rewrite H51.
rewrite <- H50.
symmetry in H9.
assert ( H52 : (Z.to_nat (i + (j - Z.div2 (Zlength il)))) = Nat.add (Z.to_nat i) (Z.to_nat (j - Z.div2 (Zlength il)))). { lia. }
rewrite H52 in H9.
assert (G := merge_invariant _ _ _ _ H9).
assert (
      merge (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))
        (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)) =
      merge (firstn (Z.to_nat i) (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)))
        (firstn (Z.to_nat (j - Z.div2 (Zlength il)))
           (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))) ++
      merge (skipn (Z.to_nat i) (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)))
        (skipn (Z.to_nat (j - Z.div2 (Zlength il)))
           (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))
  ).
apply G.

{
rewrite mergesort_length.
rewrite firstn_length.
rewrite Nat.min_l; try lia.
   rewrite Zdiv2_div.
rewrite <- ZtoNat_Zlength.
rep_lia.
}


{
rewrite mergesort_length.
rewrite skipn_length.
   rewrite Zdiv2_div.
rewrite <- ZtoNat_Zlength.
rep_lia.
}

apply sorted_mergesort.
apply sorted_mergesort.

{
rewrite H21.
assert ( H53 : (Z.to_nat (i + (j + 1 - Z.div2 (Zlength il)))) = Nat.add (Z.to_nat (i + (j  - Z.div2 (Zlength il)))) 1 ). { lia. }
rewrite H53.
rewrite firstn_app.
f_equal.
   rewrite Zdiv2_div.
apply firstn_same.
rewrite merge_length.
repeat rewrite <- ZtoNat_Zlength.
repeat rewrite Zlength_firstn.
rep_lia.

rewrite merge_length.
repeat rewrite <- ZtoNat_Zlength.
repeat rewrite mergesort_Zlength.
repeat rewrite Zlength_firstn.
repeat rewrite mergesort_Zlength.
repeat rewrite Zlength_skipn.
repeat rewrite Zlength_firstn.
repeat rewrite Z.max_r; try lia.
repeat rewrite Z.min_l; try lia.
   rewrite Zdiv2_div.

   assert ( H54:  Nat.sub ( Nat.add (Z.to_nat (i + (j - Zlength il / 2)))  1%nat ) (Z.to_nat i + Z.to_nat (j - Zlength il / 2)) = 1%nat  ).
{ lia. }
rewrite H54.

   remember (mergesort (firstn (Z.to_nat ((Zlength il) / 2)) il)) as l1.                                                                                                                   
   remember (mergesort (skipn (Z.to_nat ((Zlength il) / 2)) il)) as l2.
  

rewrite sublist.skipn_cons.
rewrite (sublist.skipn_cons (Z.to_nat (j - (Zlength il) /2 ))).


unfold merge; unfold merge_func;
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
remember ( Znth (Z.of_nat (Z.to_nat i)) l1 <=? Znth (Z.of_nat (Z.to_nat (j -  (Zlength il) / 2))) l2 ).
destruct b.
{ rewrite Znth_app1 in Heqb; try lia. 
    rewrite Znth_app2 in Heqb; try lia.
    rewrite Zdiv2_div in Heqb.
    rewrite <- Heql1 in Heqb.
rewrite <- Heql2 in Heqb.
repeat rewrite ZifyInst.of_nat_to_nat_eq in Heqb0.
rewrite Z.max_r in Heqb0; try lia. 
rewrite Z.max_r in Heqb0; try lia. 
    rewrite Zdiv2_div in H75.
    rewrite <- Heql1 in H75.
    rewrite H75 in Heqb.
    lia.
    }
{ f_equal; f_equal; intuition. }


   assert (H66 : i < Zlength l1). {
      rewrite   Heql1.
      rewrite mergesort_Zlength.
      rewrite Zlength_firstn.
      rewrite Z.max_r; lia.
   }
   assert (H67 : Zlength l2 = Zlength il - Zlength il / 2 ). {
     rewrite Heql2.
     rewrite mergesort_Zlength.
     rewrite Zlength_skipn.
     rewrite Z.max_r; lia.
   }
 
rewrite <- ZtoNat_Zlength.
 apply Nat2Z.inj_lt; rewrite Z2Nat_id'.
 rewrite Z.max_r; try lia.

   assert (H66 : i < Zlength l1). {
      rewrite   Heql1.
      rewrite mergesort_Zlength.
      rewrite Zlength_firstn.
      rewrite Z.max_r; lia.
   }
   assert (H67 : Zlength l2 = Zlength il - Zlength il / 2 ). {
     rewrite Heql2.
     rewrite mergesort_Zlength.
     rewrite Zlength_skipn.
     rewrite Z.max_r; lia.
   }
   rewrite <- ZtoNat_Zlength.
 apply Nat2Z.inj_lt; rewrite Z2Nat_id'.
 rewrite Z.max_r; try lia.

}

apply derives_refl'; f_equal; f_equal; f_equal; f_equal; f_equal; f_equal; lia.

Intro i; Intro j; Intro k; Intros.


  destruct H5; destruct H5; subst.

  assert (j = k). { lia. }
  subst k.
  clear H7.
  
  forward_loop     (PROP ( )
     LOCAL (temp _k (Vint (Int.repr j)); temp _j (Vint (Int.repr j));
     temp _i (Vint (Int.repr (Z.div2 (Zlength il)))); temp _t t;
     temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
     temp _arr1 p; temp _p (Vint (Int.repr (Zlength il / 2))); gvars gv; 
     temp _arr p; temp _len (Vint (Int.repr (Zlength il))))
     SEP (mem_mgr gv; malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
       (map Vint
          (map Int.repr
             (merge
                (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))
                (firstn (Z.to_nat (j - Zlength il / 2))
                   (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))) ++
        Zrepeat (default_val tuint) (Zlength il - j)) t;
     data_at sh (tarray tuint (Zlength il))
       (map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))) ++
            map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))) p))
   break:     (PROP ( )
     LOCAL (temp _k (Vint (Int.repr j)); temp _j (Vint (Int.repr j));
     temp _i (Vint (Int.repr (Z.div2 (Zlength il)))); temp _t t;
     temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
     temp _arr1 p; temp _p (Vint (Int.repr (Zlength il / 2))); gvars gv; 
     temp _arr p; temp _len (Vint (Int.repr (Zlength il))))
     SEP (mem_mgr gv; malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
       (map Vint
          (map Int.repr
             (merge
                (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))
                (firstn (Z.to_nat (j - Zlength il / 2))
                   (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))) ++
        Zrepeat (default_val tuint) (Zlength il - j)) t;
     data_at sh (tarray tuint (Zlength il))
       (map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))) ++
        map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))) p)).
   

  entailer!.
  {
    apply derives_refl'; f_equal; f_equal; f_equal; f_equal; f_equal.
    apply Zfirstn_same;
      rewrite mergesort_Zlength.    
  rewrite Zlength_firstn;  lia.
  }
  
  forward_if False.
  lia.
  forward.
    entailer!.

   remember (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)) as l1.
   remember (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)) as l2.                                                                                                                    
    forward_loop  (EX j ,
                    PROP (Z.div2 (Zlength il) <= j <= Zlength il;
          firstn (Z.to_nat j) (merge l1 l2) = merge l1 (firstn (Z.to_nat (j - Zlength il / 2)) l2)
                          )
                    LOCAL (temp _k (Vint (Int.repr j));
                           temp _j (Vint (Int.repr j));
     temp _i (Vint (Int.repr (Z.div2 (Zlength il)))); temp _t t;
     temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
     temp _arr1 p; temp _p (Vint (Int.repr (Zlength il / 2))); gvars gv; 
     temp _arr p; temp _len (Vint (Int.repr (Zlength il))))
     SEP (mem_mgr gv; malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
       (map Vint
          (map Int.repr
             (merge
                (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))
                (firstn (Z.to_nat (j - Zlength il / 2))
                   (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))) ++
        Zrepeat (default_val tuint) (Zlength il - j)) t;
     data_at sh (tarray tuint (Zlength il))
       (map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))) ++
            map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))) p))

    break:  ( PROP ( )
                               LOCAL (temp _k (Vint (Int.repr (Zlength il)));
                                      temp _j (Vint (Int.repr (Zlength il)));
     temp _i (Vint (Int.repr (Z.div2 (Zlength il)))); temp _t t;
     temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
     temp _arr1 p; temp _p (Vint (Int.repr (Zlength il / 2))); gvars gv; 
     temp _arr p; temp _len (Vint (Int.repr (Zlength il))))
     SEP (mem_mgr gv; malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
       (map Vint
          (map Int.repr
             (merge
                (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))
                (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))) t;
     data_at sh (tarray tuint (Zlength il))
       (map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))) ++
            map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))) p)).
  
  Exists j.
  entailer!.

  assert ( H44 : (Z.to_nat (Z.div2 (Zlength il) + (j - Z.div2 (Zlength il)))) = Z.to_nat j ).
  { lia. }
  rewrite H44 in H8.
  rewrite H8.
  f_equal.
  apply firstn_same.
  rewrite mergesort_length.
  rewrite firstn_length.
  rewrite Nat.min_l; try lia.
  rewrite <- ZtoNat_Zlength.
  rep_lia.
  
  Intro j0; Intros.
  forward_if (j0 < Zlength il).
  forward.
  entailer!.
    assert (j0 = Zlength il). { lia. }
  subst.
  forward.
  entailer!.

  apply derives_refl'; repeat f_equal.
 rewrite Z.sub_diag.
rewrite Zrepeat_0.
rewrite app_nil_r.
repeat f_equal.

apply Zfirstn_same; rewrite mergesort_Zlength.
rewrite Zlength_skipn; rep_lia.

forward.
entailer!.
entailer!.
list_solve.

forward.
forward.
forward.
Exists (j0 + 1).




     symmetry in H7.
     assert (H46 := merge_invariant_lr l1 l2  (Z.to_nat (Zlength il / 2)) (Z.to_nat (j0 - (Zlength il / 2))) (Z.to_nat (Zlength il / 2)) (Z.to_nat (j0 - (Zlength il / 2) + 1))  ).
     rewrite (firstn_same _ (Z.to_nat (Zlength il / 2))) in H46.
     assert ( H51 : Nat.add (Z.to_nat (Zlength il / 2)) (Z.to_nat (j0 - Zlength il / 2))  = Z.to_nat j0 ).
     { lia.  }
     rewrite H51 in H46.
       specialize (H46 H7 ).   

       assert (H47 := merge_invariant l1  (firstn (Z.to_nat (j0 + 1 - Zlength il / 2)) l2) (length l1)  (Z.to_nat (j0 - Zlength il / 2)) ).
             rewrite (firstn_same _ (length l1)) in H47.
      rewrite skipn_all in H47.
      rewrite merge_nil_l in H47.
      rewrite firstn_firstn in H47.
      rewrite Nat.min_l in H47.
      rewrite <- ZtoNat_Zlength in H47.
      assert ( H48 : Nat.add (Z.to_nat (Zlength l1)) (Z.to_nat (j0 - Zlength il / 2)) = Z.to_nat j0 ).
      { lia. }
      rewrite H48 in H47; auto; try lia.

      assert ( H65:  merge l1 (firstn (Z.to_nat (j0 + 1 - Zlength il / 2)) l2) =
        merge l1 (firstn (Z.to_nat (j0 - Zlength il / 2)) l2) ++
        skipn (Z.to_nat (j0 - Zlength il / 2)) (firstn (Z.to_nat (j0 + 1 - Zlength il / 2)) l2) ).
      apply H47; try lia.
      rewrite H46; try lia.
      f_equal; f_equal; f_equal; lia.

      rewrite <- ZtoNat_Zlength; rep_lia.
      rewrite <- ZtoNat_Zlength; rep_lia.
      rewrite Heql1; apply sorted_mergesort.
      rewrite Heql2; apply sorted_mergesort.
   rewrite <- ZtoNat_Zlength; rewrite Zlength_firstn; rep_lia.
           rewrite Heql1; apply sorted_mergesort.
           apply sorted_firstn;     rewrite Heql2; apply sorted_mergesort. 

          entailer!.

           rewrite Zdiv2_div in *.
             remember (mergesort (firstn (Z.to_nat ((Zlength il) / 2)) il)) as l1.                                                                                                                      
             remember (mergesort (skipn (Z.to_nat ((Zlength il) / 2)) il)) as l2.
             
   assert (G := merge_invariant l1 l2 (length l1) (Z.to_nat (j0 - (Zlength il / 2 )))).
      rewrite (firstn_same _ (length l1)) in G.
      rewrite skipn_all in G.
      rewrite merge_nil_l in G.
      rewrite G.


         
      rewrite firstn_app2.
      rewrite merge_length.
      rewrite firstn_length.
      rewrite <- ZtoNat_Zlength.
      rewrite Nat.min_l.

      


          
      rewrite H47; f_equal.     
      rewrite skipn_firstn; f_equal; lia.
      rewrite H46; f_equal; f_equal; f_equal; f_equal; try lia.
      
        rewrite <- ZtoNat_Zlength; rep_lia.
  rewrite <- ZtoNat_Zlength; rep_lia.
      
      rewrite Heql1; apply sorted_mergesort.
        rewrite Heql2; apply sorted_mergesort.
lia. 
rewrite firstn_length;   rewrite <- ZtoNat_Zlength; rep_lia.
      rewrite Heql1; apply sorted_mergesort.
apply sorted_firstn;     rewrite Heql2; apply sorted_mergesort.
        rewrite <- ZtoNat_Zlength; rep_lia.
rewrite merge_length;   rewrite <- ZtoNat_Zlength; rewrite firstn_length; rep_lia.


rewrite H7; f_equal;  rewrite <- ZtoNat_Zlength; rep_lia.
   lia.
   rewrite <- ZtoNat_Zlength; rep_lia.
   rewrite Heql1; apply sorted_mergesort.
   rewrite Heql2; apply sorted_mergesort.
   lia.



   
apply derives_refl'; f_equal.



             remember (mergesort (firstn (Z.to_nat ((Zlength il) / 2)) il)) as l1.                                                                                                                      
             remember (mergesort (skipn (Z.to_nat ((Zlength il) / 2)) il)) as l2.
             
             assert ( H78 :  Zlength l2 = Zlength il -Zlength il / 2). {
  rewrite Heql2.
  rewrite mergesort_Zlength.
  rewrite Zlength_skipn.
  rep_lia.
}
rewrite H65.


rewrite upd_Znth_app2.
repeat rewrite Zlength_map.
repeat rewrite merge_Zlength.
rewrite Zlength_firstn.
repeat rewrite mergesort_Zlength.
rewrite Zlength_firstn.
rewrite Zlength_skipn.
assert (
 H57 :    ( j0 -
     (Z.min (Z.max 0 (Z.div2 (Zlength il))) (Zlength il) +
      Z.min (Z.max 0 (j0 - Zlength il / 2)) (Z.max 0 (Zlength il - Z.max 0 (Z.div2 (Zlength il)))))) = 0
  ). { lia. }
rewrite H57.
rewrite Znth_app2.
assert ( H58 : Zlength il - j0 = 1 + (Zlength il - (j0 + 1)) ). { lia. }
rewrite H58.
  rewrite <- (Zrepeat_app 1).                                                                                                                                                                 
  rewrite <- cons_Zrepeat_1_app.
  rewrite upd_Znth0.

  repeat rewrite Zlength_map.
repeat rewrite mergesort_Zlength.
rewrite Zlength_firstn.
rewrite skipn_firstn.
assert ( H59 : Nat.sub (Z.to_nat (j0 + 1 - Zlength il / 2))  (Z.to_nat (j0 - Zlength il / 2)) = 1%nat ). { lia. }
rewrite H59.

rewrite Zdiv2_div.
rewrite <- Heql1.   
rewrite <- Heql2.


rewrite sublist.skipn_cons.
simpl.
repeat rewrite map_app.
rewrite <- app_assoc.

f_equal; simpl; f_equal; repeat rewrite Znth_map; repeat f_equal.
lia.

rep_lia.
rewrite Zlength_map; rep_lia.

rewrite <- ZtoNat_Zlength; rep_lia.
lia.
rep_lia.
repeat rewrite Zlength_map; rewrite mergesort_Zlength; rewrite Zlength_firstn; rep_lia.
repeat rewrite Zlength_map; rewrite merge_Zlength; repeat rewrite mergesort_Zlength; repeat rewrite Zlength_firstn;  repeat rewrite mergesort_Zlength; rewrite Zlength_skipn; rep_lia.
rep_lia.
lia.
rewrite <- ZtoNat_Zlength; rep_lia.


forward_call (Ews , sh , p, t,
 (merge (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))
                (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))
             ).

entailer!.

{
simpl; do 5 f_equal.
rewrite merge_Zlength.
repeat rewrite mergesort_Zlength.
rewrite Zlength_firstn.
rewrite Zlength_skipn.
rep_lia.
}

entailer!.
rewrite merge_Zlength.
repeat rewrite mergesort_Zlength.
rewrite Zlength_firstn.
rewrite Zlength_skipn.
assert ( H88 :  (Z.min (Z.max 0 (Z.div2 (Zlength il))) (Zlength il) +
            Z.max 0 (Zlength il - Z.max 0 (Z.div2 (Zlength il))))
               = Zlength il ). { lia. } 
rewrite H88.
entailer!.
sep_apply data_at_memory_block.
simpl.
rewrite Z.max_r.
entailer!.
lia.

rewrite merge_Zlength.
repeat rewrite mergesort_Zlength.
rewrite Zlength_firstn.
rewrite Zlength_skipn.
rep_lia.

forward_call (tarray tuint (Zlength il), t , gv).
destruct ( eq_dec t nullval ); try contradiction; try entailer!.

sep_apply data_at_data_at_.
entailer!.
assert ( H77 : (Zlength
          (merge (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))
             (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il)))) = Zlength il ).
{
rewrite merge_Zlength.
repeat rewrite mergesort_Zlength.
rewrite Zlength_firstn.
rewrite Zlength_skipn.
rep_lia.
}

rewrite H77; entailer!.
entailer!.

apply derives_refl'.
rewrite mergesort_Zlength.
rewrite mergesort_merge; auto.

(* another branch *)
rewrite Zdiv2_div in *.
assert ( k = i + Zlength il - Zlength il / 2 ). { lia. }
subst k.
clear H7.

assert ( H72 : (Z.to_nat (Zlength il - Zlength il / 2) >=
  Datatypes.length (mergesort (skipn (Z.to_nat (Zlength il / 2)) il)))%nat ).
{
  rewrite <- ZtoNat_Zlength; rep_lia.
}

rewrite (firstn_same  _ (Z.to_nat (Zlength il - Zlength il / 2))) in *; auto.
assert ( H37: (Zlength il - (i + Zlength il - Zlength il / 2)) = Zlength il / 2 - i ).
{ lia. }
rewrite H37.

   remember (mergesort (firstn (Z.to_nat ((Zlength il) / 2)) il)) as l1.
   remember (mergesort (skipn (Z.to_nat ((Zlength il) / 2)) il)) as l2.


   forward_loop  (EX i , PROP (0 <= i <= Zlength il /2;
       firstn (Z.to_nat (i + Zlength il - Zlength il / 2)) (merge l1 l2) = merge (firstn (Z.to_nat i) l1) l2
                              )
     LOCAL (temp _k (Vint (Int.repr (i + Zlength il - Zlength il / 2)));
            temp _j (Vint (Int.repr (Zlength il)));
            temp _i (Vint (Int.repr i)); 
            temp _t t;
            temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
     temp _arr1 p; temp _p (Vint (Int.repr (Zlength il / 2))); gvars gv; 
     temp _arr p; temp _len (Vint (Int.repr (Zlength il))))
     SEP (mem_mgr gv; malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il))
       (map Vint (map Int.repr (merge (firstn (Z.to_nat i) l1) l2) ) ++
        Zrepeat (default_val tuint) (Zlength il / 2 - i)) t;
     data_at sh (tarray tuint (Zlength il))
             (map Vint (map Int.repr l1) ++ map Vint (map Int.repr l2)) p))

   break:  (PROP ( )
     LOCAL (temp _k (Vint (Int.repr (Zlength il)));
     temp _j (Vint (Int.repr (Zlength il))); temp _i (Vint (Int.repr (Zlength il / 2))); 
     temp _t t;
     temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
     temp _arr1 p; temp _p (Vint (Int.repr (Zlength il / 2))); gvars gv; 
     temp _arr p; temp _len (Vint (Int.repr (Zlength il))))
     SEP (mem_mgr gv; malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il)) (map Vint (map Int.repr (mergesort il))) t;
     data_at sh (tarray tuint (Zlength il))
       (map Vint (map Int.repr l1) ++ map Vint (map Int.repr l2)) p)).

   Exists i; entailer!.

  rewrite <- H8; f_equal; lia.
  clear H8.

  Intro i0.
  forward_if (i0 < Zlength il / 2).
  forward.
  entailer!.
  forward.
  assert (i0 = Zlength il /2). { lia. }
  subst.
  entailer!.
  f_equal; f_equal; lia.
  entailer!.
  apply derives_refl'; f_equal.
  assert ( H46 : (Zlength il / 2 - Zlength il / 2) = 0 ). { lia. }
  rewrite H46; rewrite Zrepeat_0; rewrite app_nil_r; f_equal; f_equal.
  rewrite firstn_same; auto.
  rewrite <- Zdiv2_div; rewrite mergesort_merge;  auto.
  rewrite <- ZtoNat_Zlength; rep_lia.

   abbreviate_semax.
   Intros.
   forward.
   entailer!.
   list_solve.
   forward; forward; forward.

       
  assert (H49 : merge l1 l2 = merge (firstn (Z.to_nat i0) l1) l2 ++ skipn (Z.to_nat i0) l1 ).
{
  assert (H45 :=  merge_invariant l1 l2 (Z.to_nat i0) (Z.to_nat (Zlength il - Zlength il / 2)) ).
  rewrite (firstn_same _  (Z.to_nat (Zlength il - Zlength il / 2))) in H45.
  rewrite (skipn_short (Z.to_nat (Zlength il - Zlength il / 2))) in H45.
  rewrite merge_nil_r in H45.
  apply H45; try lia.
  rewrite <- H8; f_equal; lia.
  rewrite <- ZtoNat_Zlength; rep_lia.
  rewrite <- ZtoNat_Zlength; rep_lia.
  rewrite Heql1 ; apply sorted_mergesort.
  rewrite Heql2 ; apply sorted_mergesort.
  rewrite <- ZtoNat_Zlength; rep_lia.
  rewrite <- ZtoNat_Zlength; rep_lia.
}


       
assert (  H48 :  merge (firstn (Z.to_nat i0) l1) l2 =
firstn (Z.to_nat i0 + Z.to_nat (Zlength il - Zlength il / 2))
       (merge (firstn (Z.to_nat (i0 + 1)) l1) l2) ).
{
  symmetry in H8.
  assert (H30 := merge_invariant_lr l1 l2 (Z.to_nat i0) (Z.to_nat (Zlength il - Zlength il / 2))  (Z.to_nat (i0 + 1))  (Z.to_nat (Zlength il - Zlength il / 2)) ).
  rewrite (firstn_same _  (Z.to_nat (Zlength il - Zlength il / 2)) ) in H30.

  apply H30; try lia.
  rewrite H8; f_equal; lia.
  rewrite <- ZtoNat_Zlength; rep_lia.
  rewrite <- ZtoNat_Zlength; rep_lia.
  rewrite Heql1 ; apply sorted_mergesort.
  rewrite Heql2 ; apply sorted_mergesort.
  rewrite <- ZtoNat_Zlength; rep_lia.
}


assert ( H46: 
   merge (firstn (Z.to_nat (i0 + 1)) l1) l2 =
    merge (firstn (Z.to_nat i0) l1) l2 ++
    skipn (Z.to_nat i0) (firstn (Z.to_nat (i0 + 1)) l1)).
{
  assert (H47 := merge_invariant  (firstn (Z.to_nat (i0 + 1)) l1) l2  (Z.to_nat i0) (Z.to_nat (Zlength il - Zlength il / 2)) ).

  repeat rewrite firstn_firstn in H47.
  rewrite Nat.min_l in H47; try lia.
  rewrite (skipn_short (Z.to_nat (Zlength il - Zlength il / 2))) in H47.
  rewrite merge_nil_r in H47.
  rewrite (firstn_same _ (Z.to_nat (Zlength il - Zlength il / 2))) in H47.


  apply H47; auto; try lia.
  rewrite <- ZtoNat_Zlength;
  rewrite Zlength_firstn;
  rep_lia.
  rewrite <- ZtoNat_Zlength; rep_lia.
  apply sorted_firstn; 
  rewrite Heql1 ; apply sorted_mergesort.
  rewrite Heql2 ; apply sorted_mergesort.
  rewrite <- ZtoNat_Zlength; rep_lia.
  rewrite <- ZtoNat_Zlength; rep_lia.
}
rewrite skipn_firstn_comm in H46.
assert ( H94 : Nat.sub (Z.to_nat (i0 + 1))  (Z.to_nat i0) = 1%nat ).
{ lia. }
rewrite H94 in H46.


Exists (i0 +1); entailer!.
split.
rewrite H46.
rewrite H49.


rewrite firstn_app2.
f_equal; f_equal;
rewrite <- ZtoNat_Zlength; rewrite merge_Zlength; rewrite Zlength_firstn; 
  rep_lia.

rewrite <- ZtoNat_Zlength; rewrite merge_Zlength; rewrite Zlength_firstn; 
  rep_lia.

f_equal; f_equal; lia.

apply derives_refl'; f_equal.

rewrite upd_Znth_app2.
rewrite Znth_app1.
repeat rewrite Zlength_map;  rewrite merge_Zlength; rewrite Zlength_firstn;
  repeat rewrite mergesort_Zlength;  rewrite Zlength_firstn; rewrite Zlength_skipn.

assert ( H93 :    (i0 + Zlength il - Zlength il / 2 -
     (Z.min (Z.max 0 i0) (Z.min (Z.max 0 (Zlength il / 2)) (Zlength il)) +
      Z.max 0 (Zlength il - Z.max 0 (Zlength il / 2)))) = 0     ).
{ lia. }
rewrite H93.
assert ( H92 : Zlength il / 2 - i0 = 1 +  (Zlength il / 2 - (i0 + 1))  ).
{ lia. }
rewrite H92.

rewrite <- Zrepeat_app.
rewrite upd_Znth_app1; try lia.
simpl.

rewrite H46.
repeat rewrite map_app.

rewrite (sublist.skipn_cons (Z.to_nat i0)).
simpl.
rewrite <- app_assoc.     
list_solve.

rewrite <- ZtoNat_Zlength;   repeat rewrite mergesort_Zlength;  rewrite Zlength_firstn; rep_lia.
rewrite Zlength_Zrepeat; lia.
lia.
rep_lia.
repeat rewrite Zlength_map; rewrite mergesort_Zlength; rewrite Zlength_firstn; rep_lia.
repeat rewrite Zlength_map; rewrite merge_Zlength; rewrite Zlength_firstn; rep_lia.

forward_loop     (PROP ( )
     LOCAL (temp _k (Vint (Int.repr (Zlength il))); temp _j (Vint (Int.repr (Zlength il)));
     temp _i (Vint (Int.repr (Zlength il / 2))); temp _t t;
     temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
     temp _arr1 p; temp _p (Vint (Int.repr (Zlength il / 2))); gvars gv; 
     temp _arr p; temp _len (Vint (Int.repr (Zlength il))))
     SEP (mem_mgr gv; malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il)) (map Vint (map Int.repr (mergesort il))) t;
     data_at sh (tarray tuint (Zlength il))
             (map Vint (map Int.repr l1) ++ map Vint (map Int.repr l2)) p))
                 break:     (PROP ( )
     LOCAL (temp _k (Vint (Int.repr (Zlength il))); temp _j (Vint (Int.repr (Zlength il)));
     temp _i (Vint (Int.repr (Zlength il / 2))); temp _t t;
     temp _arr2
       (force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr (Zlength il / 2)))));
     temp _arr1 p; temp _p (Vint (Int.repr (Zlength il / 2))); gvars gv; 
     temp _arr p; temp _len (Vint (Int.repr (Zlength il))))
     SEP (mem_mgr gv; malloc_token Ews (tarray tuint (Zlength il)) t;
     data_at Ews (tarray tuint (Zlength il)) (map Vint (map Int.repr (mergesort il))) t;
     data_at sh (tarray tuint (Zlength il))
             (map Vint (map Int.repr l1) ++ map Vint (map Int.repr l2)) p)).

entailer!.
forward_if False.
forward.
entailer!.
forward.
entailer!.

forward_call (Ews , sh , p, t,   mergesort il).
repeat rewrite mergesort_Zlength.
entailer!.
repeat rewrite mergesort_Zlength.
entailer!.
sep_apply data_at_memory_block.
simpl.
rewrite Z.max_r; try rep_lia.
entailer!.

rewrite mergesort_Zlength; rep_lia.

forward_call (tarray tuint (Zlength il), t , gv).
destruct ( eq_dec t nullval ); try contradiction; try entailer!.

repeat rewrite mergesort_Zlength; entailer!.

entailer!.
rewrite mergesort_Zlength; entailer!.

repeat rewrite Zlength_map; rewrite Zlength_firstn; rep_lia.
repeat rewrite Zlength_map; rewrite Zlength_skipn; rep_lia.
Qed.

