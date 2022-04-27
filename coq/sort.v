Require Import Arith.
Require Import Lia.
Require Import Recdef.
Require Import List.
Require Import Program.Tactics.
Require Import Program.Equality.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Import ListNotations.

Definition pairlen (x : list nat * list nat) : nat :=
  length (fst x) + length (snd x).

Function merge (x : list nat * list nat) {measure pairlen x} : list nat :=
  match x with
  | ([], []) => []
  | ([], (b :: t)) => b :: t
  | ((a :: s), []) => a :: s
  | ((a :: s), (b :: t)) => match (a ?= b) with
                            | Lt => a :: (merge (s, (b :: t)))
                            | Eq => a :: (merge (s, (b :: t)))
                            | Gt => b :: (merge ((a :: s), t))
                            end
  end.
Proof.
  all: intros; cbn; lia.
Defined.

Function halve (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | a :: [] => ([a], [])
  | a :: (b :: t) => let x := halve t in (a :: (fst x), b :: (snd x))
  end.

Lemma halve_sum (l : list nat) :
  length l = length (fst (halve l)) + length (snd (halve l)).
Proof.
  functional induction (halve l); simpl; lia.
Qed.

Function mergesort (l : list nat) {measure length l} : list nat :=
  match l with
  | [] => []
  | a :: [] => [a]
  | a :: (b :: t) => let x := halve l in merge (mergesort (fst x), mergesort (snd x))
  end.
Proof.
  all: intros; cbn; rewrite (halve_sum t); lia.
Defined.

Lemma halve_cons (a b : nat) (l : list nat) : 
  halve (a :: b :: l) = (a :: (fst (halve l)), b :: (snd (halve l))).
Proof.
  unfold halve. cbn. auto.
Qed.

Lemma Permutation_merge (x : list nat * list nat) :
  Permutation ((fst x) ++ (snd x)) (merge x).
Proof.
  functional induction (merge x); cbn in *; auto.
  - rewrite app_nil_end. auto.
  - apply (perm_skip b) in IHl.
    assert (Permutation ((a :: s) ++ (b :: t)) (b :: (a :: s) ++ t)).
    + apply Permutation_sym. apply Permutation_middle.
    + rewrite app_comm_cons in *. 
      apply Permutation_trans with (l':=(b :: (a :: s) ++ t)); auto.
Qed.

Lemma Permutation_halve (l : list nat) :
  Permutation l (fst (halve l) ++ snd (halve l)).
Proof.
  functional induction (halve l); simpl; auto.
  apply perm_skip. apply perm_trans with (l' := (b :: snd (halve t) ++ fst (halve t))).
  - apply perm_skip. apply perm_trans with (l' := (fst (halve t) ++ snd (halve t))); auto.
    apply Permutation_app_comm.
  - rewrite app_comm_cons. apply Permutation_app_comm.
Qed.

Lemma Permutation_mergesort (l : list nat) :
  Permutation l (mergesort l).
Proof.
  functional induction (mergesort l); auto.
  remember (halve (a :: b :: t)) as x.
  remember ((mergesort (fst x), mergesort (snd x))) as sortedx.
  assert (Permutation (fst (sortedx) ++ snd (sortedx)) (merge sortedx)) by apply Permutation_merge.
  apply perm_trans with (l' := (fst sortedx ++ snd sortedx)); auto.
  rewrite Heqsortedx; simpl.
  assert (Permutation (fst x ++ snd x) (mergesort (fst x) ++ mergesort (snd x))) by (apply Permutation_app; auto).
  apply perm_trans with (l' := (fst x ++ snd x)); auto.
  rewrite Heqx.
  apply Permutation_halve.
Qed.


Lemma Sorted_merge1 (n : nat) (xx : list nat * list nat) :
     HdRel le n (fst xx)
  -> HdRel le n (snd xx)
  -> Sorted le (merge xx)            
  -> HdRel le n (merge xx).
Proof.
  intros.
  functional induction merge xx.
  easy.
  easy.
  easy.

  simpl in *.
  econstructor.
  apply HdRel_inv in H. auto.

  simpl in *.
  econstructor.
  apply HdRel_inv in H. auto.

  simpl in *.
  econstructor.
  apply HdRel_inv in H0. auto.
Qed.



Lemma Sorted_merge (x : list nat * list nat) :
  Sorted le (fst x) -> Sorted le (snd x) -> Sorted le (merge x).
Proof.
  intros. functional induction merge x.
  all: auto; cbn in *.
  1-2: apply Sorted_inv in H. 3: apply Sorted_inv in H0.
  all: destruct_conjs; apply Sorted_cons; auto.
  all: specialize (IHl H H0).
  1: apply nat_compare_lt in e0. 2: apply nat_compare_eq in e0. 3: apply nat_compare_gt in e0.
  - apply Sorted_merge1. simpl. auto. simpl. econstructor. lia. auto.
  - apply Sorted_merge1. simpl. auto. simpl. econstructor. lia. auto.
  - apply Sorted_merge1. simpl. econstructor. lia. simpl.  auto. auto.
Qed.

Lemma Sorted_mergesort (l : list nat) :
  Sorted le (mergesort l).
Proof.
  functional induction mergesort l; auto.
  apply Sorted_merge; auto.
Qed.

Theorem mergesort_correct (l : list nat) :
  Permutation l (mergesort l) /\ Sorted le (mergesort l).
Proof.
  split.
  - apply Permutation_mergesort.
  - apply Sorted_mergesort.
Qed.
