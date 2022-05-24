Require Import VST.floyd.proofauto.
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
      | y1 :: ys => if x1 <? y1
        then x1::(merge xs y)
        else y1::(merge x ys)
      | _ => x
    end
  | _ => y
  end.
Next Obligation.
  apply Nat.add_le_lt_mono.
  reflexivity.
  auto.
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

(*
Definition my_mergesort_spec :=
 DECLARE _my_mergesort
 WITH p: val, l: list val
 PRE [ Tarray tint (Zlength l) noattr , tint ]
     PROP()
     PARAMS (p; length)
     SEP (data_at Tsh (Tarray tint length noattr ) l p )
 POST [ Tarray tint x noattr  ]
    EX r: val,
     PROP()
     RETURN(r)
     SEP (data_at Tsh (Tarray tint length noattr ) l p).
 *)

Definition my_mergesort_spec : ident * funspec :=
 DECLARE _my_mergesort
 WITH p: val,  il: list Z, gv: globals
 PRE [  Tarray tint 1 noattr , tint ] 
    PROP () 
    PARAMS (p; Vint (Int.repr (Zlength il)) ) GLOBALS(gv) 
    SEP () 
 POST [ Tarray tint 1 noattr  ] 
    PROP ( ) RETURN (p )
    SEP ().

Definition Gprog : funspecs := [ my_mergesort_spec ].

