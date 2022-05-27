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


Definition my_mergesort_spec : ident * funspec :=
 DECLARE _my_mergesort
 WITH p: val,  sh : share, il: list Z, gv: globals
 PRE [ tptr tint , tint ] 
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

(*
Definition malloc_spec_example  :=
 DECLARE _malloc
 WITH t:type, count : Z , gv: globals
 PRE [ tulong ]
    PROP (0 <= sizeof t <= Int.max_unsigned;
          complete_legal_cosu_type t = true;
          natural_aligned natural_alignment t = true)
    PARAMS (Vlong (Int64.repr( (sizeof t) * count)))
    SEP (mem_mgr gv)
 POST [ tptr tvoid ] EX p:_,
    PROP ()
    RETURN (p)
    SEP (mem_mgr gv;
            if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p)).

Definition Gprog : funspecs := [ my_mergesort_spec ; malloc_spec_example ].
 *)

Definition Gprog : funspecs :=
  ltac:(with_library prog [
             my_mergesort_spec                                    
 ]). 

Lemma div2_le : forall z, z >= 0 -> Z.div2 z <= z .
Proof.
intros.
unfold Z.div2.
destruct z.
lia.
destruct p; unfold Pos.div2; lia.
contradiction.
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
    destruct il. { admit. }  {
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
    rewrite  Zmax_left; try rep_lia.  
    rewrite Zmax_left; try rep_lia.
    split; try rep_lia.
    admit.
  }

  forward_call ( tarray tint (Zlength il), gv).
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

  
