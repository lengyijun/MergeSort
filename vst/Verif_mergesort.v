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
  apply Nat.add_le_lt_mono; auto.
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

Lemma merge_length : forall l1 , forall l2 , Zlength (merge l1 l2 ) = Zlength l1 + Zlength l2.
Proof.
  induction l1.
  intros.
  intuition.

  induction l2.
  intuition.

  unfold merge.
  unfold merge_func.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold merge_func.
  destruct (a <? a0); simpl; do 3 rewrite Zlength_cons.

  specialize (IHl1 (a0 :: l2)). 
  unfold merge in IHl1.
  rewrite IHl1.
  intuition.

  unfold merge in IHl2.
  rewrite IHl2.
  intuition.
Qed.

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
    assert ( Z.div2 (Zlength il) < Zlength il). {apply div2_le2. lia. }
    rep_lia.
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
  
  forward_loop (
     EX i, EX j, EX k,
     PROP(0 <= i <= Z.div2 (Zlength il);
          Z.div2 (Zlength il) <= j <= Zlength il;
          0 <= k <= Zlength il;
          Z.add k (Z.div2 (Zlength il)) = Z.add i j )
     LOCAL (temp _k (Vint (Int.repr k));
            temp _j (Vint (Int.divs (Int.repr (Zlength il)) (Int.repr 2)));
            temp _i (Vint (Int.repr i));
            temp _t t;
            temp _arr2
       (force_val
          (sem_binary_operation' Oadd (tptr tint) tint p
                                 (Vint (Int.divs (Int.repr (Zlength il)) (Int.repr 2)))));
            temp _arr1 p;
            temp _p (Vint (Int.divs (Int.repr (Zlength il)) (Int.repr 2)));
            gvars gv; 
            temp _arr p;
            temp _len (Vint (Int.repr (Zlength il)))
       )
       
     SEP (mem_mgr gv;
          malloc_token Ews (tarray tint (Zlength il)) t;
          data_at_ Ews (tarray tint (Zlength il)) t;
          data_at sh (tarray tuint (Zlength (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))
       (map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))
       (field_address0 (tarray tuint (Zlength il)) (SUB Z.div2 (Zlength il)) p);
     data_at sh (tarray tuint (Zlength (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))))
       (map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)))) p)
    )
    break:
    (
     EX i, EX j, EX k,
      PROP( i = Z.div2 (Zlength il) \/ j <= Zlength il;
            0 <= k <= Zlength il;
            Z.add k (Z.div2 (Zlength il)) = Z.add i j 
          )
     LOCAL (temp _k (Vint (Int.repr k));
            temp _j (Vint (Int.divs (Int.repr (Zlength il)) (Int.repr 2)));
            temp _i (Vint (Int.repr i));
            temp _t t;
            temp _arr2
       (force_val
          (sem_binary_operation' Oadd (tptr tint) tint p
                                 (Vint (Int.divs (Int.repr (Zlength il)) (Int.repr 2)))));
            temp _arr1 p;
            temp _p (Vint (Int.divs (Int.repr (Zlength il)) (Int.repr 2)));
            gvars gv; 
            temp _arr p;
            temp _len (Vint (Int.repr (Zlength il))))
     
     SEP (mem_mgr gv; malloc_token Ews (tarray tint (Zlength il)) t;
     data_at_ Ews (tarray tint (Zlength il)) t;
     data_at sh (tarray tuint (Zlength (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))
       (map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))
       (field_address0 (tarray tuint (Zlength il)) (SUB Z.div2 (Zlength il)) p);
     data_at sh (tarray tuint (Zlength (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))))
       (map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)))) p)
    ).

  Exists 0.
  Exists (Z.div2 (Zlength il)).
  Exists 0.
  entailer!.

  Intro i. Intro j. Intro k. Intros.

  forward_if (
     PROP ( )
     LOCAL (temp _k (Vint (Int.repr k));
     temp _j (Vint (Int.divs (Int.repr (Zlength il)) (Int.repr 2))); temp _i (Vint (Int.repr i));
     temp _t t;
     temp _arr2
       (force_val
          (sem_binary_operation' Oadd (tptr tint) tint p
             (Vint (Int.divs (Int.repr (Zlength il)) (Int.repr 2))))); temp _arr1 p;
     temp _p (Vint (Int.divs (Int.repr (Zlength il)) (Int.repr 2))); gvars gv; 
            temp _arr p;
            temp _len (Vint (Int.repr (Zlength il)));
            temp _t'2 (Val.of_bool true)
           )
     
     SEP (mem_mgr gv; malloc_token Ews (tarray tint (Zlength il)) t;
     data_at_ Ews (tarray tint (Zlength il)) t;
     data_at sh (tarray tuint (Zlength (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))
       (map Vint (map Int.repr (mergesort (skipn (Z.to_nat (Z.div2 (Zlength il))) il))))
       (field_address0 (tarray tuint (Zlength il)) (SUB Z.div2 (Zlength il)) p);
     data_at sh (tarray tuint (Zlength (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il))))
       (map Vint (map Int.repr (mergesort (firstn (Z.to_nat (Z.div2 (Zlength il))) il)))) p)
    ).
  forward.
  entailer!.
  {
    f_equal.
    unfold Int.divs.
  }
  forward.
  entailer!.
  forward_if True.
