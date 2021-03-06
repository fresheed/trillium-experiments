From iris.proofmode Require Import tactics.
From trace_program_logic.program_logic Require Export weakestpre.
From trace_program_logic.fairness Require Import fairness fair_termination.
From trace_program_logic.prelude Require Export finitary quantifiers sigma classical_instances.

Require Import stdpp.decidable.
From trace_program_logic.heap_lang Require Export lang lifting tactics.
From trace_program_logic.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.

Import derived_laws_later.bi.

Require Import List.
Import ListNotations.

Set Default Proof Using "Type".

(* Make it less ridiculous later... *)
Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

Tactic Notation "solve_pure_exec" :=
  lazymatch goal with
  | |- PureExec _ _ ?e _ =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      eapply (pure_exec_fill K _ _ e');
      [iSolveTC                       (* PureExec *)
      (* |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *) *)
      ])
    || fail "failed :("
  end.


Tactic Notation "wp_bind" open_constr(efoc) :=
  lazymatch goal with
  | |- context[(wp ?s ?E ?tid ?e ?Q)] =>
    reshape_expr e ltac:(fun K e' => unify e' efoc;
       iApply (wp_bind K); simpl
    )
    || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.


Ltac my_pure Hf :=
  iApply wp_lift_pure_step_no_fork_singlerole; eauto;
  do 3 iModIntro; iFrame; try iModIntro;
  iIntros Hf; simpl.

Ltac my_pures Hf :=
  repeat (my_pure Hf).

Ltac my_ld Hpthf :=
      wp_bind (Load _);
      iApply (wp_load_nostep with Hpthf); (try set_solver);
      [| iFrame; by rewrite has_fuel_fuels_S | (* TODO: one role versions! *)
      iModIntro; iIntros Hpthf; rewrite -has_fuel_fuels]; first set_solver.

Ltac my_st Hpthf :=
      wp_bind (Store _ _);
      iApply (wp_store_nostep with Hpthf);(try set_solver);
      [| iFrame; by rewrite has_fuel_fuels_S |
      iModIntro; iIntros Hpthf; rewrite -has_fuel_fuels]; first set_solver.


Global Hint Extern 0 (PureExec _ _ _ _) => solve_pure_exec: core.
Global Hint Extern 0 (vals_compare_safe _ _) => solve_vals_compare_safe: core.

Section SpinlockDefs. 


  (* The standard spin lock code *)
  Definition newlock : val := ??: <>, ref #false.
  Definition acquire : val :=
    rec: "acquire" "l" :=
      if: CAS "l" #false #true then #() else "acquire" "l".
  Definition release : val := ??: "l", "l" <- #false.

  Definition client : val :=
    ??: "l", acquire "l" ;; release "l".

  (* 2: not started yet, 1: has lock, 0: finished *)
  Definition spinlock_state := list nat.

  Definition state_unlocked (st: spinlock_state) :=
    forall j v (JV: st !! j = Some v), v = 0 \/ v >= 2.

  Definition state_locked_by (st: spinlock_state) (i: nat) :=
    st !! i = Some 1 /\
    (forall j v (JV: st !! j = Some v) (JNI: not (j = i)), v = 0 \/ v >= 2). 

  Inductive spinlock_model_step
    : spinlock_state -> option nat -> spinlock_state -> Prop :=
  | sm_lock st i v (READYi: st !! i = Some v) (V2: v >= 2)
            (UNLOCKED: state_unlocked st):
      spinlock_model_step st (Some i) (<[i:=1]> st)
  | sm_unlock st i (LOCKi: state_locked_by st i):
      spinlock_model_step st (Some i) (<[i:=0]> st)
  | sm_stutter st i v (LOCKED: exists j, state_locked_by st j)
               (READYi: st !! i = Some v) (V2: v >= 2):
      spinlock_model_step st (Some i) st
  .

  Lemma sm_step_same_length (st1 st2: spinlock_state) ol
        (STEP: spinlock_model_step st1 ol st2):
    length st1 = length st2.
  Proof. inversion STEP; try rewrite insert_length; auto. Qed. 

  Definition spinlock_lr (st: spinlock_state): gset nat :=
    list_to_set (filter (fun n => 0 <? default 0 (st !! n))
                        (seq 0 (length st))).
                          
  Definition spinlock_model: FairModel.
  Proof.
    refine ({|
        fmstate := spinlock_state; 
        fmrole := nat;
        fmtrans := spinlock_model_step;
        live_roles := spinlock_lr;
        fuel_limit _ := 25%nat; (* exact value; should relax its usage *)
             |}). 
    { intros. unfold spinlock_lr.
      apply elem_of_list_to_set, elem_of_list_In, filter_In.
      inversion H; subst. 
      - split.
        + apply in_seq. apply lookup_lt_Some in READYi. lia. 
        + apply PeanoNat.Nat.ltb_lt. rewrite READYi. simpl. lia.  
      - destruct LOCKi as [LOCKi _]. split.
        + apply in_seq. apply lookup_lt_Some in LOCKi. lia. 
        + apply PeanoNat.Nat.ltb_lt. rewrite LOCKi. auto. 
      - split.
        + apply in_seq. apply lookup_lt_Some in READYi. lia. 
        + apply PeanoNat.Nat.ltb_lt. rewrite READYi. simpl. lia. }
    { intros. unfold spinlock_lr in *. 
      apply elem_of_list_to_set, elem_of_list_In, filter_In.
      apply elem_of_list_to_set, elem_of_list_In, filter_In in H0 as [IN' DOM'].
      split.
      { erewrite <- sm_step_same_length; eauto. }
      apply PeanoNat.Nat.ltb_lt. apply PeanoNat.Nat.ltb_lt in DOM'.
      replace (s' !! ??') with (s !! ??'); auto.
      inversion H; subst; auto; symmetry; by apply list_lookup_insert_ne. }
  Defined. 
        
        
(* End SpinlockModel.  *)

  (* Section SpinlockCMRA. *)


  Class spinlockPreG ?? := {
    lock_preG :> inG ?? (exclR unitR);
    thread_preG :> inG ?? (excl_authR natO);
    
  }.
  
  Class spinlockG ?? := {
    lockG :> inG ?? (exclR unitR);
    threadG :> inG ?? (excl_authR natO);
    
    thread_gnames: list gname;
  }.
   
  Definition spinlock?? : gFunctors :=
    #[ heap?? spinlock_model; GFunctor (exclR unitR);
      GFunctor (excl_authR natO) ].
  
  Global Instance subG_spinlock?? {??} : subG spinlock?? ?? ??? spinlockPreG ??.
  Proof. solve_inG. Qed.
    
End SpinlockDefs. 

Section ClientProofs.
  Context `{!heapGS ?? spinlock_model, !spinlockG ??}.
  Let Ns := nroot .@ "spinlock".

  Definition thst_auth (i v: nat): iProp ?? :=
    ??? (tgn: gname), ???thread_gnames !! i = Some tgn??? ??? own tgn (???E v).

  Definition thst_frag (i v: nat): iProp ?? :=
    ??? (tgn: gname), ???thread_gnames !! i = Some tgn??? ??? own tgn (???E v).
  
  Definition model_inv_impl (st: list nat) : iProp ?? :=
      frag_model_is st ??? 
      ([??? set] i ??? list_to_set (seq 0 (length thread_gnames)), 
       ??? v, ???st !! i = Some v??? ??? thst_auth i v) ???
      ???length st = length thread_gnames???.

  Definition locked ?? := own ?? (Excl ()).
       
  Definition lock_inv_impl v l ?? P : iProp ?? :=
    l ??? v ??? (???v = #false??? ??? P ??? locked ?? ??? ???v = #true???).

  Definition model_lock_corr_impl v st: iProp ?? :=
    ???v = #false ??? state_unlocked st ??? v = #true ??? ??? i, state_locked_by st i???. 

  Definition spinlock_inv l ?? P: iProp ?? :=
    inv Ns (??? (v: val) (st: spinlock_state),
               model_inv_impl st ??? lock_inv_impl v l ?? P ???
                              model_lock_corr_impl v st).

  Lemma thst_frag_bound th i:
    thst_frag th i -??? ???th < length thread_gnames???.
  Proof. 
    iIntros "TH_ST". rewrite /thst_frag.
    iDestruct "TH_ST" as (tgn) "[%LOOKUP _]". iPureIntro.
    eapply lookup_lt_Some. eauto.
  Qed.

  Lemma thst_auth_bound th i:
    thst_auth th i -??? ???th < length thread_gnames???.
  Proof. 
    iIntros "TH_ST". rewrite /thst_auth. 
    iDestruct "TH_ST" as (tgn) "[%LOOKUP _]". iPureIntro.
    eapply lookup_lt_Some. eauto.
  Qed.

  (* Lemma excl_authR_agree (gf: gFunctors) {A: ofe} (??: gname) (x y: A): *)
  (*   own ?? (???E x) -??? own ?? (???E y) -??? ??? x = y ???. *)
  (* Proof. *)
  (*   iIntros "HA HB". iCombine "HB HA" as "H". *)
  (*   iDestruct (own_valid with "H") as "%Hval". *)
  (*   iPureIntro. by apply excl_auth_agree_L. *)
  (* Qed. *)
  Lemma thst_agree (i x y: nat):
    thst_auth i x -??? thst_frag i y -??? ??? x = y ???.
  Proof.
    iIntros "AUTH FRAG". 
    rewrite /thst_frag. iDestruct "AUTH" as (tgn) "[%ITH AUTH]".
    rewrite /thst_auth. iDestruct "FRAG" as (tgn') "[%ITH' FRAG]".
    assert (tgn' = tgn) as -> by congruence. 
    iCombine "AUTH FRAG" as "OWN". 
    iDestruct (own_valid with "OWN") as "%VALID".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.

  Lemma thst_update (i z x y: nat):
    thst_auth i x ??? thst_frag i y ==??? thst_auth i z ??? thst_frag i z. 
  Proof.
    iIntros "[AUTH FRAG]". 
    rewrite /thst_frag. iDestruct "AUTH" as (tgn) "[%ITH AUTH]".
    rewrite /thst_auth. iDestruct "FRAG" as (tgn') "[%ITH' FRAG]".
    assert (tgn' = tgn) as -> by congruence.
    iDestruct (own_update with "[AUTH FRAG]") as "OWN". 
    { eapply excl_auth_update. }
    { iApply own_op. iFrame. }
    iMod "OWN". iModIntro.
    iApply bi.sep_exist_r. iExists tgn. iApply bi.sep_exist_l. iExists tgn.
    iDestruct (own_op with "OWN") as "[? ?]".
    iFrame. auto.    
  Qed.

  Lemma live_roles_preservation st (th: fmrole spinlock_model) v
        (THST01 : 0 < default 0 (st !! th)):
    live_roles spinlock_model (<[th:=v]> st) ??? live_roles spinlock_model st.
  Proof. 
    simpl. rewrite /spinlock_lr.
    apply elem_of_subseteq. intros ?? IN.
    apply elem_of_list_to_set, elem_of_list_In, filter_In. 
    apply elem_of_list_to_set, elem_of_list_In, filter_In in IN as [IN FLT].
    split.
    { erewrite <- insert_length. eauto. }
    destruct (dec_eq_nat ?? th) as [-> | ?]. 
    { by apply Nat.ltb_lt. }
    rewrite list_lookup_insert_ne in FLT; auto. 
  Qed.

  Lemma model_inv_helper th v' (st: list nat)
        (LENGTHS: length st = length thread_gnames):
    (([??? set] y ??? (list_to_set (seq 0 (length thread_gnames)) ??? {[th]}),
     ??? v, ???st !! y = Some v??? ??? thst_auth y v) ???
    frag_model_is st ??? 
    ???st !! th = Some v'??? ???
    thst_auth th v') -???
    model_inv_impl st.
  Proof.
    iIntros "(AUTHS' & ST & %LOOKUP & AUTH)".
    iFrame.
    rewrite /model_inv_impl.
    iPoseProof (thst_auth_bound with "[AUTH]") as "%BOUND"; [iFrame| ].
    iSplitL; [| done].     
    iApply big_sepS_delete.
    { apply elem_of_list_to_set, elem_of_list_In. apply in_seq.
      split; [lia | eauto]. }
    iSplitL "AUTH".
    { iExists v'. by iFrame. }
    iFrame. 
  Qed.


  Lemma model_inv_change_helper th v' (st: list nat)
        (LENGTHS: length st = length thread_gnames):
    ([??? set] y ??? (list_to_set (seq 0 (length thread_gnames)) ??? {[th]}),
     ??? v, ???st !! y = Some v??? ??? thst_auth y v) ???
    frag_model_is (<[th:=v']> st) ??? thst_auth th v' -???
    model_inv_impl (<[th:=v']> st).
  Proof.
    iIntros "(AUTHS' & ST & AUTH)".
    iApply (model_inv_helper with "[AUTHS' ST AUTH]").
    { by rewrite insert_length. }
    iPoseProof (thst_auth_bound with "AUTH") as "%BOUND". 
    iFrame. iSplit.  
    2: { iPureIntro. apply list_lookup_insert. congruence. }
    iApply (big_sepS_impl with "[AUTHS']"); [by iFrame| ].
    iModIntro. iIntros (i IN) "[%v [%ITH AUTH]]".
    iExists v. iFrame.
    destruct (dec_eq_nat i th) as [-> | ?]. 
    2: { iPureIntro. rewrite list_lookup_insert_ne; auto. }
    apply elem_of_difference in IN as [_ NEQ].
    destruct NEQ. set_solver.
  Qed.

  Lemma state_becomes_locked st th (UNLOCKED: state_unlocked st)
        (DOM: th < length st):
    state_locked_by (<[th:=1]> st) th.
  Proof.
    red. split.
    { by apply list_lookup_insert. }
    intros. eapply UNLOCKED. rewrite <- JV.
    symmetry. by apply list_lookup_insert_ne. 
  Qed.

  Lemma state_becomes_unlocked st th (LOCKED: state_locked_by st th)
        (DOM: th < length st):
    state_unlocked (<[th:=0]> st).
  Proof.
    red. intros.
    destruct (dec_eq_nat j th) as [-> | ?].
    { rewrite list_lookup_insert in JV; auto. inversion JV. auto. } 
    rewrite list_lookup_insert_ne in JV; auto.
    destruct LOCKED. eapply H1; eauto.
  Qed. 


  Ltac pure_step_burn_fuel f :=
    destruct f; [lia| ]; 
    iApply wp_lift_pure_step_no_fork_singlerole; auto;
    do 3 iModIntro; iFrame; iIntros "FUEL"; simpl.

  Lemma nonfinished_role_is_alive th st v (DOM: th < length st)
        (THV: st !! th = Some v)
        (NONFIN: 0 < v):
    th ??? live_roles spinlock_model st.
  Proof.
    simpl. unfold spinlock_lr.
    apply elem_of_list_to_set, elem_of_list_In. apply filter_In. split.
    { apply in_seq. lia. }
    rewrite THV. by apply PeanoNat.Nat.ltb_lt.
  Qed. 
      
  Lemma acquire_spec_term tid l ?? P f (FUEL: f > 5) th:
    {{{ spinlock_inv l ?? P ??? has_fuel tid th f ??? thst_frag th 2 }}}
      acquire #l @ tid
    {{{ RET #(); P ??? locked ?? ??? thst_frag th 1 ??? ??? f, has_fuel tid th f ??? ???f > 4 ???}}}.
  Proof.
    iL??b as "IH" forall (f FUEL). 
    iIntros (??) "(#INV & FUEL & THST_FRAG) Kont".
    rewrite {2}/acquire.

    pure_step_burn_fuel f. 
    
    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic. 
    iInv Ns as (lv st) "(>MODEL & LOCK & >%CORR)" "Clos".
    
    iDestruct (thst_frag_bound with "THST_FRAG") as "%TH_BOUND".

    rewrite {1}/model_inv_impl. iDestruct "MODEL" as "(ST & AUTHS & %LENGTHS)".
    iDestruct (big_sepS_delete with "AUTHS") as "[TH_AUTH AUTHS']".
    { apply elem_of_list_to_set, elem_of_list_In. apply in_seq. simpl.
      split; [lia| apply TH_BOUND]. }
    iDestruct "TH_AUTH" as (v) "[%THST_V THST_AUTH]".
    iDestruct (thst_agree with "THST_AUTH THST_FRAG") as "%V0". subst v.

    assert (th < length st) as TH_BOUND' by (eapply lookup_lt_Some; eauto). 

    rewrite {1}/lock_inv_impl.
    destruct CORR as [[-> UNLOCKED]| [LOCKED [i ST_LOCKED]]]. 
    - iDestruct "LOCK" as "[>L [(_ & P & LOCKED) | Lval]]". 
      2: { iDestruct "Lval" as ">%Lval". done. }
      (* |={??? ??? ???Ns,?E3}=> WP #l <- #false @ tid; ?E3 {{ v, |={?E3,???}=> ?? v }} *)

      iApply ((wp_cmpxchg_suc_step_singlerole _ tid th _ 10%nat st (<[th:=1]> st)) with "[$]"). 
      all: eauto. 
      { simpl. lia. }
      { econstructor; eauto. }
      { apply live_roles_preservation. rewrite THST_V. simpl. lia. }

      do 2 iModIntro. iIntros "(L & ST & FUEL)".
      iMod ((thst_update th 1) with "[THST_AUTH THST_FRAG]")
        as "[THST_AUTH THST_FRAG]"; [by iFrame| ].
      iMod ("Clos" with "[-THST_FRAG Kont P LOCKED FUEL]") as "_". 
      { iModIntro. iExists (#true)%V. iExists _.
        iDestruct (model_inv_change_helper with "[AUTHS' ST THST_AUTH]") as "MODEL"; eauto. 
        { iFrame. }
        iFrame. iSplitL.
        { iRight. done. } 
        rewrite /model_lock_corr_impl. iPureIntro. right.
        split; auto. exists th. by apply state_becomes_locked. }
      rewrite decide_True. 
      2: { eapply nonfinished_role_is_alive. 
           - by rewrite insert_length.
           - by apply list_lookup_insert.
           - lia. }
      iModIntro.
      do 2 (pure_step_burn_fuel f). 
      iApply wp_value. iApply "Kont". iFrame. iExists _. iFrame. iPureIntro. lia.
    - iDestruct "LOCK" as "[>L [[>-> _] | >->]]"; [done| ].
      iApply ((wp_cmpxchg_fail_step_singlerole _ tid th _ 10%nat st st) with "[$]").
      all: eauto. 
      { simpl. lia. }
      { econstructor; eauto. }
      do 2 iModIntro. iIntros "(L & ST & FUEL)".
      rewrite decide_True.
      2: { eapply nonfinished_role_is_alive; eauto. }
      iMod ("Clos" with "[-THST_FRAG Kont FUEL]") as "_". 
      { iDestruct (model_inv_helper with "[AUTHS' ST THST_AUTH]") as "MODEL"; eauto.
        { by iFrame. }
        iModIntro. do 2 iExists _. iFrame. iSplit.
        { by iRight. }
        rewrite /model_lock_corr_impl. iRight. eauto. }
      iModIntro.
      do 2 pure_step_burn_fuel f.
      iApply ("IH" $! 8 with "[] [FUEL THST_FRAG]"). 
      { iPureIntro. lia. }
      { do 2 iFrame. done. }
      iFrame. 
  Qed.

  Lemma locked_thread_det st (i: nat) (th: fmrole spinlock_model)
        (ST_LOCKED: state_locked_by st i):
    thst_frag th 1 -??? model_inv_impl st -???
    ???i = th???.
  Proof.
    iIntros "THST_FRAG MODEL".
    iPoseProof (thst_frag_bound with "THST_FRAG") as "%BOUND". 
    rewrite /model_inv_impl. iDestruct "MODEL" as "(_ & AUTHS & %LENGTHS)".
    iDestruct (big_sepS_delete with "AUTHS") as "[TH_AUTH AUTHS']".
    { apply elem_of_list_to_set, elem_of_list_In. apply in_seq. simpl.
      split; [lia| apply BOUND]. }
    iDestruct "TH_AUTH" as (v) "[%TH_V AUTH]".
    iDestruct (thst_agree with "AUTH THST_FRAG") as "#->".
    iPureIntro.
    destruct (dec_eq_nat i th); [done| ].
    red in ST_LOCKED. destruct ST_LOCKED as [_ NOT1].
    specialize (NOT1 _ _ TH_V). lia.   
  Qed. 

  Lemma release_spec_term tid l ?? P f (FUEL: f > 2) (th: fmrole spinlock_model):
    {{{ spinlock_inv l ?? P ??? P ??? locked ?? ??? thst_frag th 1 ??? has_fuel tid th f }}}
      release #l @ tid
    {{{ RET #(); tid ???M ??? ??? thst_frag th 0 }}}.
  Proof.
    iIntros (??) "(#INV & P & LOCKED & THST_FRAG & FUEL) Kont". rewrite /release.
    iDestruct (thst_frag_bound with "THST_FRAG") as "%TH_BOUND".


    (* TODO: fix pure_step_burn_fuel by adding FUEL param *)
    destruct f; [lia| ]. 
    iApply wp_lift_pure_step_no_fork_singlerole; auto. 
    do 3 iModIntro. iSplitL "FUEL"; [by iFrame| ]. iIntros "FUEL"; simpl.

    rewrite /spinlock_inv.
    iApply wp_atomic.
    iInv Ns as (lv st) "(>MODEL & [>L LOCK] & >%CORR)" "Clos".
    rewrite {2}/lock_inv_impl.
    
    iDestruct "LOCK" as "[(_ & _ & LOCKED') | LOCK]".
    { iMod "LOCKED'".
      rewrite /locked. iCombine "LOCKED LOCKED'" as "L'".
      simpl.
      rewrite /op /cmra_op /=  /excl_op_instance.
      iDestruct (own_valid with "L'") as "%".
      done. }
    
    
    iDestruct "LOCK" as ">->".
    destruct CORR as [[? _] | [_ [i ST_LOCKED]]]; [done| ].
    
    iDestruct (locked_thread_det with "THST_FRAG MODEL") as "%EQ"; eauto. subst i.

    destruct f; [lia| ]. 
    rewrite {2}/model_inv_impl. iDestruct "MODEL" as "(ST & AUTHS & %LENGTH)". 
    iApply ((wp_store_step_singlerole _ tid th _ 10%nat st (<[th:=0]> st)) with "[L ST FUEL]").
    all: eauto.
    { simpl. lia. }
    { by econstructor. }
    { apply live_roles_preservation. destruct ST_LOCKED. rewrite H. simpl. lia. }
    { iFrame. }
    do 2 iModIntro. iIntros "(L & ST & FUEL)".
    rewrite decide_False.
    2: { simpl. unfold spinlock_lr. intros IN.
         apply elem_of_list_to_set, elem_of_list_In, filter_In in IN as [_ FLT].
         rewrite list_lookup_insert in FLT; [done| lia]. }

    iApply "Kont". iFrame. 

    iDestruct (big_sepS_delete with "AUTHS") as "[TH_AUTH AUTHS']".
    { apply elem_of_list_to_set, elem_of_list_In. apply in_seq. simpl.
      split; [lia| eauto]. }
    iDestruct "TH_AUTH" as (v) "[%TH_V THST_AUTH]".
    iMod ((thst_update th 0) with "[THST_AUTH THST_FRAG]")
        as "[THST_AUTH THST_FRAG]"; [by iFrame| ].
    iFrame. 

    iMod ("Clos" with "[-]") as "_"; [| done].
    iNext. iExists (#false)%V. iExists _. 
    iDestruct (model_inv_change_helper with "[AUTHS' ST THST_AUTH]") as "MODEL".
    { eauto. }
    { iFrame. }
    iFrame. iSplitL; [by (iLeft; iFrame)|].
    rewrite /model_lock_corr_impl. iLeft. iPureIntro. split; auto. 
    apply state_becomes_unlocked; auto. lia.
  Qed. 
    
    
  Lemma client_terminates tid l ?? P f th (FUEL: f > 12) :
    {{{ spinlock_inv l ?? P ??? has_fuel tid th f ??? thst_frag th 2}}}
      client #l @ tid
    {{{ RET #(); tid ???M ???  }}}.
  Proof.
    iIntros (??) "(#INV & FUEL & FRAG) Kont".
    rewrite /client.
    pure_step_burn_fuel f.
    wp_bind (acquire #l)%E.
    iApply (acquire_spec_term with "[-Kont]"). 
    2: { by iFrame. }
    { lia. }
    clear dependent f. 
    iNext. iIntros "(P & LOCKED & FRAG & [%f [FUEL %FUEL]])".
    do 2 pure_step_burn_fuel f. 
    iApply (release_spec_term with "[-Kont]").
    2: { iFrame. iSplitR "P"; done. }
    { lia. }
    iNext. iIntros "[FIN FRAG]". by iApply "Kont".
  Qed.

  Definition fuels_ge (fs: gmap (fmrole spinlock_model) nat) b :=
    forall ?? f (FUEL: fs !! ?? = Some f), f >= b. 
    
  Lemma has_fuels_ge_S_exact b tid ths (fs: gmap (fmrole spinlock_model) nat)
        (FUELS_GE: fuels_ge fs (S b)):
    has_fuels tid ths fs -???
    has_fuels_S tid ths (fmap (fun f => f - 1) fs). 
  Proof.
    iIntros "FUELS".
    rewrite /has_fuels_S /has_fuels.
    iDestruct "FUELS" as "(? & %DOM & FUELS)". iFrame. iSplitR.
    { iPureIntro. by do 2 rewrite dom_fmap_L. }
    iApply (big_sepS_impl with "[-]"); [by iFrame| ].
    iModIntro. iIntros (??) "%DOM?? [%f [%TT F??]]".
    iExists _. iFrame. iPureIntro.
    apply lookup_fmap_Some. exists (f - 1). split.
    { red in FUELS_GE. specialize (FUELS_GE _ _ TT). lia. }
    apply lookup_fmap_Some. eauto.
  Qed.

  Lemma fuels_ge_minus1 fs b (FUELS_GE: fuels_ge fs (S b)):
    fuels_ge ((?? f, f - 1) <$> fs) b.
  Proof. 
    red. intros.
    pose proof (elem_of_dom_2 _ _ _ FUEL) as DOM.
    rewrite dom_fmap_L in DOM.
    simpl in FUEL.
    apply lookup_fmap_Some in FUEL as (f' & <- & FUEL).
    red in FUELS_GE. specialize (FUELS_GE _ _ FUEL). lia.
  Qed. 
    
  Lemma has_fuels_ge_S b tid ths (fs: gmap (fmrole spinlock_model) nat)
        (FUELS_GE: fuels_ge fs (S b)):
    has_fuels tid ths fs -??? ??? fs', has_fuels_S tid ths fs' ??? ???fuels_ge fs' b???.
  Proof.
    iIntros "FUELS".
    iDestruct (has_fuels_ge_S_exact with "FUELS") as "FUELS"; eauto.
    iExists _. iFrame. 
    iPureIntro. by apply fuels_ge_minus1. 
  Qed.
          
End ClientProofs.


Section MainProof.
  Context `{!heapGS ?? spinlock_model, !spinlockPreG ??}.
  Let Ns := nroot .@ "spinlock".

  Definition program: expr :=
    let: "l" := newlock #() in
    ((Fork (client "l") ) ;; (Fork (client "l") )).

  (* TODO: use set_seq instead of list_to_set *)
  Lemma thread_gnames_allocation n v:
    ??? (|==> ??? (tgns: list gname), ???length tgns = n??? ???
        ([??? set] i ??? list_to_set (seq 0 n), 
         ??? ??, ???tgns !! i = Some ????? ??? own ?? (???E v) ??? own ?? (???E v)))%I.
  Proof.
    iInduction n as [| n'] "IH".
    { iModIntro. iExists []. iSplit; done. }
    iMod (own_alloc (???E v  ??? ???E v)) as (??) "[AUTH FRAG]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod "IH" as (tgns) "[%LEN IH]". iModIntro.
    (* appending to the end to obtain the same domain and reuse IH *)
    (* TODO: problems with appending to the head and/or big_sepS_forall *)
    iExists (tgns ++ [??]). iSplitL "".
    { iPureIntro. rewrite app_length. simpl. lia. }
    rewrite seq_S list_to_set_app_L. simpl. rewrite union_empty_r_L.
    iApply big_sepS_union.
    { symmetry. rewrite list_to_set_seq. set_solver by lia. }
    iSplitL "IH".
    { iApply (big_sepS_impl with "IH"). iModIntro.
      iIntros (i DOM) "[%??' (%ITH & ? & ?)]".
      iExists _. iFrame. iPureIntro.
      rewrite lookup_app_l; auto. by apply lookup_lt_Some in ITH. }
    iApply big_sepS_singleton.
    iExists _. iFrame. iPureIntro. rewrite lookup_app_r; [| lia].
    by rewrite LEN PeanoNat.Nat.sub_diag. 
  Qed.

  Lemma repeat_lookup {A: Type} (v: A) (n i: nat) (DOM: i < n):
    (repeat v n) !! i = Some v.
  Proof.
    generalize dependent i. induction n; [lia| ].
    intros i DOM. simpl. destruct i; auto.
    simpl. apply IHn. lia.
  Qed.

  Lemma has_fuels_funext tid ths (fs: gmap (fmrole spinlock_model) nat) g1 g2
        (EXT: forall n, g1 n = g2 n):
    has_fuels tid ths (g1 <$> fs) -??? has_fuels tid ths (g2 <$> fs).
  Proof.
    iIntros "FUELS". rewrite /has_fuels.
    iDestruct "FUELS" as "(? & ? & FUELS)".
    repeat rewrite dom_fmap_L. iFrame.
    iApply (big_sepS_impl with "[$]").
    iModIntro. iIntros (x DOM) "(%ITH & % & ?)".
    iExists _. iFrame. iPureIntro. erewrite map_fmap_ext.
    2: { intros. symmetry. apply EXT. }
    auto.
  Qed. 

  Lemma newlock_spec tid P (ths: list (fmrole spinlock_model)) fs
        (THSn0: ths ??? []) (FUELS: fuels_ge fs 20):
    {{{ P ??? has_fuels tid (list_to_set ths) fs ???
          frag_model_is (repeat 2 (length ths)) }}}
      newlock #() @ tid
    {{{ l, RET #l; ??? ?? (slG: spinlockG ??),
          spinlock_inv l ?? P ???
          ([??? set] i ??? list_to_set (seq 0 (length ths)), thst_frag i 2) ???
          (* (??? fs, has_fuels tid (list_to_set ths) fs ??? ???fuels_ge fs 18???) }}}. *)
          (has_fuels tid (list_to_set ths) ((fun f => f - 2) <$> fs)) }}}.
  (* Proof. *)
  Proof using Ns heapGS0 spinlockPreG0 ??. 
    iIntros (??) "(P & FUELS & ST) Kont". rewrite /newlock.
    remember (list_to_set ths) as ths_set.
    assert (ths_set ??? ???) as THSn0'.
    { subst. destruct ths; [done| ].
      apply (non_empty_inhabited_L f). set_solver. }

    iDestruct (has_fuels_ge_S_exact with "FUELS") as "FUELS'"; eauto.
    iApply wp_lift_pure_step_no_fork'; eauto.
    do 3 iModIntro. simpl.
    iFrame. iIntros "FUELS".
    
    iMod (own_alloc (Excl ())) as (??) "LOCK"; [done| ].
    
    iDestruct (has_fuels_ge_S_exact 18 with "FUELS") as "FUELS"; eauto.
    { by apply fuels_ge_minus1. }
    (* TODO: fupd in goal is needed to create invariant *)
    wp_bind (Alloc _)%E.
    iApply (wp_alloc_nostep with "[FUELS]"); eauto.

    iNext. iIntros (l) "(L & _ & FUELS)".
    
    (* (* TODO: resources disappear? *) *)
    (* (* iApply (fupd_mono with "[-Kont]"). *) *)

    rewrite <- map_fmap_compose. simpl.

    iMod (thread_gnames_allocation (base.length ths) 2) as "[%tgns [%TGNS_LEN TGNS]]".

    set (slg := {| thread_gnames := tgns; threadG := @thread_preG _ spinlockPreG0;
                   lockG := @lock_preG _ spinlockPreG0 |}).
    
    iAssert (([??? set] i ??? list_to_set (seq 0 (base.length ths)), thst_frag i 2) ???
             ([??? set] i ??? list_to_set (seq 0 (base.length ths)), thst_auth i 2))%I with "[TGNS]" as "[FRAGS AUTHS]". 
    { iApply big_sepS_sep. iApply (big_sepS_impl with "[$]").
      iModIntro. clear dependent ??. iIntros (i DOM) "[%?? (%ITH & AUTH & FRAG)]".
      rewrite /thst_auth /thst_frag.
      iApply bi.sep_exist_r. iExists _. iFrame.
      iApply bi.sep_exist_l. iExists _. iFrame. done. }
    
    iApply fupd_wp. 
    iMod (inv_alloc Ns _ (??? v st, model_inv_impl st ??? lock_inv_impl v l ?? P ???
                                                 model_lock_corr_impl v st)%I with "[-Kont FRAGS FUELS]") as "INV".
    2: { iModIntro. iApply wp_value. iApply "Kont".
         do 2 iExists _. iFrame.
         iApply (has_fuels_funext with "[$]"). intros. simpl. lia. }
    iNext. rewrite /model_inv_impl /lock_inv_impl /model_lock_corr_impl.
    do 2 iExists _. iFrame.
    rewrite TGNS_LEN. iSplitL "AUTHS".
    { iSplitR ""; [| iPureIntro; by rewrite repeat_length].
      iApply (big_sepS_impl with "[$]").
      iModIntro. clear dependent ??. iIntros (i DOM) "AUTH".
      iExists 2. iFrame. iPureIntro.
      apply repeat_lookup. 
      apply elem_of_list_to_set, elem_of_seq in DOM. simpl in DOM. lia. }

    iSplitR "".
    { iLeft. by iFrame. }
    iLeft. iPureIntro. split; auto. red. intros. 
    pose proof (lookup_lt_Some _ _ _ JV) as DOM. rewrite repeat_length in DOM. 
    rewrite repeat_lookup in JV; auto. inversion JV. lia. 
  Qed. 

  Lemma has_fuels_equiv_args tid (R1 R2: gset (fmrole spinlock_model))
        (FS1 FS2: gmap (fmrole spinlock_model) nat)
        (REQ: R1 ??? R2) (FSEQ: FS1 ??? FS2):
    has_fuels tid R1 FS1 -??? has_fuels tid R2 FS2.
  Proof.
    apply leibniz_equiv in REQ. apply leibniz_equiv in FSEQ. subst. auto. 
  Qed. 

  (* TODO: merge with previous *)
  Ltac pure_step_burn_fuel_impl :=
    iApply wp_lift_pure_step_no_fork_singlerole; auto;
    do 3 iModIntro; iFrame; iIntros "FUEL"; simpl.

  Ltac pure_step_burn_fuel f := destruct f; [lia| ]; pure_step_burn_fuel_impl.

  Lemma fuels_ge_helper fs b th f (REC: fuels_ge fs b) (GE: f >= b):
    fuels_ge (<[th:=f]> fs) b.
  Proof.
    unfold fuels_ge. intros.
    pose proof FUEL as FUEL_. apply elem_of_dom_2 in FUEL.
    destruct (dec_eq_nat ?? th) as [-> | NEQ]. 
    { rewrite lookup_insert in FUEL_. congruence. }
    rewrite dom_insert_L in FUEL. apply elem_of_union in FUEL as [DOM | DOM].
    { by apply elem_of_singleton_1 in DOM. }
    rewrite lookup_insert_ne in FUEL_; eauto.  
  Qed. 
    
  Lemma program_spec tid (P: iProp ??):
    (* {{{ frag_model_is [0; 0] ??? has_fuels tid {[ 0; 1 ]} fs ??? P }}} *)
    {{{ frag_model_is [2; 2] ??? P ??? 
      has_fuels tid {[0; 1]} {[ 0:=25; 1:=25 ]} }}}
      program @ tid
    {{{ RET #(); tid ???M ??? }}}.
  Proof using All.
    iIntros (??) "(ST & P & FUELS) Kont". rewrite /program.

    wp_bind (newlock #())%E.
    iApply (newlock_spec tid P [0; 1] with "[P FUELS ST]"); eauto.
    2: { iFrame. iApply has_fuels_equiv_args; last by iFrame.
         - set_solver.
         - reflexivity. }
    { do 2 (apply fuels_ge_helper; [| lia]). done. }

    iNext. iIntros (l) "(%?? & %slG & (#INV & FRAGS & FUELS))".
    repeat rewrite fmap_insert. simpl. rewrite fmap_empty. simpl.   

    iDestruct ((has_fuels_ge_S_exact 22) with "FUELS") as "FUELS"; eauto.
    { do 2 (apply fuels_ge_helper; [| lia]). done. }
    repeat rewrite fmap_insert. simpl. rewrite fmap_empty. simpl.   
    iApply (wp_lift_pure_step_no_fork' _ _ _ _ _ _ _ _ {[0; 1]}); eauto.
    
    do 3 iModIntro. iSimpl. 
    iFrame. iIntros "FUELS".
    Unshelve. all: try by eauto.  (* TODO: get rid of *)

    iDestruct ((has_fuels_ge_S_exact 21) with "FUELS") as "FUELS"; eauto.
    { do 2 (apply fuels_ge_helper; [| lia]). done. }
    repeat rewrite fmap_insert. simpl. rewrite fmap_empty. simpl.
    iApply (wp_lift_pure_step_no_fork' _ _ _ _ _ _ _ _ {[0; 1]}); eauto.
    do 3 iModIntro. iSimpl. 
    iFrame. iIntros "FUELS".
    Unshelve. all: try by eauto.  (* TODO: get rid of *)
    
    iDestruct (big_sepS_insert with "FRAGS") as "[FRAG0 FRAGS]"; [set_solver| ]. 
    iDestruct (big_sepS_insert with "FRAGS") as "[FRAG1 _]"; [set_solver| ]. 

    wp_bind (Fork _)%E.

    iDestruct ((has_fuels_ge_S_exact 20) with "FUELS") as "FUELS"; eauto.
    { do 2 (apply fuels_ge_helper; [| lia]). done. }
    repeat rewrite fmap_insert. simpl. rewrite fmap_empty. simpl.
    
    iApply (wp_fork_nostep _ tid _ _ _ {[ 1 ]} {[ 0 ]} _ with "[FRAG0] [-FUELS] [FUELS]").
    5: { rewrite /has_fuels_S.
         iApply has_fuels_equiv_args; last (by iFrame); set_solver. }
    { set_solver. }
    { done. }
    { iIntros (tid0).
      iNext. iIntros "FUEL".
      rewrite map_filter_insert; last set_solver.
      rewrite map_filter_insert_not; last set_solver.
      rewrite map_filter_empty insert_empty.
      iApply (client_terminates with "[-]"); last by auto. 
      2: { iFrame. iSplitR; [by iApply "INV"| ].
           iApply has_fuel_fuels. iFrame. }
      lia. }

    (* TODO: unify these proofs *)
    
    iNext. iIntros "FUEL".
    iModIntro.

    rewrite map_filter_insert_not; last set_solver.    
    rewrite map_filter_insert; last set_solver.
    rewrite map_filter_empty insert_empty.
    
    iDestruct (has_fuel_fuels with "FUEL") as "FUEL".
    do 2 pure_step_burn_fuel_impl. 
    
    (* TODO: unify even more*)
    iApply (wp_fork_nostep _ tid _ _ _ ??? {[ 1 ]} {[1 := 17]} with "[FRAG1] [-FUEL] [FUEL]").
    5: { rewrite /has_fuels_S.
         iApply has_fuels_equiv_args.
         3: { iApply has_fuel_fuels. iFrame. }
         { set_solver. }
         rewrite fmap_insert fmap_empty. set_solver. }
    { set_solver. }
    { done. }
    { iIntros (tid0).
      iNext. iIntros "FUEL".
      rewrite map_filter_insert; last set_solver.
      rewrite map_filter_empty insert_empty.
      iApply (client_terminates with "[-]"); last by auto. 
      2: { iFrame. iSplitR; [by iApply "INV"| ].
           iApply has_fuel_fuels. iFrame. }
      lia. }

    iNext. iIntros "FUELS". iModIntro. iApply "Kont".
    rewrite /has_fuels. by iDestruct "FUELS" as "[? _]". 

  Qed.

End MainProof. 
