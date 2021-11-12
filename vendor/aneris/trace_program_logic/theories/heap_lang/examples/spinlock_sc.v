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

Section SpinlockCode.

  (* The standard spin lock code *)
  Definition newlock : val := λ: <>, ref #false.
  Definition acquire : val :=
    rec: "acquire" "l" :=
      if: CAS "l" #false #true then #() else "acquire" "l".
  Definition release : val := λ: "l", "l" <- #false.

  Definition client : val :=
    λ: "l", "acquire" "l" ;; "release" "l".

  (* Definition program : val := *)
  Definition alloc_lock_unlock_par2: expr :=
    let: "l" := "newlock" #() in
    (* "client" "l" ||| "client" "l".  *)
    ((Fork ("client" "l") ) ;; (Fork ("client" "l") )).

End SpinlockCode.

Section SpinlockModel.
  
  (* Used as a role and piece of state *)
  Inductive thread_index := ti0 | ti1 | ti2.

  Instance ti_eqdec: EqDecision thread_index.
  Proof. solve_decision. Qed.

  Instance ti_countable: Countable thread_index. 
  Proof.    
    refine ({|
               encode ti := match ti with | ti0 => 1 | ti1 => 2 | ti2 => 3 end;
               decode n := match n with | 1 => Some ti0 | 2 => Some ti1
                                   | 3 => Some ti2 | _ => None
                           end
             |})%positive.
    intros yn. by destruct yn.
  Qed.

  Instance ti_inhabited: Inhabited thread_index.
  Proof. exact (populate ti0). Qed.


  (* Definition spinlock_state := (nat * thread_index)%type.     *)

  (* Inductive spinlock_model_step *)
  (*   : spinlock_state -> option thread_index -> spinlock_state -> Prop := *)
  (* | sm_alloc: *)
  (*     spinlock_model_step (6, ti0) (Some ti0) (5, ti0) *)
  (* | sm_lock_first (ti: thread_index) (TI12: (not (ti = ti0))) *)
  (*            (* (TI12: (ti <> ti0)%type_scope) *) *)
  (*   : *)
  (*     spinlock_model_step (5, ti0) (Some ti) (4, ti) *)
  (* | sm_unlock_first (ti: thread_index) (TI12: (not (ti = ti0))): *)
  (*     spinlock_model_step (4, ti) (Some ti) (3, ti) *)

  (* See paper notes *)
  Definition spinlock_state := (option thread_index * list thread_index)%type.

  Inductive spinlock_model_step
    : spinlock_state -> option thread_index -> spinlock_state -> Prop :=
  | sm_unlock ti tis_rem: (* also used as the first transition *)
      spinlock_model_step (Some ti, tis_rem) (Some ti) (None, tis_rem)
  (* | sm_lock ti tis_rem (IN: In ti tis_rem): *)
  (*     let rm_ti := filter (fun ti' => negb (ti_eqb ti ti')) tis_rem in *)
  (*     spinlock_model_step (None, tis_rem) (Some ti) (Some ti, rm_ti) *)
  | sm_lock ti tis' tis'':
      let tis := tis' ++ [ti] ++ tis'' in
      spinlock_model_step (None, tis) (Some ti) (Some ti, tis' ++ tis'')
  | sm_wait ti ti' tis_rem (NEQ: not (ti = ti')) (IN: In ti' tis_rem):
      spinlock_model_step (Some ti, tis_rem) (Some ti') (Some ti, tis_rem)
  .

  (* Definition spinlock_live_roles (st: spinlock_state): gset spinlock_state := *)
  (*   match st with *)
  (*   | (cur, tis_rem) => *)
  (*     (match cur with | Some ti => {[ ti ]} | None => ∅ end) ∪ (list_to_set tis_rem) *)
  (*   end. *)
     
  (* Definition the_model: FairModel. *)
  (* Proof. *)
  (*   refine({| *)
  (*             fmstate := nat * bool * bool * bool; *)
  (*             fmrole := YN; *)
  (*             fmtrans := yntrans; *)
  (*             live_roles nb := *)
  (*               match nb with *)
  (*               | (_, _, yf, nf) => (if yf then {[ Y ]} else ∅) ∪ (if nf then {[ No ]} else ∅) *)
  (*               end; *)
  (*             fuel_limit _ := 45%nat; *)
  (*             fm_live_spec := live_spec_holds; *)
  (*           |}). *)
  (*   intros ρ' [[[? ?] ?] ?] ρ [[[? ?] ?] ?] Htrans Hin Hneq. *)
  (*   inversion Htrans; destruct ρ; try set_solver. *)
  (* Defined. *)

  Definition spinlock_model: FairModel.
  Proof.
    refine ({|
        fmstate := spinlock_state; 
        fmrole := thread_index;
        fmtrans := spinlock_model_step;
        live_roles st :=
          match st with
          | (cur, tis_rem) =>
            (match cur with | Some ti => {[ ti ]} | None => ∅ end) ∪
            (list_to_set tis_rem)
          end;
        fuel_limit _ := 10%nat; (* don't know yet *)
             |}).
    { do 2 econstructor. }
    { intros s ρ s' STEP. inversion STEP; subst.
      2, 3: by apply elem_of_union_r, elem_of_list_to_set, elem_of_list_In.
      by apply elem_of_union_l, elem_of_singleton_2. }
    { intros ρ' s ρ s' STEP ENρ' NEQ. inversion STEP; subst.
      - apply elem_of_union in ENρ' as [EQ | ?].
        + destruct NEQ. symmetry. eapply elem_of_singleton_1; eauto.
        + by apply elem_of_union_r.
      - apply elem_of_union_r. subst rm_ti. apply elem_of_list_to_set.
        apply elem_of_list_In, filter_In. split.
        + apply elem_of_union in ENρ' as [C%not_elem_of_empty | ?].
          * destruct C. 
          [edestruct C|].
          * 

End SpinlockModel. 

Section SpinlockCMRA.
  (* Class lockG Σ := lock_G :> inG Σ (exclR unitR). *)
  
  (* Class spinlockG Σ := SpinlockG { *)
  (*                       (* yes_name: gname; *) *)
  (*                       (* no_name: gname; *) *)
  (*                       (* yes_f_name: gname; *) *)
  (*                       (* no_f_name: gname; *) *)
  (*                       lockG :> inG Σ (excl_authR natO); *)
  (*                     }. *)
  Class spinlockPreG Σ := {
    lockG :> inG Σ (excl_authR natO);
  }.
  
  Definition spinlockΣ : gFunctors :=
    #[ heapΣ the_model; GFunctor (excl_authR natO) ].
  
  Global Instance subG_yesnoΣ {Σ} : subG yesnoΣ Σ → yesnoPreG Σ.
  Proof. solve_inG. Qed.
  
  
End SpinlockCMRA.   

Section proof_start.
  Context `{!heapGS Σ the_model, !yesnoPreG Σ}.
  Let Ns := nroot .@ "spinlock".

  Lemma start_spec tid (N: nat) f (Hf: f > 40):
    {{{ frag_model_is (N, true, true, true) ∗
        has_fuels tid {[ Y; No ]} {[ Y := f; No := f ]} ∗
        ⌜N > 0⌝ }}}
      start #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "[Hst [Hf %HN]] Hkont". unfold start.
    destruct f as [|f]; first lia.

    iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[Y := f; No := f]} {[Y; No]});
      [set_solver | eauto |].
    do 3 iModIntro. iSplitL "Hf".
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iIntros "Hf". simpl.

    destruct f as [|f]; first lia.
    wp_bind (Alloc _).
    iApply (wp_alloc_nostep _ _ _ _ {[Y; No]} {[Y := f; No := f]} with "[Hf]");
      [set_solver | eauto |].
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iIntros "!>" (l) "(Hl & _ & Hf)".


    destruct f as [|f]; first lia.
    iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[Y := f; No := f]} {[Y; No]} True) ;
      [set_solver | eauto | eauto |].
    do 3 iModIntro. iSplitL "Hf".
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iIntros "Hf". simpl.

    destruct f as [|f]; first lia.
    iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[Y := f; No := f]} {[Y; No]} True) ; eauto; first set_solver.
    do 3 iModIntro. iSplitL "Hf".
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iIntros "Hf". simpl.

    (* Allocate the invariant. *)
    iMod (own_alloc (●E N  ⋅ ◯E N)) as (γ_yes_at) "[Hyes_at_auth Hyes_at]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E N  ⋅ ◯E N)) as (γ_no_at) "[Hno_at_auth Hno_at]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E true  ⋅ ◯E true)) as (γ_yes_fin) "[Hyes_fin_auth Hyes_fin]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E true  ⋅ ◯E true)) as (γ_no_fin) "[Hno_fin_auth Hno_fin]".
    { apply auth_both_valid_2; eauto. by compute. }

    pose (the_names := {|
     yes_name := γ_yes_at;
     yes_f_name := γ_yes_fin;
     no_name := γ_no_at;
     no_f_name := γ_no_fin;
    |}).

    iApply fupd_wp.
    iMod (inv_alloc Ns _ (yesno_inv_inner l) with "[-Hkont Hf Hyes_at Hno_at Hyes_fin Hno_fin]") as "#Hinv".
    { iNext. unfold yesno_inv_inner. iExists N, true, true, true.
      iSplit; first done. iFrame. }
    iModIntro.

    wp_bind (Fork _).
    destruct f as [|f]; first lia.
    iApply (wp_fork_nostep _ tid _ _ _ {[ No ]} {[ Y ]} {[Y := f; No := f]} with "[Hyes_at Hyes_fin] [- Hf] [Hf]").
    all: cycle 4.
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=.
      rewrite insert_commute // union_comm_L //. }
    { set_solver. }
    { apply insert_non_empty. }
    { iIntros (tid') "!> Hf". iApply (yes_spec _ _ _ f with "[-]"); eauto; first lia.
      rewrite map_filter_insert; last set_solver.
      rewrite map_filter_insert_not; last set_solver.
      rewrite map_filter_empty insert_empty.
      rewrite has_fuel_fuels. by iFrame "#∗". }

    iIntros "!> Hf".
    rewrite map_filter_insert_not; last set_solver.
    rewrite map_filter_insert; last set_solver.
    rewrite map_filter_empty insert_empty.

    destruct f as [|f]; first lia.
    iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[No := f]} {[No]} True) ; eauto; first set_solver.
    do 3 iModIntro. iSplitL "Hf".
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iModIntro. iIntros "Hf". simpl.

    destruct f as [|f]; first lia.
    iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[No := f]} {[No]} True) ; eauto; first set_solver.
    do 3 iModIntro. iSplitL "Hf".
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iIntros "Hf". simpl.

    destruct f as [|f]; first lia.
    iApply (wp_fork_nostep _ tid _ _ _ ∅ {[ No ]} {[No := f]} with "[Hno_at Hno_fin] [Hkont] [Hf]").
    all: cycle 4.
    { unfold has_fuels_S.  eauto. rewrite union_empty_l_L !fmap_insert fmap_empty //=. }
    { set_solver. }
    { apply insert_non_empty. }
    { iIntros (tid') "!> Hf". iApply (no_spec _ _ _ f with "[-]"); eauto; first lia.
      rewrite map_filter_insert; last set_solver.
      rewrite map_filter_empty insert_empty.
      rewrite has_fuel_fuels. by iFrame "#∗". }

    iNext. iIntros "[Hf _]".
    by iApply "Hkont".
  Qed.
End proof_start.
