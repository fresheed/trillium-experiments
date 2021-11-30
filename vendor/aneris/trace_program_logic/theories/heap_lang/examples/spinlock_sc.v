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

(* Section SpinlockCode. *)

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

(* End SpinlockCode. *)

(* Section SpinlockModel. *)
  
  (* Used as a role and piece of state *)
  Inductive thread_index := ti0 | ti1 | ti2.

  Global Instance ti_eqdec: EqDecision thread_index.
  Proof. solve_decision. Qed.

  Global Instance ti_countable: Countable thread_index. 
  Proof.    
    refine ({|
               encode ti := match ti with | ti0 => 1 | ti1 => 2 | ti2 => 3 end;
               decode n := match n with | 1 => Some ti0 | 2 => Some ti1
                                   | 3 => Some ti2 | _ => None
                           end
             |})%positive.
    intros yn. by destruct yn.
  Qed.

  Global Instance ti_inhabited: Inhabited thread_index.
  Proof. exact (populate ti0). Qed.

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
    { intros s ρ s' STEP. inversion STEP; subst.
      - by apply elem_of_union_l, elem_of_singleton_2.
      - subst tis0; apply elem_of_union_r, elem_of_list_to_set, elem_of_list_In; rewrite !in_app_iff; simpl; tauto. 
      -  by apply elem_of_union_r, elem_of_list_to_set, elem_of_list_In. }
    { intros ρ' s ρ s' STEP ENρ' NEQ. inversion STEP; subst; auto. 
      - apply elem_of_union in ENρ' as [EQ | ?].
        + by apply elem_of_singleton_1 in EQ. 
        + by apply elem_of_union_r.
      - apply elem_of_union in ENρ' as [C%not_elem_of_empty | IN].
        { by destruct C. }
        subst tis tis0. apply elem_of_union_r. rewrite list_to_set_app.
        repeat rewrite list_to_set_app in IN * => IN. (* TODO: syntax? *)
        rewrite (union_comm (list_to_set [ρ]))  in IN  * => IN. 
        rewrite union_assoc in IN * => IN.
        apply elem_of_union in IN as [? | IN]; auto.
        by apply elem_of_list_to_set, elem_of_list_singleton in IN. }
  Defined. 
        
(* End SpinlockModel.  *)

(* Section SpinlockCMRA. *)

  Class spinlockPreG Σ := {
    lock_preG :> inG Σ (exclR unitR);
    cur_G :> inG Σ (excl_authR (optionO natO));
    (* rems_G :> inG Σ (excl_authR boolO); *)
  }.
  
  Class spinlockG Σ := {
    lockG :> inG Σ (exclR unitR);

    cur_name: gname;
    rems_name: gname
  }.
   
  Definition spinlockΣ : gFunctors :=
    #[ heapΣ spinlock_model; GFunctor (exclR unitR) ].
  
  Global Instance subG_spinlockΣ {Σ} : subG spinlockΣ Σ → spinlockPreG Σ.
  Proof. solve_inG. Qed.
    
(* End SpinlockCMRA.    *)

Section proof_start.
  Context `{!heapGS Σ spinlock_model, !spinlockPreG Σ}.
  Let Ns := nroot .@ "spinlock".

  (* (* The lock invariant *) *)
  (* Definition is_lock γ (v : val) (P: iProp Σ) := *)
  (*   (∃ (ℓ : loc), ⌜v = #ℓ⌝ ∧ inv (lockN v) (ℓ ↦ #false ∗ P ∗ locked γ ∨ ℓ ↦ #true))%I. *)

  (* (* The is_lock predicate is persistent *) *)
  (* Global Instance is_lock_persistent γ l Φ : Persistent (is_lock γ l Φ). *)
  (* Proof. *)
  (*   (* Print Hint *.  *) *)
  (*   (* what does this syntax mean? *) *)
  (*   (* apply _. Show Proof. *) *)
  (*   unfold is_lock. apply bi.exist_persistent. intros lc. *)
  (*   apply bi.and_persistent. *)
  (*   - apply bi.pure_persistent.  *)
  (*   - apply inv_persistent. *)
  (* Qed. *)

  Definition locked (γ: gname): iProp Σ := own γ (Excl ()).
  
  Definition cur_auth (n: nat) := own yes_name (●E n).
  Definition cur_frag (b: bool) := own yes_f_name (◯E b).
  Definition no_finished (b: bool) := own no_f_name (◯E b).

  Definition auth_yes_finished (b: bool) := own yes_f_name (●E b).
  Definition auth_no_finished (b: bool) := own no_f_name (●E b).


  Definition spinlock_inv_impl l γ P : iProp Σ :=
    ∃ ti_opt tis,
      (frag_model_is (ti_opt, tis) ∗
       (l ↦ #false ∗ P ∗ locked γ ∗ ⌜ti_opt = None⌝
        ∨ l ↦ #true ∗ (∃ ti, ⌜ti_opt = Some ti /\ not (In ti tis)⌝)))%I.

  Definition spinlock_inv l γ P :=
      inv Ns (spinlock_inv_impl l γ P).

  Lemma acquire_terminates tid l γ P f (FUEL: f > 10) ti:
    {{{ spinlock_inv l γ P ∗ has_fuel tid ti f }}}
      acquire #l @ tid
    {{{ RET #(); tid ↦M ∅  }}}.
  Proof.
    iLöb as "IH" forall (f FUEL). 
    iIntros (Φ) "(#INV & FUEL) Kont".
    rewrite {2}/acquire.

    destruct f; [lia| ].
    iApply wp_lift_pure_step_no_fork_singlerole; [done| ]. fold acquire.
    do 3 iModIntro. iFrame.
    iIntros "FUEL". simpl.

    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic. 
    iInv Ns as (ti_opt tis) "[>ST LOCK]" "Clos".
      rewrite {1}/lock_inv_impl {1}/model_inv_impl.
    iDestruct "LOCK" as "[LOCK|LOCK]". 
    - 
    
  Lemma client_terminates tid l γ P sst f (FUEL: f > 10) ti:
    {{{ spinlock_inv l γ P sst ∗ has_fuel tid ti f }}}
      client #l @ tid
    {{{ RET #(); tid ↦M ∅  }}}.
  Proof.
    iIntros (Φ) "(#INV & FUEL) Kont".
    rewrite /client. 
    
  
  Lemma program_spec tid f (Hf: f > 10):
    {{{ frag_model_is (Some ti0, [ti1; ti2]) ∗
        has_fuels tid {[ ti0; ti1; ti2 ]} {[ ti0 := f; ti1 := f; ti2 := f ]}
    }}}
        alloc_lock_unlock_par2 @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    
  Qed.
  
End proof_start.
