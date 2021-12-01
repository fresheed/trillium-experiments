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

Definition yes_go : val :=
  rec: "yes_go" "n" "b" :=
    (if: CAS "b" #true #false
      then "n" <- !"n" - #1
       else #());;
    if: #0 < !"n"
      then "yes_go" "n" "b"
      else #().

Definition yes : val :=
  λ: "N" "b",
    let: "n" := Alloc "N" in
    yes_go "n" "b".

Definition no_go : val :=
  rec: "no_go" "n" "b" :=
    (if: CAS "b" #false #true
      then "n" <- !"n" - #1
       else #());;
    if: #0 < !"n"
      then "no_go" "n" "b"
      else #().

Definition no : val :=
  λ: "N" "b",
    let: "n" := Alloc "N" in
    no_go "n" "b".

Definition start : val :=
  λ: "N",
    let: "b" := Alloc #true in
    (Fork (yes "N" "b") ;;
    Fork (no "N" "b")).

(** * Definition of the model! *)

Inductive YN := Y | No.

Instance YN_eqdec: EqDecision YN.
Proof. solve_decision. Qed.

Instance YN_countable: Countable YN.
Proof.
  refine ({|
             encode yn := match yn with Y => 1 | No => 2 end;
             decode p := match p with 1 => Some Y | 2 => Some No | _ => None end;
         |})%positive.
  intros yn. by destruct yn.
Qed.

Instance YN_inhabited: Inhabited YN.
Proof. exact (populate Y). Qed.

Inductive yntrans: nat*bool*bool*bool -> option YN -> nat*bool*bool*bool -> Prop :=
| yes_trans n: (n > 0)%nat ->yntrans (n, true, true, true) (Some Y) (n, false, true, true) (* < *)
| yes_fail n: (n > 0)%nat ->yntrans (n, false, true, true) (Some Y) (n, false, true, true) (* ≤ *)
| no_trans n: yntrans (S n, false, true, true) (Some No) (n, true, true, true) (* < *)
| no_trans_end yf: yntrans (1, false, yf, true) (Some No) (0, true, yf, true) (* < *)
| no_fail n: yntrans (n, true, true, true) (Some No) (n, true, true, true) (* ≤ *)
| yes_finish N B nf: (N ≤ 1) -> yntrans (N, B, true, nf) (Some Y) (N, B, false, nf) (* < *)
| no_finish B yf: yntrans (0, B, yf, true) (Some No) (0, B, yf, false). (* < *)

Lemma live_spec_holds:
     forall s ρ s', yntrans s (Some ρ) s' -> ρ ∈ (match s with
                | (_, _, yf, nf) => (if yf then {[ Y ]} else ∅) ∪ (if nf then {[ No ]} else ∅)
              end: gset YN).
Proof.
  intros [[[n ?] yf] nf] yn [[[??] ?] ?] Htrans.
  inversion Htrans; set_solver.
Qed.

Definition the_model: FairModel.
Proof.
  refine({|
            fmstate := nat * bool * bool * bool;
            fmrole := YN;
            fmtrans := yntrans;
            live_roles nb :=
              match nb with
              | (_, _, yf, nf) => (if yf then {[ Y ]} else ∅) ∪ (if nf then {[ No ]} else ∅)
              end;
            fuel_limit _ := 45%nat;
            fm_live_spec := live_spec_holds;
          |}).
  intros ρ' [[[? ?] ?] ?] ρ [[[? ?] ?] ?] Htrans Hin Hneq.
  inversion Htrans; destruct ρ; try set_solver.
Defined.


(** The CMRAs we need. *)
Class yesnoG Σ := YesnoG {
  yes_name: gname;
  no_name: gname;
  yes_f_name: gname;
  no_f_name: gname;
  yesno_n_G :> inG Σ (excl_authR natO);
  yesno_f_G :> inG Σ (excl_authR boolO);
 }.
Class yesnoPreG Σ := {
  yesno_PreG :> inG Σ (excl_authR natO);
  yesno_f_PreG :> inG Σ (excl_authR boolO);
 }.
Definition yesnoΣ : gFunctors :=
  #[ heapΣ the_model; GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ].

Global Instance subG_yesnoΣ {Σ} : subG yesnoΣ Σ → yesnoPreG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ the_model, !yesnoG Σ}.
  (* Context `{!yesnoG Σ}. *)
  Let Ns := nroot .@ "yes_no".

  Definition yes_at (n: nat) := own yes_name (◯E n).
  Definition no_at (n: nat) := own no_name (◯E n).

  Definition auth_yes_at (n: nat) := own yes_name (●E n).
  Definition auth_no_at (n: nat) := own no_name (●E n).

  Definition yes_finished (b: bool) := own yes_f_name (◯E b).
  Definition no_finished (b: bool) := own no_f_name (◯E b).

  Definition auth_yes_finished (b: bool) := own yes_f_name (●E b).
  Definition auth_no_finished (b: bool) := own no_f_name (●E b).

  Lemma they_agree γ (N M: nat):
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  Lemma yes_agree N M:
    yes_at N -∗ auth_yes_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.
  Lemma no_agree N M:
    no_at N -∗ auth_no_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.

  Lemma they_finished_agree γ (N M: bool):
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  Lemma yes_finished_agree N M:
    yes_finished N -∗ auth_yes_finished M -∗ ⌜ M = N ⌝.
  Proof. apply they_finished_agree. Qed.
  Lemma no_finished_agree N M:
    no_finished N -∗ auth_no_finished M -∗ ⌜ M = N ⌝.
  Proof. apply they_finished_agree. Qed.

  Lemma they_update γ (N M P: nat):
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.
  Lemma yes_update P N M:
     auth_yes_at M ∗ yes_at N ==∗ auth_yes_at P ∗ yes_at P.
  Proof. apply they_update. Qed.
  Lemma no_update P N M:
     auth_no_at M ∗ no_at N ==∗ auth_no_at P ∗ no_at P.
  Proof. apply they_update. Qed.

  Lemma they_finished_update γ (N M P: bool):
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.
  Lemma yes_finished_update P N M:
     auth_yes_finished M ∗ yes_finished N ==∗ auth_yes_finished P ∗ yes_finished P.
  Proof. apply they_finished_update. Qed.
  Lemma no_finished_update P N M:
     auth_no_finished M ∗ no_finished N ==∗ auth_no_finished P ∗ no_finished P.
  Proof. apply they_finished_update. Qed.

  Definition yesno_inv_inner b :=
    (∃ N B yf nf,
          ⌜((N > 1 ∨ (N > 0 ∧ B = true)) -> yf = true) ∧ (N > 0 -> nf = true)⌝ ∗
          auth_yes_finished yf ∗ auth_no_finished nf ∗
          frag_model_is (N, B, yf, nf) ∗ b ↦ #B ∗
                           if B
                           then auth_yes_at N ∗ auth_no_at N
                           else auth_yes_at (N-1)%nat ∗ auth_no_at N)%I.
  Definition yesno_inv b := inv Ns (yesno_inv_inner b).

  Lemma yes_go_finish b tid Φ n e':
    (yesno_inv b ∗ yes_finished true ∗ (tid ↦M ∅ -∗ Φ #()) ∗
     yes_at 0 ∗ n ↦ #0 ∗ has_fuel tid Y 21 ) -∗
    WP if: #false then e' else #() @tid {{ v, Φ v }}.
  Proof.
    iIntros "(#INV & YES_FIN_FRAG & Kont & YES_AT_FRAG & nN & Fρ)".
    (* iApply wp_atomic. *)
    iInv Ns as (M B yf nf) "(>[%YF %NF'] & >YES_FIN_AUTH & >NO_FIN_AUTH & >ST & >bB & B_AUTHS)" "Clos".
    
    destruct B.
    - (* b -> true, Y thread can finish *)
      iDestruct "B_AUTHS" as "[>YES_AT_AUTH >NO_AT_AUTH]".
      iDestruct (yes_agree with "YES_AT_FRAG YES_AT_AUTH") as %->.
      iDestruct (yes_finished_agree with "YES_FIN_FRAG YES_FIN_AUTH") as %->.

      iApply (wp_lift_pure_step_no_fork_singlerole_take_step
                ((0, true, true, nf): fmstate the_model) (0, true, false, nf) _ _ _ _ 0
                 ); eauto.
      { set_solver. }
      { lia. }
      { econstructor. lia. }
      iFrame. iModIntro.
      iMod (yes_finished_update false with "[$]") as "[YES_FIN_AUTH YES_FIN_FRAG]".
      iModIntro. iNext. iModIntro.
      iIntros "ST".
      
      rewrite -wp_value.

      rewrite decide_False.
      2: { destruct nf; simpl; set_solver. }
      iIntros "TID_EMP". 
      
      iApply "Kont". iFrame.
      iMod ("Clos" with "[-]"); [| done].
      rewrite /yesno_inv_inner. do 4 iExists _. iFrame. iPureIntro. lia.
      
    - (* b -> false, finish as well *)
      (* what is the difference with previous case? *)
      iDestruct "B_AUTHS" as "[>YES_AT_AUTH >NO_AT_AUTH]".
      iDestruct (yes_agree with "YES_AT_FRAG YES_AT_AUTH") as %Heq. 
      iDestruct (yes_finished_agree with "YES_FIN_FRAG YES_FIN_AUTH") as %->.
      
      iApply (wp_lift_pure_step_no_fork_singlerole_take_step
                ((M, false, true, nf): fmstate the_model) (M, false, false, nf) _ _ _ _ 0
             ); eauto.
      { set_solver. }
      { lia. }
      { econstructor. lia. }
      
      iFrame. iModIntro.
      iMod (yes_finished_update false with "[$]") as "[YES_FIN_AUTH YES_FIN_FRAG]".
      iModIntro. iNext. iModIntro.
      iIntros "ST".

      rewrite -wp_value.

      rewrite decide_False.
      2: { destruct nf; simpl; set_solver. }
      iIntros "TID_EMP".
      
      iApply "Kont". iFrame.
      iMod ("Clos" with "[-]"); [| done].
      rewrite /yesno_inv_inner. do 4 iExists _. iFrame. iPureIntro.
      split; auto. lia. 
Qed. 
    

  
  Lemma yes_go_spec tid n b (N: nat) f (FUELS: f > 17):
    {{{ yesno_inv b ∗ has_fuel tid Y f ∗ n ↦ #N ∗ ⌜N > 0⌝ ∗ yes_at N ∗ yes_finished true }}}
      yes_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "IH" forall (N f FUELS).
                   
    iIntros (Φ) "(#INV & FUELS & nN & %HN & YES_AT_FRAG & YES_FIN_FRAG) Kont".
    
    unfold yes_go.
    
    destruct f as [|f]; first lia. my_pure "FUELS".
    destruct f as [|f]; first lia. my_pure "FUELS".
    destruct f as [|f]; first lia. my_pure "FUELS".
    
    fold yes_go.
    
    wp_bind (CmpXchg _ _ _).

    remember (fun v : val => @wp heap_lang (uPred (iResUR Σ)) _ _ _ _ _ _ _)
      as yes_go_body_wp.
    
    
    assert (∀ s, Atomic s (CmpXchg #b #true #false)).
    { apply _. }

    iApply wp_atomic. 

    iInv Ns as (M B yf nf) "(>[%FIN_YES %FIN_NO] & >YES_FIN_AUTH & >NO_FIN_AUTH & >ST & >bB & B_AUTHS)" "Clos".
    iDestruct (yes_finished_agree with "YES_FIN_FRAG YES_FIN_AUTH") as %->.
    destruct B; iDestruct "B_AUTHS" as "[>YES_AT_AUTH >NO_AT_AUTH]".
    - (* 'yes' can progress: b = 1, N = M *)
      iDestruct (yes_agree with "YES_AT_FRAG YES_AT_AUTH") as "%Heq".
      rewrite -> Heq in *. clear Heq.
      rewrite (FIN_NO HN).

      iApply (wp_cmpxchg_suc_step_singlerole _ tid (Y: fmrole the_model) _ 30%nat
                                             (N, true, true, true) (N, false, true, true)
             with "[$]"); eauto.
      { simpl. lia. }
      { econstructor. lia. }
      
      iModIntro. simpl. 
      iIntros "!> (B & ST & Fρ)".
      iMod (yes_update (N-1) with "[$]") as "[YES_AT_AUTH YES_AT_FRAG]".
      rewrite /yesno_inv_inner. 
      iMod ("Clos" with "[ST B YES_FIN_AUTH NO_FIN_AUTH NO_AT_AUTH YES_AT_AUTH]").
      { iNext. iExists N, false, true, true. iFrame. iPureIntro; intros; lia. }
      (* simpl. *)
      
      destruct N as [|N]; first lia.
      rewrite decide_True. 
      2: { destruct N; set_solver. }

      subst yes_go_body_wp. 
      my_pures "Fρ".

      my_ld "[nN Fρ]".
      my_pures "Fρ".
      my_st "[nN Fρ]".
      my_pures "Fρ".
      my_ld "[nN Fρ]".
      my_pures "Fρ".
      
      destruct (decide (0 < S N - 1)) as [GT|LE].
      + rewrite bool_decide_eq_true_2 //; last lia.
        
        my_pure "Fρ".
        
        iApply ("IH" with "[] [Fρ nN YES_AT_FRAG YES_FIN_FRAG] [$]"); last first.
        { iFrame "∗#". iSplit; last (iPureIntro; lia).
          replace (#(N - 0)%nat) with (#(S N - 1)); first done.
          do 2 f_equal. lia. }
        { iPureIntro. auto. }
      + rewrite bool_decide_eq_false_2 //; last lia.
        have ->: N = 0 by lia. simpl.
        iApply (yes_go_finish b tid Φ). iFrame. done.  
    - (* b -> false, 'yes' stutters *)
      iDestruct (yes_agree with "YES_AT_FRAG YES_AT_AUTH") as "%M_".
      rewrite -> M_ in *.
      (* have Mnz: M > 0 by lia. *)
      (* rewrite (Htrue' HM). *)
      rewrite FIN_NO; [| lia].
      
      iApply (wp_cmpxchg_fail_step_singlerole _ tid (Y: fmrole the_model) _ 30%nat
                                             (M, false, true, true) (M, false, true, true)
             with "[$]"); eauto.
      { simpl. lia. }
      { econstructor. lia. }
      iIntros "!>!> (B & ST & Fρ)".
      (* iMod (yes_update (N-1) with "[$]") as "[Hay Hyes]". *)
      iMod ("Clos" with "[ST B YES_AT_AUTH NO_AT_AUTH NO_FIN_AUTH YES_FIN_AUTH]").
      { iNext. iExists M, false, true, true. rewrite M_. iFrame. iPureIntro; intros; lia. }
      simpl.

      destruct N as [|N]; first lia. rewrite decide_True; last first.
      { destruct N; set_solver. }

      subst yes_go_body_wp. my_pures "Fρ".
      my_ld "[nN Fρ]".

      do 2 (my_pure "Fρ").

      iApply ("IH" with "[] [-Kont] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  Qed.

  Lemma yes_spec tid b (N: nat) f (Hf: f > 25):
    {{{ yesno_inv b ∗ has_fuel tid Y f ∗ ⌜N > 0⌝ ∗ yes_at N ∗ yes_finished true }}}
      yes #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#INV & FUELS & %Npos & YES_AT_FRAG & YES_FIN_FRAG) Kont".
    unfold yes.

    do 3 (destruct f as [|f]; [lia | my_pure "Hf"]). 

    destruct f as [|f]; [lia| ].   
    wp_bind (Alloc _).

    iApply (wp_alloc_nostep _ _ _ _ {[Y]} with "[Hf]"); first set_solver.
    { by rewrite has_fuel_fuels_S. }
    iNext. iIntros (l) "(LN & _ & Hf)".
    rewrite -has_fuel_fuels.

    do 2 (destruct f as [|f]; [lia| my_pure "Hf"]). 

    iApply (yes_go_spec with "[-Kont]"); try iFrame.
    { lia. }
    { iFrame "INV". done. }
  Qed.

  (* Lemma no_go_spec tid n b (N: nat) f (Hf: f > 17): *)
  (*   {{{ yesno_inv b ∗ has_fuel tid No f ∗ n ↦ #N ∗ ⌜N > 0⌝ ∗ no_at N ∗ no_finished true }}} *)
  (*     no_go #n #b @ tid *)
  (*   {{{ RET #(); tid ↦M ∅ }}}. *)

  Lemma no_spec tid b (N: nat) f (Hf: f > 25):
    {{{ yesno_inv b ∗ has_fuel tid No f ∗ ⌜N > 0⌝ ∗ no_at N ∗ no_finished true }}}
      no #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof. Admitted. 

End proof.


Section proof_start.
  Context `{!heapGS Σ the_model, !yesnoPreG Σ}.
  Let Ns := nroot .@ "yes_no".

  (* Lemma start_spec tid (N: nat) f (Hf: f > 40): *)
  (*   {{{ frag_model_is (N, true, true, true) ∗ *)
  (*       has_fuels tid {[ Y; No ]} {[ Y := f; No := f ]} ∗ *)
  (*       ⌜N > 0⌝ }}} *)
  (*     start #N @ tid *)
  (*   {{{ RET #(); tid ↦M ∅ }}}. *)
  (* Proof using All. *)
  (*   iIntros (Φ) "[Hst [Hf %HN]] Hkont". unfold start. *)
  (*   destruct f as [|f]; first lia. *)

  (*   iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[Y := f; No := f]} {[Y; No]}); *)
  (*     [set_solver | eauto |]. *)
  (*   do 3 iModIntro. iSplitL "Hf". *)
  (*   { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. } *)

  Lemma start_spec tid (N: nat) f (BOUND_F: f > 40):
    {{{ frag_model_is (N, true, true, true) ∗
        has_fuels tid {[ Y; No ]} {[ Y := f; No := f ]} ∗
        ⌜N > 0⌝ }}}
      start #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "[MODEL [FUELS %NZ_F]] Kont". unfold start.
    destruct f as [|f']; first lia.

    iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[Y := f'; No := f']} {[Y; No]}).
    { set_solver. }
    { done. }

    (* do 3 iModIntro. *)
    iModIntro. (* ? *)
    iModIntro. iModIntro.
    
    iSplitL "FUELS".
    { unfold has_fuels_S. rewrite !fmap_insert fmap_empty //=. }
    
    iIntros "FUELS". simpl.

    destruct f' as [|f'']; first lia. 
    wp_bind (Alloc _).
    iApply (wp_alloc_nostep _ _ _ _ {[Y; No]} {[Y := f''; No := f'']} with "[FUELS]"). 
    { set_solver. }
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iIntros "!>" (l) "(Lt & _ & FUELS)".


    destruct f'' as [|f]; first lia.
    iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[Y := f; No := f]} {[Y; No]} True) ;
      [set_solver | eauto | eauto |].
    do 3 iModIntro. iSplitL "FUELS".
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iIntros "FUELS". simpl.

    destruct f as [|f]; first lia.
    iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[Y := f; No := f]} {[Y; No]} True) ; eauto; first set_solver.
    do 3 iModIntro. iSplitL "FUELS".
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iIntros "FUELS". simpl.

    (* Allocate the invariant. *)
    iMod (own_alloc (●E N  ⋅ ◯E N)) as (γ_yes_at) "[YES_AT_AUTH YES_AT_FRAG]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E N  ⋅ ◯E N)) as (γ_no_at) "[NO_AT_AUTH NO_AT_FRAG]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E true  ⋅ ◯E true)) as (γ_yes_fin) "[YES_FIN_AUTH YES_FIN_FRAG]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E true  ⋅ ◯E true)) as (γ_no_fin) "[NO_FIN_AUTH NO_FIN_FRAG]".
    { apply auth_both_valid_2; eauto. by compute. }

    pose (the_names := {|
     yes_name := γ_yes_at;
     yes_f_name := γ_yes_fin;
     no_name := γ_no_at;
     no_f_name := γ_no_fin;
    |}).

    iApply fupd_wp.
    iMod (inv_alloc Ns _ (yesno_inv_inner l) with "[-Kont FUELS YES_AT_FRAG NO_AT_FRAG YES_FIN_FRAG NO_FIN_FRAG]") as "#Hinv".
    { iNext. unfold yesno_inv_inner. iExists N, true, true, true.
      iSplit; first done. iFrame. }
    iModIntro.

    wp_bind (Fork _).
    destruct f as [|f]; first lia.
    iApply (wp_fork_nostep _ tid _ _ _ {[ No ]} {[ Y ]} {[Y := f; No := f]} with "[YES_AT_FRAG YES_FIN_FRAG] [-FUELS] [FUELS]").
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

    iIntros "!> FUELS".
    rewrite map_filter_insert_not; last set_solver.
    rewrite map_filter_insert; last set_solver.
    rewrite map_filter_empty insert_empty.

    destruct f as [|f]; first lia.
    iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[No := f]} {[No]} True) ; eauto; first set_solver.
    do 3 iModIntro. iSplitL "FUELS".
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iModIntro. iIntros "FUELS". simpl.

    destruct f as [|f]; first lia.
    iApply (wp_lift_pure_step_no_fork tid _ _ _ _ _ {[No := f]} {[No]} True) ; eauto; first set_solver.
    do 3 iModIntro. iSplitL "FUELS".
    { unfold has_fuels_S.  eauto. rewrite !fmap_insert fmap_empty //=. }
    iIntros "FUELS". simpl.

    destruct f as [|f]; first lia.
    iApply (wp_fork_nostep _ tid _ _ _ ∅ {[ No ]} {[No := f]} with "[NO_AT_FRAG NO_FIN_FRAG] [Kont] [FUELS]").
    all: cycle 4.
    { unfold has_fuels_S.  eauto. rewrite union_empty_l_L !fmap_insert fmap_empty //=. }
    { set_solver. }
    { apply insert_non_empty. }
    { iIntros (tid') "!> Hf". iApply (no_spec _ _ _ f with "[-]"); eauto; first lia.
      rewrite map_filter_insert; last set_solver.
      rewrite map_filter_empty insert_empty.
      rewrite has_fuel_fuels. by iFrame "#∗". }

    iNext. iIntros "[Hf _]".
    by iApply "Kont".
  Qed.
End proof_start.
