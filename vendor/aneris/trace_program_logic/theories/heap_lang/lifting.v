From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trace_program_logic.program_logic Require Export weakestpre adequacy.
From trace_program_logic.fairness Require Export fairness resources fair_termination.
From trace_program_logic.program_logic Require Import ectx_lifting.
From trace_program_logic.heap_lang Require Export lang.
From trace_program_logic.heap_lang Require Import tactics notation.
Set Default Proof Using "Type".

Canonical Structure ModelO (Mdl : FairModel) := leibnizO Mdl.
Canonical Structure RoleO (Mdl : FairModel) := leibnizO (Mdl.(fmrole)).

Class heapGpreS Σ (Mdl : FairModel) := HeapPreG {
  heapGpreS_inv :> invGpreS Σ;
  heapGpreS_gen_heap :> gen_heapGpreS loc val Σ;
  heapGpreS_fairness :> fairnessGpreS Mdl heap_lang Σ;
}.

Class heapGS Σ (Mdl: FairModel) := HeapG {
  heap_inG :> heapGpreS Σ Mdl;

  heap_invGS :> invGS Σ;
  heap_gen_heapGS :> gen_heapGS loc val Σ;

  heap_fairnessGS :> fairnessGS Mdl heap_lang Σ;
}.

Definition heapΣ (Mdl : FairModel) : gFunctors :=
  #[ invΣ; gen_heapΣ loc val; fairnessΣ Mdl heap_lang ].

Global Instance subG_heapPreG {Σ Mdl} :
  subG (heapΣ Mdl) Σ → heapGpreS Σ Mdl.
Proof. constructor; solve_inG. Qed.

Instance heapG_irisG `{!heapGS Σ Mdl} : irisG heap_lang (aux_fair_state Mdl) Σ := {
  state_interp extr auxtr :=
    ((gen_heap_interp (trace_last extr).2.(heap)) ∗ model_state_interp (trace_last extr).1 (trace_last auxtr))%I ;
  fork_post tid := λ _, tid ↦M ∅;
}.

Section adequacy.

Lemma posts_of_empty_mapping `{heapGS Σ Mdl} (e1 e: expr) v (tid : nat) (tp : list expr):
  tp !! tid = Some e ->
  to_val e = Some v ->
  posts_of tp ((λ (_ : val), 0%nat ↦M ∅) ::  (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) tp)))) -∗
  tid ↦M ∅.
Proof.
  intros Hsome Hval. simpl.

  rewrite (big_sepL_elem_of (λ x, x.2 x.1) _ (v, (λ _: val, tid ↦M ∅)) _) //.
  apply elem_of_list_omap.
  exists (e, (λ _: val, tid ↦M ∅)); split; last first.
  - simpl. apply fmap_Some. exists v. split; done.
  - destruct tp as [|e1' tp]; first set_solver. simpl.
    apply elem_of_cons.
    destruct tid as [|tid]; [left|right]; first by simpl in Hsome; simplify_eq.
    apply elem_of_lookup_zip_with. eexists tid, e, _. do 2 split =>//.
    rewrite /locale_of /=.
    rewrite list_lookup_fmap fmap_Some. simpl in Hsome.
    exists (e1 :: take tid tp, e). rewrite drop_0. split.
    + erewrite prefixes_from_lookup =>//.
    + rewrite /locale_of /= take_length_le //.
      assert (tid < length tp)%nat; last lia. by eapply lookup_lt_Some.
Qed.

(* Local Hint Resolve tid_step_tp_length_heap: core. *)

Lemma from_locale_from_lookup tp0 tp tid e :
  from_locale_from tp0 tp tid = Some e <-> (tp !! (tid - length tp0)%nat = Some e ∧ (length tp0 <= tid)%nat).
Proof.
  split.
  - revert tp0 tid. induction tp as [| e1 tp1 IH]; intros tp0 tid.
    { unfold from_locale. simpl. done. }
    unfold from_locale. simpl.
    destruct (decide (locale_of tp0 e1 = tid)).
    + intros ?; simplify_eq. rewrite /locale_of /= Nat.sub_diag.
      split; [done|lia].
    + intros [H Hlen]%IH. rewrite app_length /= in H.
      rewrite app_length /= in Hlen.
      destruct tid as [|tid]; first lia.
      assert (Heq1 : (length tp0 + 1 = S (length tp0))%nat) by lia.
      rewrite Heq1 in Hlen.
      assert (length tp0 ≤ tid)%nat by lia.
      assert (Heq : (S tid - length tp0)%nat = (S ((tid - (length tp0))))%nat) by lia.
      rewrite Heq /=. split.
      * rewrite -H. f_equal. lia.
      * transitivity tid; try lia. assumption.
  - revert tp0 tid. induction tp as [|e1 tp1 IH]; intros tp0 tid.
    { set_solver. }
    destruct (decide (tid = length tp0)) as [-> | Hneq].
    + rewrite Nat.sub_diag /=. intros  [? _]. simplify_eq.
      rewrite decide_True //.
    + intros [Hlk Hlen]. assert (length tp0 < tid)%nat as Hle by lia.
      simpl. rewrite decide_False //. apply IH. split.
      * assert (tid - length tp0 = S ((tid - 1) - length tp0))%nat as Heq by lia.
        rewrite Heq /= in Hlk. rewrite -Hlk app_length /=. f_equal; lia.
      * rewrite app_length /=. apply lt_le_S in Hle. rewrite Nat.add_comm //.
Qed.

Lemma from_locale_lookup tp tid e :
  from_locale tp tid = Some e <-> tp !! tid = Some e.
Proof.
  assert (from_locale tp tid = Some e <-> (tp !! tid = Some e ∧ 0 ≤ tid)%nat) as H; last first.
  { split; intros ?; apply H; eauto. split; [done|lia]. }
  unfold from_locale. replace (tid) with (tid - length (A := expr) [])%nat at 2;
    first apply from_locale_from_lookup. simpl; lia.
Qed.

Theorem simulation_adequacy Σ {Mdl: FairModel} `{!heapGpreS Σ Mdl} (s: stuckness)
           (e1 : expr) σ1 (s1: Mdl):
  (* The model has finite branching *)
  valid_state_evolution_finitary (aux_fair_state Mdl) (λ ex aux, live_tids (trace_last ex) (trace_last aux))→
  live_roles Mdl s1 ≠ ∅ ->
  (* The initial configuration satisfies certain properties *)
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!heapGS Σ Mdl},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         has_fuels (Σ := Σ) 0%nat (Mdl.(live_roles) s1) (gset_to_gmap (fuel_limit s1) (Mdl.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  @continued_simulation
    heap_lang
    (aux_fair_state Mdl)
    (λ ex aux, live_tids (trace_last ex) (trace_last aux))
    (trace_singleton ([e1], σ1))
    (trace_singleton (initial_ls s1 0%nat)).
Proof.
  intros Hfevol Hne H.
  apply (wp_strong_adequacy heap_lang (aux_fair_state Mdl) Σ s
         (λ ex aux, live_tids (trace_last ex) (trace_last aux))); first by eauto.
  iIntros (?) "".
  iMod (gen_heap_init (heap σ1)) as (genheap)" [Hgen _]".
  iMod (model_state_init s1) as (γmod) "[Hmoda Hmodf]".
  iMod (model_mapping_init s1) as (γmap) "[Hmapa Hmapf]".
  iMod (model_fuel_init s1) as (γfuel) "[Hfuela Hfuelf]".
  set (distG :=
         {|
          heap_fairnessGS := {|
                              fairness_model_name := γmod;
                              fairness_model_mapping_name := γmap;
                              fairness_model_fuel_name := γfuel;
                              |}
         |}).

  iMod (H distG) as "Hwp". clear H.
  iSpecialize ("Hwp" with "Hmodf [Hmapf Hfuelf]").
  { rewrite /has_fuels /frag_mapping_is /= map_fmap_singleton. iFrame.
    iAssert ([∗ set] ρ ∈ live_roles Mdl s1, ρ ↦F (fuel_limit s1))%I with "[Hfuelf]" as "H".
    - unfold frag_fuel_is. setoid_rewrite map_fmap_singleton.
      rewrite -big_opS_own //. iApply (own_proper with "Hfuelf").
      rewrite -big_opS_auth_frag. f_equiv. rewrite gset_to_gmap_singletons //.
    - iSplit; first by (iPureIntro; rewrite dom_gset_to_gmap).
      iApply (big_sepS_mono with "H"). iIntros (ρ Hin) "H".
      iExists _. iFrame. iPureIntro. apply lookup_gset_to_gmap_Some. done. }
  iMod "Hwp". iModIntro.
  iExists state_interp, (λ _, 0%nat ↦M ∅)%I, fork_post.
  iSplitR.
  { unfold config_wp. iIntros "!>" (???????) "?". done. }
  iFrame.
  iSplitL "Hmapa Hfuela".
  { iExists {[ 0%nat := (live_roles Mdl s1) ]}. iSplitL "Hfuela".
    - rewrite /auth_fuel_is /= fmap_gset_to_gmap //.
    - rewrite /auth_mapping_is /ls_mapping /= map_fmap_singleton. iFrame; iPureIntro.
      split.
      + intros ρ tid. rewrite lookup_gset_to_gmap_Some.
        setoid_rewrite lookup_singleton_Some.
        split; naive_solver.
      + intros tid Hlocs. rewrite lookup_singleton_ne //.
        unfold locales_of_list in Hlocs. simpl in Hlocs. set_solver. }

  iIntros (ex atr δ3 c3 Hval Hexst Hauxst Hexend Hauxend Hbig).
  iIntros (Hns) "Hsi Hposts".
  destruct ex as [c|ex' tid c'].
  - (* We need to prove that the initial state satisfies the property *)
    destruct atr as [δ|???]; last by inversion Hval. simpl.
    have Heq1 := trace_singleton_ends_in_inv _ _ Hexend.
    have Heq2 := trace_singleton_ends_in_inv _ _ Hauxend.
    have Heq3 := trace_singleton_starts_in_inv _ _ Hexst.
    have Heq4 := trace_singleton_starts_in_inv _ _ Hauxst.
    simplify_eq.
    iApply (fupd_mask_weaken ∅); first set_solver. iIntros "_ !>".
    assert (∀ (ρ : fmrole Mdl) (tid : nat),
               ls_mapping (initial_ls s1 0%nat) !! ρ = Some tid →
               is_Some (([e1], σ1).1 !! tid)) as HA.
    { simpl. intros ρ tid Hsome. apply lookup_gset_to_gmap_Some in Hsome as [??].
      simplify_eq. by eexists _. }
    destruct (to_val e1) as [v1|] eqn:Heq.
    + iSplit.
      { iPureIntro. intros ρ tid Hinit.
        simpl in Hinit. apply lookup_gset_to_gmap_Some in Hinit as [_ <-].
        rewrite /from_locale //. eauto. }
      iIntros (tid e Hsome Hnoval ρ). destruct tid; last done.
      simpl in Hsome. simplify_eq.
      iAssert (0%nat ↦M ∅) with "[Hposts]" as "Hem".
      { rewrite /= Heq /fmap /=. by iDestruct "Hposts" as "[??]". }
      iDestruct "Hsi" as "(_&Hsi)". iDestruct "Hsi" as "(%M&Hfuela&Hmapa&%Hinvmap&%Hsmall&Hmodel)".
      iDestruct (frag_mapping_same 0%nat M with "[Hmapa] Hem") as "%H"; first done.
      iPureIntro. by eapply no_locale_empty.
    + iSplit; iPureIntro.
      { simpl. intros ρ tid Hsome. apply lookup_gset_to_gmap_Some in Hsome as [??].
        simplify_eq. by eexists _. }
      intros tid e Hsome Hval' ρ.
      destruct tid as [|tid]; rewrite /from_locale /= in Hsome; by simplify_eq.
  - (* We need to prove that that the property is preserved *)
    destruct atr as [|atr' ℓ δ]; first by inversion Hval.
    rewrite (trace_singleton_ends_in_inv _ _ Hexend); last exact unit.
    rewrite (trace_singleton_ends_in_inv _ _ Hauxend); last exact unit.
    specialize (Hbig ex' atr' tid ℓ).
    have H: trace_contract (trace_extend ex' tid c') tid ex' by eexists.
    have H': trace_contract (trace_extend atr' ℓ δ) ℓ atr' by eexists.
    destruct (Hbig H H') as (Hlm & Hlt & Hvs & Hts). clear H H' Hbig.

    have H: trace_ends_in ex' (trace_last ex') by eexists.
    have H': trace_ends_in atr' (trace_last atr') by eexists.
    iApply (fupd_mask_weaken ∅); first set_solver. iIntros "_ !>".
    apply (trace_singleton_ends_in_inv (L := unit)) in Hexend.
    apply (trace_singleton_ends_in_inv (L := unit)) in Hauxend.
    simpl in *. simplify_eq.
    iSplit.
    + iPureIntro. intros ρ tid' Hsome. by eapply Hts.
    + iIntros (tid' e Hsome Hnoval ρ). simpl.
      iAssert (tid' ↦M ∅) with "[Hposts]" as "H".
      { destruct (to_val e) as [?|] eqn:Heq; last done.
        iApply posts_of_empty_mapping => //.
        apply from_locale_lookup =>//. }
      iDestruct "Hsi" as "(_&Hsi)". iDestruct "Hsi" as "(%M&Hfuela&Hmapa&%Hinvmap&%Hsmall&Hmodel)".
      iDestruct (frag_mapping_same tid' M with "Hmapa H") as "%Hlk".
      { rewrite /auth_mapping_is. iPureIntro. by eapply no_locale_empty. }
Qed.

Theorem simulation_adequacy_inftraces Σ (Mdl : FairModel) `{!heapGpreS Σ Mdl} (s: stuckness)
        e1 σ1 (s1: Mdl)
        (iex : inf_execution_trace heap_lang)
        (Hvex : valid_inf_exec (trace_singleton ([e1], σ1)) iex)
  :
  (* The model has finite branching *)
  valid_state_evolution_finitary (aux_fair_state Mdl) (λ ex aux, live_tids (trace_last ex) (trace_last aux))→
  live_roles Mdl s1 ≠ ∅ ->
  (∀ `{!heapGS Σ Mdl},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         has_fuels (Σ := Σ) 0%nat (Mdl.(live_roles) s1) (gset_to_gmap (fuel_limit s1) (Mdl.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  exists iatr,
  @valid_inf_system_trace
    _ (aux_fair_state Mdl)
    (@continued_simulation
       heap_lang
       (aux_fair_state Mdl)
       (λ ex aux, live_tids (trace_last ex) (trace_last aux)))
    (trace_singleton ([e1], σ1))
    (trace_singleton (initial_ls s1 0%nat))
    iex
    iatr.
Proof.
  intros Hfin Hlr Hwp.
  eexists.
  eapply produced_inf_aux_trace_valid_inf.
  Unshelve.
  - apply (simulation_adequacy Σ s) => //.
  - done.
Qed.


Notation exaux_traces_match Mdl :=
    (@traces_match (option nat)
                   (@mlabel (@aux_state heap_lang (aux_fair_state Mdl)))
                   (cfg heap_lang)
                   (LiveState Mdl)
                   labels_match
                   live_tids
                   locale_step
                   ls_trans
    ).

Theorem simulation_adequacy_traces Σ (Mdl : FairModel) `{!heapGpreS Σ Mdl} (s: stuckness)
        e1 (s1: Mdl)
        (extr : extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  valid_state_evolution_finitary (aux_fair_state Mdl) (λ ex aux, live_tids (trace_last ex) (trace_last aux))→
  live_roles Mdl s1 ≠ ∅ ->
  (∀ `{!heapGS Σ Mdl},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         has_fuels (Σ := Σ) 0%nat (Mdl.(live_roles) s1) (gset_to_gmap (fuel_limit s1) (Mdl.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  exists auxtr, exaux_traces_match Mdl extr auxtr.
Proof.
  intros Hfin Hlr Hwp.
  have [iatr Hbig] : exists iatr,
      @valid_inf_system_trace
        _ (aux_fair_state Mdl)
        (@continued_simulation
           heap_lang
           (aux_fair_state Mdl)
           (λ ex aux, live_tids (trace_last ex) (trace_last aux)))
        (trace_singleton ([e1], (trfirst extr).2))
        (trace_singleton (initial_ls s1 0%nat))
        (from_trace extr)
        iatr.
  { apply (simulation_adequacy_inftraces Σ Mdl s); eauto.
    eapply from_trace_preserves_validity; eauto; first econstructor.
    simpl. destruct (trfirst extr) eqn:Heq. simplify_eq. f_equal.
    simpl in Hexfirst. rewrite -Hexfirst Heq //. }
  exists (to_trace (initial_ls s1 0%nat) iatr).
  eapply (valid_inf_system_trace_implies_traces_match); eauto.
  - intros ?? Hϕ. by apply continued_simulation_rel in Hϕ.
  - apply from_trace_spec. simpl. destruct (trfirst extr) eqn:Heq. simplify_eq. f_equal.
    simpl in Hexfirst. rewrite -Hexfirst Heq //.
  - apply to_trace_spec.
Qed.

Theorem simulation_adequacy_model_trace Σ (Mdl : FairModel) `{!heapGpreS Σ Mdl} (s: stuckness)
        e1 (s1: Mdl)
        (extr : extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  valid_state_evolution_finitary (aux_fair_state Mdl) (λ ex aux, live_tids (trace_last ex) (trace_last aux))→
  live_roles Mdl s1 ≠ ∅ ->
  (∀ `{!heapGS Σ Mdl},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         has_fuels (Σ := Σ) 0%nat (Mdl.(live_roles) s1) (gset_to_gmap (fuel_limit s1) (Mdl.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  exists auxtr mtr, exaux_traces_match Mdl extr auxtr ∧
               upto_stutter ls_under Ul auxtr mtr.
Proof.
  intros Hfb Hlr Hwp.
  destruct (simulation_adequacy_traces
              Σ Mdl _ e1 s1 extr Hvex Hexfirst Hfb Hlr Hwp) as [auxtr Hmatch].
  destruct (can_destutter_auxtr extr auxtr) as [mtr Hupto] =>//.
  { intros ?? contra. inversion contra. done. }
  eauto.
Qed.

Theorem simulation_adequacy_terminate Σ Mdl `{!heapGpreS Σ Mdl} (s: stuckness)
        e1 (s1: Mdl)
        (extr : extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  fairly_terminating Mdl ->
  (* The model has finite branching *)
  valid_state_evolution_finitary (aux_fair_state Mdl) (λ ex aux, live_tids (trace_last ex) (trace_last aux))→
  live_roles Mdl s1 ≠ ∅ ->
  (∀ `{!heapGS Σ Mdl},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         has_fuels (Σ := Σ) 0%nat (Mdl.(live_roles) s1) (gset_to_gmap (fuel_limit s1) (Mdl.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  intros Hterm Hfb Hlr Hwp Hfair.
  destruct (simulation_adequacy_model_trace
              Σ Mdl _ e1 s1 extr Hvex Hexfirst Hfb Hlr Hwp) as (auxtr&mtr&Hmatch&Hupto).
  destruct (infinite_or_finite extr) as [Hinf|] =>//.
  have Hfairaux := fairness_preserved extr auxtr Hinf Hmatch Hfair.
  have Hvalaux := exaux_preserves_validity extr auxtr Hmatch.
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
  have Htermtr := Hterm mtr Hmtrvalid Hfairm.
  eapply exaux_preserves_termination =>//.
  eapply upto_stutter_finiteness =>//.
Qed.

Theorem simulation_adequacy_terminate_ftm Σ `{FairTerminatingModel Mdl} `{!heapGpreS Σ Mdl} (s: stuckness)
        e1 (s1: Mdl)
        (extr : extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  valid_state_evolution_finitary (aux_fair_state Mdl) (λ ex aux, live_tids (trace_last ex) (trace_last aux))→
  live_roles Mdl s1 ≠ ∅ ->
  (∀ `{!heapGS Σ Mdl},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         has_fuels (Σ := Σ) 0%nat (Mdl.(live_roles) s1) (gset_to_gmap (fuel_limit s1) (Mdl.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  eapply simulation_adequacy_terminate =>//.
  apply fair_terminating_traces_terminate.
Qed.

End adequacy.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
(* Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core. *)

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _) => eapply CmpXchgS : core.
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _) => apply alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Instance rec_atomic s f x e : Atomic s (Rec f x e).
Proof. solve_atomic. Qed.
Instance pair_atomic s v1 v2 : Atomic s (Pair (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance injl_atomic s v : Atomic s (InjL (Val v)).
Proof. solve_atomic. Qed.
Instance injr_atomic s v : Atomic s (InjR (Val v)).
Proof. solve_atomic. Qed.
(** The instance below is a more general version of [Skip] *)
Instance beta_atomic s f x v1 v2 : Atomic s (App (RecV f x (Val v1)) (Val v2)).
Proof. destruct f, x; solve_atomic. Qed.
Instance unop_atomic s op v : Atomic s (UnOp op (Val v)).
Proof. solve_atomic. Qed.
Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance if_true_atomic s v1 e2 : Atomic s (If (Val $ LitV $ LitBool true) (Val v1) e2).
Proof. solve_atomic. Qed.
Instance if_false_atomic s e1 v2 : Atomic s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
Proof. solve_atomic. Qed.
Instance fst_atomic s v : Atomic s (Fst (Val v)).
Proof. solve_atomic. Qed.
Instance snd_atomic s v : Atomic s (Snd (Val v)).
Proof. solve_atomic. Qed.

Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. Qed.

Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
Proof. solve_atomic. Qed.
Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
Proof. solve_atomic. Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof. solve_pure_exec. Qed.
(* Higher-priority instance for [EqOp]. *)
Instance pure_eqop v1 v2 :
  PureExec (vals_compare_safe v1 v2) 1
    (BinOp EqOp (Val v1) (Val v2))
    (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof.
  intros Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. revert Hcompare. solve_pure_exec. }
  rewrite /bin_op_eval /= decide_True //.
Qed.

Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.

Notation "f ⇂ R" := (filter (λ '(k,v), k ∈ R) f) (at level 30).

Lemma own_proper `{inG Σ X} γ (x y: X):
  x ≡ y ->
  own γ x -∗ own γ y.
Proof. by intros ->. Qed.

Lemma auth_fuel_is_proper `{heapGS Σ Mdl} (x y : gmap (fmrole Mdl) nat):
  x = y ->
  auth_fuel_is x -∗ auth_fuel_is y.
Proof. by intros ->. Qed.

Section lifting.
Context `{!heapGS Σ Mdl}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.
Implicit Types tid : nat.


Lemma wp_lift_pure_step_no_fork tid E E' Φ e1 e2 fs R ϕ:
  R ≠ ∅ ->
  PureExec ϕ 1 e1 e2 ->
  ϕ ->
  (|={E}[E']▷=> has_fuels_S tid R fs ∗ ((has_fuels tid R fs) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  intros NnO Hpe Hϕ.
  have Hps: pure_step e1 e2.
  { specialize (Hpe Hϕ). by apply nsteps_once_inv in Hpe. }
  iIntros "H". iApply wp_lift_step; eauto.
  { destruct Hps as [Hred _]. specialize (Hred inhabitant). eapply reducible_not_val; eauto. }
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi".
  iMod "H". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first by destruct Hps as [Hred _].
  iNext. iIntros (e2' σ2 efs Hpstep).
  destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?).
  simplify_eq. iMod "Hclose" as "_". iMod "H" as "[Hfuels Hkont]".
  rewrite !app_nil_r.
  iDestruct "Hsi" as "(Hgh&Hmi)". simpl.
  iMod (update_no_step_enough_fuel with "Hfuels Hmi") as "H"; eauto.
  { econstructor =>//. by apply fill_step. }
  iModIntro.
  iDestruct ("H") as (δ2 ℓ [Hlabels Hvse]) "[Hfuels Hmi]".
  iExists δ2, ℓ. repeat iSplit.
  - iPureIntro. destruct ℓ =>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//. by list_simplifier.
  - rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi".
    iSplit =>//. by iApply "Hkont".
Qed.

(* Lemma wp_lift_pure_step_no_fork_2 tid E E' Φ e1 e2 (fs: gmap (fmrole Mdl) nat) R ϕ: *)
(*   R ≠ ∅ -> *)
(*   PureExec ϕ 1 e1 e2 -> *)
(*   ϕ -> *)
(*   (forall (ρ: fmrole Mdl) (f: nat), fs !! ρ = Some f -> f > 0) -> *)
(*   (|={E}[E']▷=> has_fuels tid R fs ∗ ((has_fuels tid R (fmap (λ (x: nat), (x - 1)%nat) fs)) -∗ WP e2 @ tid; E {{ Φ }})) *)
(*   ⊢ WP e1 @ tid; E {{ Φ }}. *)
(* Proof. *)

Lemma wp_lift_pure_step_no_fork' fs R tid E E' Φ e1 e2:
  R ≠ ∅ ->
  PureExec True 1 e1 e2 ->
  (|={E}[E']▷=> has_fuels_S tid R fs ∗ ((has_fuels tid R fs) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  intros. by iApply wp_lift_pure_step_no_fork.
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole tid E E' Φ e1 e2 ρ f φ:
  PureExec φ 1 e1 e2 -> φ ->
  (|={E}[E']▷=> has_fuel tid ρ (S f) ∗ ((has_fuel tid ρ f) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  iIntros (??) "H". rewrite has_fuel_fuels_S.
  iApply (wp_lift_pure_step_no_fork {[ ρ := f ]} {[ρ]}); eauto; last first.
  rewrite has_fuel_fuels //. set_solver.
Qed.

Lemma wp_lift_pure_step_no_fork_take_step s1 s2 tid E E' fs1 fs2 Φ e1 e2 ρ φ:
  PureExec φ 1 e1 e2 -> φ ->
  valid_new_fuelmap fs1 fs2 s1 s2 ρ ->
  Mdl.(fmtrans) s1 (Some ρ) s2 ->
  (|={E}[E']▷=> frag_model_is s1 ∗ has_fuels tid (dom (gset _) fs1) fs1 ∗
    (frag_model_is s2 -∗ (has_fuels tid (dom (gset _) fs2) fs2 -∗ WP e2 @ tid; E {{ Φ }})))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  iIntros (Hpe Hφ Hval Htrans).
  have Hps: pure_step e1 e2.
  { specialize (Hpe Hφ). by apply nsteps_once_inv in Hpe. }
  iIntros "Hkont".
  iApply wp_lift_step; eauto.
  { destruct (pure_step_safe _ e2 Hps inhabitant) as (?&?&?&?). by eapply val_stuck. }

  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi".
  iMod "Hkont". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first by destruct Hps as [Hred _].
  iNext. iIntros (e2' σ2 efs Hpstep).
  destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?).
  simplify_eq. iMod "Hclose" as "_". iMod "Hkont" as "(Hmod&Hfuels&Hkont)".
  rewrite !app_nil_r.
  iDestruct "Hsi" as "(Hgh&Hmi)". simpl.
  iDestruct (model_agree' with "Hmi Hmod") as %Hmeq.

  iMod (update_step_still_alive _ _ _ _ σ1 σ1 with "Hfuels Hmod Hmi") as "H"; eauto.
  { rewrite Hexend. eauto. }
  { econstructor =>//.
    - rewrite Hexend //=.
    - by apply fill_step. }
  { rewrite Hmeq. apply Hval. }
  iModIntro. iDestruct "H" as (δ2 ℓ [Hlabels Hvse]) "(Hfuels&Hmod&Hmi)".
  iExists δ2, ℓ. repeat iSplit.
  - iPureIntro. destruct ℓ =>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//. by list_simplifier.
  - rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi".
    iSplit =>//. by iSpecialize ("Hkont" with "Hmod Hfuels").
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole_take_step s1 s2 tid E E' (f1 f2: nat) Φ e1 e2 ρ φ:
  PureExec φ 1 e1 e2 -> φ ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  (f2 ≤ s2.(fuel_limit))%nat -> Mdl.(fmtrans) s1 (Some ρ) s2 ->
  ( |={E}[E']▷=> frag_model_is s1 ∗ has_fuel tid ρ f1 ∗
    (frag_model_is s2 -∗ (if decide (ρ ∈ live_roles Mdl s2) then has_fuel tid ρ f2 else tid ↦M ∅) -∗
                                WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  iIntros (Hpe Hφ Hroles Hfl Hmdl).
  rewrite has_fuel_fuels.
  iIntros "H".
  replace ({[ρ]}) with (dom (gset (fmrole Mdl)) ({[ρ := f1]}: gmap _ _)); last by set_solver.
  iApply (wp_lift_pure_step_no_fork_take_step _ _ _ _ _ {[ρ := f1]}
         (if decide (ρ ∈ live_roles Mdl s2) then {[ρ := f2]} else ∅)  with "[H]"); eauto.
  - repeat split.
    + intros ?. rewrite decide_True //. rewrite lookup_singleton //=.
    + set_solver.
    + intros ρ' Hdom. destruct (decide (ρ ∈ live_roles Mdl s2)); set_solver.
    + intros ρ' Hneq Hin. destruct (decide (ρ ∈ live_roles Mdl s2)); set_solver.
    + destruct (decide (ρ ∈ live_roles Mdl s2)); set_solver.
  - iMod "H". do 2 iModIntro. iMod "H" as "(Hmod&Hfuels&Hkont)". iModIntro.
    iFrame "Hmod Hfuels". iIntros "Hmod Hfuels". iApply ("Hkont" with "Hmod [Hfuels]").
    destruct (decide (ρ ∈ live_roles Mdl s2)).
    + rewrite dom_singleton_L. rewrite -has_fuel_fuels //.
    + iDestruct "Hfuels" as "[Hf _]". rewrite dom_empty_L //.
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole' tid E E' Φ e1 e2 ρ f:
  PureExec True 1 e1 e2 ->
  (|={E}[E']▷=> has_fuel tid ρ (S f) ∗ ((has_fuel tid ρ f) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  iIntros (?) "H". rewrite has_fuel_fuels_S.
  iApply (wp_lift_pure_step_no_fork' {[ ρ := f ]} {[ρ]}); last first.
  rewrite has_fuel_fuels //. set_solver.
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork_nostep s tid E e Φ R1 R2 fs (Hdisj: R1 ## R2) (Hnemp: fs ≠ ∅):
  (∀ tid', ▷ (has_fuels tid' R2 (fs ⇂ R2) -∗ WP e @ s; tid'; ⊤ {{ _, tid' ↦M ∅ }})) -∗
     ▷ (has_fuels tid R1 (fs ⇂ R1) ={E}=∗ Φ (LitV LitUnit)) -∗
     has_fuels_S tid (R1 ∪ R2) fs -∗ WP Fork e @ s; tid; E {{ Φ }}.
Proof.
  iIntros "He HΦ Htid". iApply wp_lift_atomic_head_step; [done|].
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "[Hsi Hmi]".
  iMod (update_fork_split R1 R2 _
       (tp1 ++ ectx_language.fill K (Val $ LitV LitUnit) :: tp2 ++ [e]) fs _ _ _ e _ σ1 with "Htid Hmi") as
       (δ2) "(Hfuels2 & Hfuels1 & Hσ & %Hvse)" => //.
  { rewrite -Hloc. rewrite -(language.locale_fill _ _ K). econstructor 1 =>//.
    apply fill_step, head_prim_step. econstructor. }
  { list_simplifier. exists (tp1 ++ fill K #() :: tp2). split; first by list_simplifier.
    rewrite !app_length //=. }
  iModIntro. iSplit. iPureIntro; first by eauto. iNext.
  iIntros (e2 σ2 efs Hstep).
  have [-> [-> ->]] : σ2 = σ1 ∧ efs = [e] ∧ e2 = Val $ LitV LitUnit by inv_head_step.
  iMod ("HΦ" with "Hfuels1") as "HΦ". iModIntro. iExists δ2, (Silent_step tid). iFrame.
  iSplit; first by iPureIntro.
  rewrite big_sepL_singleton. rewrite Hexend /=. iFrame "Hsi".
  iApply "He". by list_simplifier.
Qed.

(** Heap *)
(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_mapsto l v (n : nat) :
  ([∗ map] l' ↦ v ∈ heap_array l (replicate n v), l' ↦ v) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

(* TODO *)

Lemma wp_allocN_seq_nostep s tid E v n R fs:
  R ≠ ∅ ->
  0 < n →
  {{{ has_fuels_S tid R fs }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; tid; E
  {{{ l, RET LitV (LitLoc l); has_fuels tid R fs ∗ [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (HnO Hn Φ) "HfuelS HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "[Hsi Hmi]".
  iModIntro; iSplit; first by eauto.
  iIntros (e2 σ2 efs Hstep). iNext.
  inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hsi")
    as "(Hsi & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id ?Hexend; auto with lia. }
  iMod (update_no_step_enough_fuel _ _ with "HfuelS Hmi") as (δ2 ℓ) "([%Hlabel %Hvse] & Hfuel & Hmi)" =>//.
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists δ2, ℓ. repeat iSplit =>//.
  iFrame "Hmi". iSplitL "Hsi".
  - rewrite Hexend //=.
  - iApply "HΦ". iFrame "Hfuel". iApply big_sepL_sep. iSplitL "Hl".
    + by iApply heap_array_to_seq_mapsto.
    + iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.

Lemma wp_alloc_nostep s tid E v R fs :
  R ≠ ∅ ->
  {{{ has_fuels_S tid R fs }}} Alloc (Val v) @ s; tid; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ ∗ has_fuels tid R fs }}}.
Proof.
  iIntros (? Φ) "HfuelS HΦ". iApply (wp_allocN_seq_nostep with "HfuelS"); auto with lia.
  iIntros "!>" (l) "/= (? & ? & _)". rewrite loc_add_0. by iApply "HΦ"; iFrame.
Qed.

Lemma wp_load_nostep s tid E l q v R fs:
  R ≠ ∅ ->
  {{{ ▷ l ↦{q} v ∗ has_fuels_S tid R fs }}} Load (Val $ LitV $ LitLoc l) @ s; tid; E {{{ RET v; l ↦{q} v ∗ has_fuels tid R fs }}}.
Proof.
  iIntros (? Φ) "[>Hl HfuelS] HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "[Hsi Hmi] !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iMod (update_no_step_enough_fuel with "HfuelS Hmi") as (δ2 ℓ) "([%Hlabels %Hvse] & Hfuel & Hmod)" =>//.
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists _,_. do 2 (iSplit=>//).
  - by destruct Hvse.
  - rewrite Hexend. iFrame "Hsi Hmod". iApply "HΦ". iFrame.
Qed.

Lemma wp_store_nostep s tid E l v' v R fs:
  R ≠ ∅ ->
  {{{ ▷ l ↦ v' ∗ has_fuels_S tid R fs }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ has_fuels tid R fs }}}.
Proof.
  iIntros (? Φ) "[>Hl HfuelS] HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "[Hsi Hmi] !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iMod (update_no_step_enough_fuel with "HfuelS Hmi") as (δ2 ℓ) "([%Hlabels %Hvse] & Hfuel & Hmod)" =>//.
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists _,_. do 2 (iSplit=>//).
  - by destruct Hvse.
  - rewrite Hexend. iFrame "Hsi Hmod". iApply "HΦ". iFrame.
Qed.

Lemma wp_cmpxchg_fail_step_singlerole s tid ρ (f1 f2: nat) s1 s2 E l q v' v1 v2:
  v' ≠ v1 → vals_compare_safe v' v1 → f2 ≤ s2.(fuel_limit) -> Mdl.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  {{{ ▷ l ↦{q} v' ∗ ▷ frag_model_is s1 ∗ ▷ has_fuel tid ρ f1 }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' ∗ frag_model_is s2 ∗
      (if decide (ρ ∈ live_roles Mdl s2) then has_fuel tid ρ f2 else tid ↦M ∅ ) }}}.
Proof.
  iIntros (?? Hfl Htrans ? Φ) "(>Hl & >Hst & >Hfuel1) HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "[Hsi Hmi] !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iDestruct (model_agree' with "Hmi Hst") as %Hmeq.
  rewrite bool_decide_false //.
  rewrite has_fuel_fuels Hexend.
  iMod (update_step_still_alive _ _ _ _ _ _ _ _ _
            (if decide (ρ ∈ live_roles Mdl s2) then {[ ρ := f2 ]} else ∅)
            with "Hfuel1 Hst Hmi") as
        (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hmod)"; eauto.
  - destruct (decide (ρ ∈ live_roles Mdl s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles Mdl s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split.
      { intros ρ' Hin. exfalso. rewrite dom_singleton_L  Hmeq in Hin. set_solver. }
      split; set_solver.
    + repeat (split; set_solver).
  - rewrite -> bool_decide_eq_false_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. destruct Hvse as (?&?&?). split =>//.
      }
    iSplit; first done. iFrame. iApply "HΦ". iFrame.
    destruct (decide (ρ ∈ live_roles Mdl s2)).
    + rewrite has_fuel_fuels dom_singleton_L //.
    + iDestruct "Hfuel" as "[?_]". rewrite dom_empty_L //.
Qed.

Lemma wp_store_step_singlerole s tid ρ (f1 f2: nat) s1 s2 E l v' v:
  (* v' = v1 → *)
  (* vals_compare_safe v' v1 → *)
  f2 ≤ s2.(fuel_limit) ->
  Mdl.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  
  {{{ ▷ l ↦ v' ∗ ▷ frag_model_is s1 ∗ ▷ has_fuel tid ρ f1 }}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ frag_model_is s2 ∗
      (if decide (ρ ∈ live_roles Mdl s2) then has_fuel tid ρ f2 else tid ↦M ∅ ) }}}.
Proof.
  iIntros (Hfl Htrans ? Φ) "(>Hl & >Hst & >Hfuel1) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "[Hsi Hmi] !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iDestruct (model_agree' with "Hmi Hst") as %Hmeq.
  (* rewrite bool_decide_true //. *)
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  rewrite has_fuel_fuels Hexend.
  iMod (update_step_still_alive _ _ _ _ _ _ _ _ _
            (if decide (ρ ∈ live_roles Mdl s2) then {[ ρ := f2 ]} else ∅)
            with "Hfuel1 Hst Hmi") as
        (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hmod)"; eauto.
  - destruct (decide (ρ ∈ live_roles Mdl s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles Mdl s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split.
      { intros ρ' Hin. exfalso. rewrite dom_singleton_L  Hmeq in Hin. set_solver. }
      split; set_solver.
    + repeat (split; set_solver).
  -
    (* rewrite -> bool_decide_eq_true_2 in *; eauto. *)
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. destruct Hvse as (?&?&?). split =>//.
      }
    iSplit; first done. iFrame. iApply "HΦ". iFrame.
    destruct (decide (ρ ∈ live_roles Mdl s2)).
    + rewrite has_fuel_fuels dom_singleton_L //.
    + iDestruct "Hfuel" as "[?_]". rewrite dom_empty_L //.
Qed.


Lemma wp_cmpxchg_suc_step_singlerole s tid ρ (f1 f2: nat) s1 s2 E l v' v1 v2:
  v' = v1 →
  vals_compare_safe v' v1 →
  f2 ≤ s2.(fuel_limit) ->
  Mdl.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  
  {{{ ▷ l ↦ v' ∗ ▷ frag_model_is s1 ∗ ▷ has_fuel tid ρ f1 }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 ∗ frag_model_is s2 ∗
      (if decide (ρ ∈ live_roles Mdl s2) then has_fuel tid ρ f2 else tid ↦M ∅ ) }}}.
Proof.
  iIntros (?? Hfl Htrans ? Φ) "(>Hl & >Hst & >Hfuel1) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "[Hsi Hmi] !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iDestruct (model_agree' with "Hmi Hst") as %Hmeq.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  rewrite has_fuel_fuels Hexend.
  iMod (update_step_still_alive _ _ _ _ _ _ _ _ _
            (if decide (ρ ∈ live_roles Mdl s2) then {[ ρ := f2 ]} else ∅)
            with "Hfuel1 Hst Hmi") as
        (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hmod)"; eauto.
  - destruct (decide (ρ ∈ live_roles Mdl s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles Mdl s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split.
      { intros ρ' Hin. exfalso. rewrite dom_singleton_L  Hmeq in Hin. set_solver. }
      split; set_solver.
    + repeat (split; set_solver).
  - rewrite -> bool_decide_eq_true_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. destruct Hvse as (?&?&?). split =>//.
      }
    iSplit; first done. iFrame. iApply "HΦ". iFrame.
    destruct (decide (ρ ∈ live_roles Mdl s2)).
    + rewrite has_fuel_fuels dom_singleton_L //.
    + iDestruct "Hfuel" as "[?_]". rewrite dom_empty_L //.
Qed.

(* Lemma wp_faa s E l i1 i2 : *)
(*   {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E *)
(*   {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}. *)
(* Proof. *)
(*   iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto. *)
(*   iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?. *)
(*   iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step. *)
(*   iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]". *)
(*   iModIntro. iSplit=>//. iFrame. by iApply "HΦ". *)
(* Qed. *)
End lifting.
