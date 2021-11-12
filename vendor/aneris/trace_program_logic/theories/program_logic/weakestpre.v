From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From trace_program_logic.program_logic Require Export language traces.
From trace_program_logic.bi Require Export weakestpre.

Class irisG (Λ : language) (AS : AuxState Λ) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS Σ;

  (** The state interpretation is an invariant that should hold in between each
  step of reduction. Here [Λstate] is the global state, [list Λobservation] are
  the remaining observations, and [nat] is the number of forked-off threads
  (not the total number of threads, which is one higher because there is always
  a main thread). *)
  state_interp : execution_trace Λ → auxiliary_trace AS → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : locale Λ → val Λ → iProp Σ;
}.
Global Opaque iris_invGS.

Definition wp_pre `{!irisG Λ AS Σ} (s : stuckness)
    (wp : coPset -d> locale Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> locale Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E ζ e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ (extr : execution_trace Λ) (atr : auxiliary_trace AS) K tp1 tp2 σ1,
      ⌜valid_exec extr⌝ -∗
      ⌜locale_of tp1 (ectx_fill K e1) = ζ⌝ -∗
      ⌜trace_ends_in extr (tp1 ++ ectx_fill K e1 :: tp2, σ1)⌝ -∗
      state_interp extr atr ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs,
         ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅}=∗ ▷ |={∅,E}=>
         ∃ δ2 ℓ,
           ⌜valid_state_evolution extr atr (Some ζ) ℓ (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2) δ2⌝ ∗
           state_interp
             (trace_extend extr (Some ζ) (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2))
             (trace_extend atr ℓ δ2) ∗
           wp E ζ e2 Φ ∗
           [∗ list] i ↦ ef ∈ efs,
              wp ⊤ (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) ef
                (fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef))
  end%I.

Local Instance wp_pre_contractive `{!irisG Λ AS Σ} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre=> n wp wp' Hwp E e1 ζ Φ /=.
  destruct to_val; first done.
  repeat apply bi.forall_ne =>?.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp_def `{!irisG Λ AS Σ} : Wp Λ (iProp Σ) stuckness :=
  λ s : stuckness, fixpoint (wp_pre s).
Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Arguments wp' {Λ AS Σ _}.
Existing Instance wp'.
Lemma wp_eq `{!irisG Λ AS Σ} : wp = @wp_def Λ AS Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!irisG Λ AS Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types ζ : locale Λ.

(* Weakest pre *)
Lemma wp_unfold s E e ζ Φ :
  WP e @ s; ζ; E {{ Φ }} ⊣⊢ wp_pre s (wp (PROP:=iProp Σ) s) E ζ e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold (wp_pre s)). Qed.

Global Instance wp_ne s E ζ e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E ζ e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre.
  destruct to_val; first by f_equiv; apply HΦ.
  repeat apply bi.forall_ne =>?.
  repeat ((f_contractive || f_equiv); try apply IH); eauto.
  eapply dist_le; eauto with lia.
Qed.
Global Instance wp_proper s E ζ e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E ζ e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Global Instance wp_contractive s E ζ e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E ζ e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He.
  repeat apply bi.forall_ne =>?.
  by repeat (f_contractive || f_equiv).
Qed.

Lemma wp_value' s E ζ Φ v : Φ v ⊢ WP of_val v @ s; ζ; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre to_of_val. auto. Qed.
Lemma wp_value_inv' s E ζ Φ v : WP of_val v @ s; ζ; E {{ Φ }} ={E}=∗ Φ v.
Proof. by rewrite wp_unfold /wp_pre to_of_val. Qed.

Lemma wp_strong_mono s1 s2 E1 E2 ζ e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; ζ; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; ζ; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e ζ E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hloc Hexe) "Hsi".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[//] [//] [//] [$]") as "[% H]".
  iModIntro. iSplit; [by iPureIntro; destruct s1, s2|].
  iIntros (e2 σ2 efs Hstep).
  iMod ("H" with "[//]") as "H". iIntros "!> !>".
  iMod "H" as (δ2 ℓ) "(Hsv & Hσ & H & Hefs)".
  iMod "Hclose" as "_". iModIntro.
  iExists δ2, ℓ. iSplit; first done.
  iFrame "Hσ". iSplitR "Hefs".
  - iApply ("IH" with "[//] H HΦ").
  - iApply (big_sepL_impl with "Hefs"); iIntros "!>" (k ef _).
    iIntros "H". iApply ("IH" with "[] H"); auto.
Qed.

Lemma fupd_wp s E ζ e Φ : (|={E}=> WP e @ s; ζ; E {{ Φ }}) ⊢ WP e @ s; ζ; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (extr atr K tp1 tp2 σ1 Hexe) "Hsi". iMod "H".
  iApply ("H" with "[] Hsi"); done.
Qed.
Lemma wp_fupd s E ζ e Φ : WP e @ s; ζ; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; ζ; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.

Class AllowsStuttering := {
  stuttering_label: mlabel AS;
  allows_stuttering :
    ∀ (extr : execution_trace Λ) (atr : auxiliary_trace AS) c δ oζ,
      valid_exec extr →
      trace_ends_in extr c →
      trace_ends_in atr δ →
      locale_step c oζ c →
      state_interp extr atr ==∗
      ⌜valid_state_evolution extr atr oζ stuttering_label c δ⌝ ∗
      state_interp (trace_extend extr oζ c) (trace_extend atr stuttering_label δ);
  }.

Class AllowsPureStep := {
  pure_label: mlabel AS;
  allows_pure_step :
    ∀ (extr : execution_trace Λ) (atr : auxiliary_trace AS)  tp tp' σ δ oζ,
      valid_exec extr →
      trace_ends_in extr (tp, σ) →
      trace_ends_in atr δ →
      locale_step (tp, σ) oζ (tp', σ) →
      state_interp extr atr ==∗
      ⌜valid_state_evolution extr atr oζ pure_label (tp', σ) δ⌝ ∗
      state_interp (trace_extend extr oζ (tp', σ)) (trace_extend atr pure_label δ);
  }.

Global Instance AllowsPureStep_AllowsStuttering :
  AllowsPureStep → AllowsStuttering.
Proof.
  intros Haps. refine ({| stuttering_label := pure_label |}).
  iIntros (extr atr [tp σ] δ oζ ? ? ? ?) "Hsi".
  iApply allows_pure_step; done.
Qed.

Lemma wp_stuttering_atomic s E1 E2 ζ e Φ
      `{!AllowsStuttering}
      `{!StutteringAtomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros "H".
  iLöb as "IH".
  rewrite {2}(wp_unfold s E1 e) /wp_pre.
  rewrite !(wp_unfold s E2 e) /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi".
  iAssert ((|={E1}=> ⌜match s with
                      | NotStuck => reducible e σ1
                      | MaybeStuck => True
                      end⌝ ∗
            state_interp extr atr ∗ _)%I) with "[H Hsi]" as
      ">(Hnstuck & Hsi & H)".
  { iApply fupd_plain_keep_l.
    iSplitR; last (iFrame "Hsi"; iExact "H").
    iIntros "[Hsi H]".
    iApply fupd_plain_mask.
    iMod "H".
    iMod ("H" with "[//] [//] [//] Hsi") as "[? _]".
    iModIntro; done. }
  iPoseProof (fupd_mask_intro_subseteq E1 ∅ True%I with "[]") as "Hmsk";
    [set_solver|done|].
  iMod "Hmsk".
  iModIntro.
  iSplitL "Hnstuck"; first done.
  iIntros (e2 σ2 efs Hstep).
  destruct (stutteringatomic _ _ _ _ Hstep) as [(?&?&?)|Hs]; simplify_eq/=.
  - iModIntro; iNext.
    iMod (allows_stuttering with "Hsi") as "[% Hsi]"; [done|done|done| |].
    { econstructor 1; [done| |by apply fill_step]; by rewrite app_nil_r. }
    iMod "Hmsk" as "_"; iModIntro.
    rewrite app_nil_r.
    iExists (trace_last atr), stuttering_label; iFrame "Hsi".
    iSplitR; first done.
    iSplitL; last done.
    iApply "IH"; done.
  - iClear "IH".
    iMod "Hmsk" as "_".
    iMod "H". iMod ("H" with "[//] [//] [//] Hsi") as "[_ H]".
    iMod ("H" with "[//]") as "H". iIntros "!>!>".
    iMod "H" as (δ2 ℓ) "(% & Hσ & H & Hefs)". destruct s.
    + rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
      * iDestruct "H" as ">> H".
        iModIntro; iExists _, _; iSplitR; first done.
        iFrame.
        rewrite !wp_unfold /wp_pre He2; done.
      * iMod ("H" with "[] [] [] [$]") as "[H _]".
        { iPureIntro. eapply extend_valid_exec; [done|done|].
          econstructor; [done|done|].
          apply fill_step; done. }
        { by erewrite <-locale_fill_step. }
        { done. }
        iDestruct "H" as %(? & ? & ? & ?%Hs); done.
    + destruct Hs as [v <-%of_to_val].
      rewrite !wp_unfold /wp_pre to_of_val.
      iMod "H" as ">H"; iModIntro.
      iExists _, _; iSplitR; first done.
      rewrite !wp_unfold /wp_pre to_of_val.
      eauto with iFrame.
Qed.

Lemma wp_stutteringatomic_take_step
      s E1 E2 ζ e Φ
      `{!AllowsStuttering}
      `{!StutteringAtomic (stuckness_to_atomicity s) e} :
  TCEq (to_val e) None →
  (|={E1,E2}=>
   ∀ extr atr c1 δ1 ζ',
     ⌜trace_ends_in extr c1⌝ -∗
     ⌜trace_ends_in atr δ1⌝ -∗
     ⌜ζ = ζ'⌝ -∗
     state_interp extr atr ={E2}=∗
     ∃ Q R,
       state_interp extr atr ∗
       (∀ c2 δ2 ℓ,
           ∃ δ',
           state_interp
             (trace_extend extr (Some ζ') c2)
             (trace_extend atr ℓ δ2) ∗
           ⌜valid_state_evolution extr atr (Some ζ') ℓ c2 δ2⌝ ∗ Q ={E2}=∗
             ⌜valid_state_evolution extr atr (Some ζ') stuttering_label c2 δ'⌝ ∗
             state_interp
               (trace_extend extr (Some ζ') c2)
               (trace_extend atr stuttering_label δ') ∗ R) ∗
       (state_interp extr atr ={E2}=∗ state_interp extr atr ∗ Q) ∗
   WP e @ s; ζ; E2 {{ v, R ={E2,E1}=∗ Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (He) "H".
  iLöb as "IH".
  rewrite {2}wp_unfold /wp_pre He.
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi".
  iAssert ((|={E1}=> ⌜match s with
                      | NotStuck => reducible e σ1
                      | MaybeStuck => True
                      end⌝ ∗
            state_interp extr atr ∗ _)%I) with "[H Hsi]" as
      ">(Hnstuck & Hsi & H)".
  { iApply fupd_plain_keep_l.
    iSplitR; last (iFrame "Hsi"; iExact "H").
    iIntros "[Hsi H]".
    iApply fupd_plain_mask.
    iMod "H".
    iMod ("H" with "[//] [//] [//] Hsi") as (Q R) "[Hsi (_&_&H)]".
    rewrite !wp_unfold /wp_pre He.
    iMod ("H" with "[] [] [] Hsi") as "[? _]"; done. }
  iMod (fupd_mask_intro_subseteq E1 ∅ True%I with "[]") as "Hmsk";
    [set_solver|done|].
  iModIntro.
  iSplit; first done.
  iIntros (e2 σ2 efs Hstep).
  pose proof Hstep as  [(?&?&?)|HSA]%stutteringatomic; simplify_eq/=.
  - iModIntro; iNext.
    iMod (allows_stuttering with "Hsi") as "[% Hsi]"; [done|done|done| |].
    { econstructor 1; [done| |by apply fill_step]; by rewrite app_nil_r. }
    iMod "Hmsk" as "_"; iModIntro.
    rewrite app_nil_r.
    iExists (trace_last atr), stuttering_label; iFrame "Hsi".
    iSplitR; first done.
    iSplitL; last done.
    iApply "IH"; done.
  - iMod "Hmsk" as "_".
    iMod ("H" with "[//] [//] [//] Hsi") as ">H".
    iDestruct "H" as (Q R) "(Hsi & Hupdate & Htrans & H)".
    rewrite (wp_unfold s E2 e) /wp_pre He.
    iMod ("Htrans" with "Hsi") as "(Hsi & HQ)".
    iMod ("H" with "[//] [//] [//] Hsi") as "[_ H]".
    iMod ("H" with "[//]") as "H". iIntros "!>!>".
    iMod "H" as (δ3 ℓ) "(Hδ3 & Hsi & H & Hefs)".
    iDestruct ("Hupdate" $! (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2) δ3 ℓ)
      as (δ') "Hupdate".
    iMod ("Hupdate" with "[$HQ $Hsi $Hδ3]") as "(Hδ2 & Hsi & HR)".
    destruct s.
    + rewrite (wp_unfold _ E2 e2); rewrite /wp_pre.
      destruct (to_val e2) as [v2|] eqn:He2.
      * iDestruct ("H" with "HR") as ">> H".
        iModIntro; iExists _, _; iFrame.
        rewrite -(of_to_val _ _ He2) -wp_value'; done.
      * iMod ("H" with "[] [] [] Hsi") as "[% _]"; try done.
        { iPureIntro. eapply extend_valid_exec; [done|done|].
          econstructor; [done|done|].
          apply fill_step; done. }
        { by erewrite locale_fill_step. }
        exfalso; simpl in *; eapply not_reducible; eauto.
    + simpl in *.
      destruct HSA as [v <-%of_to_val].
      iMod (wp_value_inv' with "H HR") as ">H".
      iModIntro. iExists _, _; iSplit; first done.
      iFrame "Hsi Hefs". by iApply wp_value'.
Qed.

Lemma wp_atomic s E1 E2 ζ e Φ
      `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros "H".
  rewrite (wp_unfold s E1 e) /wp_pre.
  rewrite !(wp_unfold s E2 e) /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale exe) "Hsi".
  iMod "H".
  iMod ("H" with "[//] [//] [//] Hsi") as "[% H]".
  iModIntro.
  iSplit; first by iPureIntro.
  iIntros (e2 σ2 efs Hstep).
  pose proof (atomic _ _ _ _ Hstep) as Hs; simplify_eq/=.
  iMod ("H" with "[//]") as "H". iIntros "!>!>".
  iMod "H" as (δ2 ℓ) "(% & Hσ & H & Hefs)". destruct s.
  - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> H".
      iModIntro; iExists _, _; iSplitR; first done.
      iFrame.
      rewrite !wp_unfold /wp_pre He2; done.
    + iMod ("H" with "[] [] [] [$]") as "[H _]"; try done.
      { iPureIntro. eapply extend_valid_exec; [done|done|].
        econstructor; [done|done|].
        apply fill_step; done. }
      { by erewrite <-locale_fill_step. }
      iDestruct "H" as %(? & ? & ? & ?%Hs); done.
  - destruct Hs as [v <-%of_to_val].
    rewrite !wp_unfold /wp_pre to_of_val.
    iMod "H" as ">H"; iModIntro.
    iExists _, _; iSplitR; first done.
    rewrite !wp_unfold /wp_pre to_of_val.
    eauto with iFrame.
Qed.

Lemma wp_atomic_take_step
      s E1 E2 ζ e Φ
      `{!Atomic (stuckness_to_atomicity s) e} :
  TCEq (to_val e) None →
  (|={E1,E2}=>
   ∀ extr atr c1 δ1 ζ',
     ⌜trace_ends_in extr c1⌝ -∗
     ⌜trace_ends_in atr δ1⌝ -∗
     ⌜ζ = ζ'⌝ -∗
     state_interp extr atr ={E2}=∗
     ∃ Q R,
       state_interp extr atr ∗
       (∀ c2 δ2 ℓ,
           ∃ δ' ℓ',
           state_interp
             (trace_extend extr (Some ζ') c2)
             (trace_extend atr ℓ δ2) ∗
           ⌜valid_state_evolution extr atr (Some ζ') ℓ c2 δ2⌝ ∗ Q ={E2}=∗
             ⌜valid_state_evolution extr atr (Some ζ') ℓ' c2 δ'⌝ ∗
             state_interp
               (trace_extend extr (Some ζ') c2)
               (trace_extend atr ℓ' δ') ∗ R) ∗
       (state_interp extr atr ={E2}=∗ state_interp extr atr ∗ Q) ∗
   WP e @ s; ζ; E2 {{ v, R ={E2,E1}=∗ Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (He) "H".
  rewrite wp_unfold /wp_pre He.
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi".
  iMod ("H" with "[//] [//] [//] Hsi") as ">H".
  iDestruct "H" as (Q R) "(Hsi & Hupdate & Htrans & H)".
  rewrite (wp_unfold s E2 e) /wp_pre He.
  iMod ("Htrans" with "Hsi") as "(Hsi & HQ)".
  iMod ("H" with "[//] [//] [//] Hsi") as "[% H]".
  iModIntro.
  iSplit; first by iPureIntro.
  iIntros (e2 σ2 efs Hstep).
  pose proof (atomic _ _ _ _ Hstep) as Hs; simplify_eq/=.
  iMod ("H" with "[//]") as "H". iIntros "!>!>".
  iMod "H" as (δ3 ℓ) "(Hδ3 & Hsi & H & Hefs)".
  iDestruct ("Hupdate" $! (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2) δ3 ℓ)
      as (δ' ℓ') "Hupdate".
  iMod ("Hupdate" with "[$HQ $Hsi $Hδ3]") as "(Hδ2 & Hsi & HR)".
  destruct s.
  - rewrite (wp_unfold _ E2 e2); rewrite /wp_pre.
    destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct ("H" with "HR") as ">> H".
      iModIntro; iExists _,_; iFrame.
      rewrite -(of_to_val _ _ He2) -wp_value'; done.
    + iMod ("H" with "[] [] [] Hsi") as "[% _]"; try done.
      { iPureIntro. eapply extend_valid_exec; [done|done|].
        econstructor; [done|done|].
        apply fill_step; done. }
      { by erewrite <-locale_fill_step. }
      exfalso; simpl in *; eapply not_reducible; eauto.
  - simpl in *.
    destruct Hs as [v <-%of_to_val].
    iMod (wp_value_inv' with "H HR") as ">H".
    iModIntro. iExists _, _; iSplit; first done.
    iFrame "Hsi Hefs". by iApply wp_value'.
Qed.

Lemma wp_step_fupd s E1 E2 ζ e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; ζ; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; ζ; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi".
  iMod "HR". iMod ("H" with "[//] [//] [//] [$]") as "[$ H]".
  iIntros "!>" (e2 σ2 efs Hstep).
  iMod ("H" $! e2 σ2 efs with "[% //]") as "H".
  iIntros "!>!>". iMod "H" as (δ2 ℓ) "(Hsv & Hσ & H & Hefs)".
  iMod "HR". iModIntro; iExists δ2, ℓ; iSplit; first done. iFrame "Hσ Hefs".
  iApply (wp_strong_mono s s E2 with "H"); [done..|].
  iIntros (v) "H". by iApply "H".
Qed.

Lemma wp_bind K s E ζ e Φ :
  WP e @ s; ζ; E {{ v, WP ectx_fill K (of_val v) @ s; ζ; E {{ Φ }} }} ⊢
  WP ectx_fill K e @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e ζ Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val; last done.
  iIntros (extr atr K' tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi".
  iMod ("H" $! _ _ (ectx_comp K' K) with "[//] [] [] [$]") as "[% H]".
  { rewrite ectx_comp_comp; done. }
  { rewrite ectx_comp_comp; done. }
  iModIntro; iSplit.
  { iPureIntro. destruct s; first apply reducible_fill; done. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv K e σ1 e2 σ2 efs) as (e2'&->&?);
    [done|done|].
  iMod ("H" with "[//]") as "H". iIntros "!>!>".
  iMod "H" as (δ2 ℓ) "(Hsv & Hσ & H & Hefs)".
  rewrite !ectx_comp_comp.
  iModIntro; iExists δ2, ℓ; iSplit; first done.
  iFrame "Hefs Hσ". by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono s E ζ e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E ζ e Φ :
  s1 ⊑ s2 → WP e @ s1; ζ; E {{ Φ }} ⊢ WP e @ s2; ζ; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E ζ e Φ :
  WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ ζ; E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 ζ e Φ : E1 ⊆ E2 → WP e @ s; ζ; E1 {{ Φ }} ⊢ WP e @ s; ζ; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E ζ e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E ζ e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E ζ e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E ζ e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value s E Φ  ζ e v : IntoVal e v → Φ v ⊢ WP e @ s; ζ; E {{ Φ }}.
Proof. intros <-. by apply wp_value'. Qed.
Lemma wp_value_fupd' s E ζ Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ s; ζ; E {{ Φ }}.
Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
Lemma wp_value_fupd s E Φ ζ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ WP e @ s; ζ;  E {{ Φ }}.
Proof. intros. rewrite -wp_fupd -wp_value //. Qed.
Lemma wp_value_inv s E Φ ζ e v : IntoVal e v → WP e @ s; ζ; E {{ Φ }} ={E}=∗ Φ v.
Proof. intros <-. by apply wp_value_inv'. Qed.

Lemma wp_frame_l s E ζ e Φ R : R ∗ WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E ζ e Φ R : WP e @ s; ζ; E {{ Φ }} ∗ R ⊢ WP e @ s; ζ; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma wp_frame_step_l s E1 E2 ζ e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; ζ; E2 {{ Φ }} ⊢ WP e @ s; ζ; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 ζ e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; ζ; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; ζ; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E ζ e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E ζ e Φ R :
  TCEq (to_val e) None → WP e @ s; ζ; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; ζ; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E ζ e Φ Ψ :
  WP e @ s; ζ; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; ζ; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E ζ e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E ζ e Φ Ψ :
  WP e @ s; ζ; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; ζ; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand_l s E ζ e Q Φ :
  Q ∗ WP e @ s; ζ; E {{ v, Q -∗ Φ v }} -∗ WP e @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End wp.

Global Arguments AllowsStuttering {_} _ _ {_}.
Global Arguments AllowsPureStep {_} _ _ {_}.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisG Λ AS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wp p s E ζ e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; ζ; E {{ Φ }}) (WP e @ s; ζ; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E ζ e Φ : IsExcept0 (WP e @ s; ζ; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E ζ e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; ζ; E {{ Φ }}) (WP e @ s; ζ; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E ζ e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; ζ; E {{ Φ }}) (WP e @ s; ζ; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_stutteringatomic p s E1 E2 ζ e P Φ :
    AllowsStuttering AS Σ →
    StutteringAtomic (stuckness_to_atomicity s) e →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @ s; ζ; E1 {{ Φ }}) (WP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r wp_stuttering_atomic.
  Qed.

  Global Instance add_modal_fupd_wp s E ζ e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; ζ; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_stuttering {X} E1 E2 ζ α β γ e s Φ :
    AllowsStuttering AS Σ →
    StutteringAtomic (stuckness_to_atomicity s) e →
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; ζ; E1 {{ Φ }})
            (λ x, WP e @ s; ζ; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ? ? _.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 ζ e P Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @ s; ζ; E1 {{ Φ }}) (WP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r wp_atomic.
  Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 ζ α β γ e s Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; ζ; E1 {{ Φ }})
            (λ x, WP e @ s; ζ; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ? _.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E ζ α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; ζ; E {{ Φ }})
            (λ x, WP e @ s; ζ; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
