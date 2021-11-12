From iris.proofmode Require Import tactics.
From trace_program_logic.program_logic Require Export weakestpre lifting ectx_lifting atomic.
From aneris.aneris_lang Require Import aneris_lang base_lang.
From aneris.aneris_lang.state_interp Require Import
     state_interp state_interp_events.
From stdpp Require Import binders.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
    [head_step]. The tactic will discharge head-reductions starting from values,
    and simplifies hypothesis related to conversions from and to values, and
    finite map operations. This tactic is slightly ad-hoc and tuned for proving
    our lifting lemmas. *)
Ltac inv_head_step :=
  repeat
    match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : aneris_to_val _ = Some _ |- _ => apply to_base_aneris_val in H
    | H : base_lang.head_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
      inversion H; subst; clear H
    | H : head_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      inversion H; subst; clear H
    | H: socket_step _ ?e _ _ _ _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      inversion H; subst; clear H
    end.

Local Ltac solve_exec_safe :=
  intros;
  repeat match goal with
         | H: _ ∧ _ |- _ => destruct H as [??]
         end;
  simplify_eq;
  do 3 eexists; eapply (LocalStepPureS _ ∅); econstructor; eauto.
Local Ltac solve_exec_puredet :=
  simpl; intros; inv_head_step;
  first (by repeat match goal with
                   | H: _ ∧ _ |- _ => destruct H as [??]; simplify_eq
                   | H : to_val _ = Some _ |- _ =>
                     rewrite to_of_val in H; simplify_eq
                   end);
  try by match goal with
         | H : socket_step _ _ _ _ _ _ _ _ _ |- _ =>
           inversion H
         end.
Local Ltac solve_pure_exec :=
  simplify_eq; rewrite /PureExec; intros;
  apply nsteps_once, pure_head_step_pure_step;
  constructor; [solve_exec_safe | solve_exec_puredet].

Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Instance into_val_val n v : IntoVal (mkExpr n (Val v)) (mkVal n v).
Proof. done. Qed.
Instance as_val_val n v : AsVal (mkExpr n (Val v)).
Proof. by exists (mkVal n v). Qed.

Instance into_val_base_val v : IntoVal (Val v) v.
Proof. done. Qed.
Instance as_val_base_val v : AsVal (Val v).
Proof. by exists v. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; inv_head_step; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; inv_head_step;
       rewrite /aneris_to_val /is_Some /=; eexists; by
         match goal with
         | H: _ = _ |- _ => rewrite -H
         end
    ].

Lemma aneris_base_fill K ip e :
  mkExpr ip (fill (Λ := base_ectxi_lang) K e) =
  fill (Λ := aneris_ectxi_lang) K (mkExpr ip e).
Proof.
  revert e; induction K as [|k K IHK] using rev_ind; first done.
  intros e.
  rewrite !fill_app /= -IHK /=; done.
Qed.

Instance aneris_pure_exec_fill
         (K : list ectx_item) ip (φ : Prop) (n : nat) e1 e2 :
  PureExec φ n (mkExpr ip e1) (mkExpr ip e2) →
  @PureExec aneris_lang φ n
            (mkExpr ip (@fill base_ectxi_lang K e1))
            (mkExpr ip (@fill base_ectxi_lang K e2)).
Proof.
  intros.
  rewrite !aneris_base_fill.
  eapply pure_exec_ctx; first apply _; done.
Qed.

Instance binop_atomic n s op v1 v2 :
  Atomic s (mkExpr n (BinOp op (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
Instance alloc_atomic lbl n s v : Atomic s (mkExpr n (Alloc lbl (Val v))).
Proof. solve_atomic. Qed.
Instance load_atomic n s v : Atomic s (mkExpr n (Load (Val v))).
Proof. solve_atomic. Qed.
Instance store_atomic n s v1 v2 : Atomic s (mkExpr n (Store (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
Instance cmpxchg_atomic n s v0 v1 v2 :
  Atomic s (mkExpr n (CAS (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
Instance fork_atomic n s e : Atomic s (mkExpr n (Fork e)).
Proof. solve_atomic. Qed.
Instance skip_atomic n s : Atomic s (mkExpr n Skip).
Proof. solve_atomic. Qed.

Instance newsocket_atomic n v0 v1 v2 s :
  Atomic s (mkExpr n  (NewSocket (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
Instance socketbind_atomic n v0 v1  s :
  Atomic s (mkExpr n (SocketBind (Val v0) (Val v1))).
Proof. solve_atomic. Qed.
Instance sendto_atomic n v0 v1 v2 s :
  Atomic s (mkExpr n (SendTo (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.

Instance setreceivetimeout_atomic n v0 v1 v2 s:
    Atomic s (mkExpr n (SetReceiveTimeout (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.

Instance receive_from_stutteringatomic n sh s :
  StutteringAtomic s (mkExpr n (ReceiveFrom (Val $ LitV $ sh))).
Proof.
  apply strongly_stutteringatomic_stutteringatomic,
    ectx_language_stutteringatomic.
  - inversion 1; inv_head_step; try naive_solver; [].
    rewrite insert_id; last done.
    match goal with
      |- context [state_heaps ?st] => by destruct st; eauto
    end.
  - apply ectxi_language_sub_redexes_are_values; intros [] **; inv_head_step;
      rewrite /aneris_to_val /is_Some /=; eexists; by
          match goal with
          | H: _ = _ |- _ => rewrite -H
          end.
Qed.

Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Instance pure_rec n f x erec :
  PureExec True 1 (mkExpr n (Rec f x erec)) (mkExpr n (Val $ RecV f x erec)).
Proof. solve_pure_exec. Qed.
Instance pure_pairc n v1 v2:
  PureExec True 1 (mkExpr n (Pair (Val v1) (Val v2)))
           (mkExpr n (Val $ PairV v1 v2)).
Proof. solve_pure_exec. Qed.
Instance pure_injlc n v :
  PureExec True 1 (mkExpr n (InjL $ Val v)) (mkExpr n (Val $ InjLV v)).
Proof. solve_pure_exec. Qed.
Instance pure_injrc n v :
  PureExec True 1 (mkExpr n (InjR $ Val v)) (mkExpr n (Val $ InjRV v)).
Proof. solve_pure_exec. Qed.

Instance pure_beta n f x erec v1 v2 `{!AsRecV v1 f x erec} :
  PureExec True 1 (mkExpr n (App (Val v1) (Val v2)))
           (mkExpr n (subst' x v2 (subst' f v1 erec))).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Instance pure_unop n op v v' :
  PureExec (un_op_eval op v = Some v') 1 (mkExpr n (UnOp op (Val v)))
           (mkExpr n (of_val v')).
Proof. solve_pure_exec. Qed.

Instance pure_binop n op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1
           (mkExpr n (BinOp op (Val v1) (Val v2))) (mkExpr n (of_val v')).
Proof. solve_pure_exec. Qed.

Instance pure_if_true n e1 e2 :
  PureExec True 1 (mkExpr n (If (Val $ LitV $ LitBool true) e1 e2)) (mkExpr n e1).
Proof. solve_pure_exec. Qed.

Instance pure_if_false n e1 e2 :
  PureExec True 1 (mkExpr n (If (Val $ LitV $ LitBool false) e1 e2))
           (mkExpr n e2).
Proof. solve_pure_exec. Qed.

Instance pure_fst n v1 v2 :
  PureExec True 1 (mkExpr n (Fst (PairV v1 v2))) (mkExpr n (Val v1)).
Proof. solve_pure_exec. Qed.

Instance pure_snd n v1 v2  :
  PureExec True 1 (mkExpr n (Snd (PairV v1 v2))) (mkExpr n (Val v2)).
Proof. solve_pure_exec. Qed.

Instance pure_find_from n v0 v1 n1 v2 v' :
  PureExec (index n1 v2 v0 = v' ∧ Z.of_nat n1 = v1) 1
           (mkExpr n (FindFrom (Val $ LitV $ LitString v0)
                       (Val $ LitV $ LitInt v1)
                       (Val $ LitV $ LitString v2)))
           (mkExpr n (of_val (option_nat_to_val v'))).
Proof. solve_pure_exec. Qed.

Instance pure_substring n v0 v1 n1 v2 n2 v' :
  PureExec (substring n1 n2 v0 = v' ∧ Z.of_nat n1 = v1 ∧ Z.of_nat n2 = v2) 1
           (mkExpr
              n (Substring
                   (LitV $ LitString v0) (LitV $ LitInt v1) (LitV $ LitInt v2)))
           (mkExpr n (of_val (LitV $ LitString v'))).
Proof. solve_pure_exec. Qed.

Instance pure_case_inl n v e1 e2  :
  PureExec True 1 (mkExpr n (Case (Val $ InjLV v) e1 e2))
           (mkExpr n (App e1 (Val v))).
Proof. solve_pure_exec. Qed.

Instance pure_case_inr n v e1 e2 :
  PureExec True 1 (mkExpr n (Case (Val $ InjRV v) e1 e2))
           (mkExpr n (App e2 (Val v))).
Proof. solve_pure_exec. Qed.

Instance pure_make_address n v1 v2 :
  PureExec True 1
           (mkExpr n (MakeAddress (LitV (LitString v1)) (LitV (LitInt (v2)))))
           (mkExpr
              n (LitV (LitSocketAddress (SocketAddressInet v1 (Z.to_pos v2))))).
Proof. solve_pure_exec. Qed.

Instance pure_get_address_info n ip p :
  PureExec True 1
           (mkExpr n (GetAddressInfo (LitV (LitSocketAddress (SocketAddressInet ip p)))))
           (mkExpr n (PairV #ip #(Zpos p))).
Proof. solve_pure_exec. Qed.

Opaque aneris_state_interp.

Section primitive_laws.
  Context `{anerisG Mdl Σ}.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : aneris_val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.
  Implicit Types σ : base_lang.state.
  Implicit Types M R T : message_soup.
  Implicit Types m : message.
  Implicit Types A B : gset socket_address.
  Implicit Types a : socket_address.
  Implicit Types ip : ip_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.
  Implicit Types mh : messages_history.

  Global Instance aneris_lang_allows_stuttering :
    AllowsStuttering aneris_AS Σ.
  Proof.
    refine ({| stuttering_label := () |}).

    iIntros (ex atr c δ ? ? Hval Hc Hδ) "[? ?]".
    rewrite /state_interp /=.
    rewrite (last_eq_trace_ends_in ex c) //=.
    rewrite (last_eq_trace_ends_in atr δ) //=.
    rewrite aneris_events_state_interp_same_tp; [| |done|done]; last first.
    { eapply extend_valid_exec; eauto. }
    iModIntro.
    rewrite -message_history_evolution_id; iFrame.
    iPureIntro; apply user_model_evolution_id.
  Qed.

  Global Instance aneris_lang_allows_pure_step :
    AllowsPureStep aneris_AS Σ.
  Proof.
    refine ({| pure_label := () |}).

    iIntros (ex atr tp tp' σ δ ? ? ? Hex Hδ) "[? ?]".
    rewrite /state_interp /=.
    rewrite (last_eq_trace_ends_in ex (tp, σ)) //=.
    rewrite (last_eq_trace_ends_in atr δ) //=.
    rewrite aneris_events_state_interp_pure; [| |done|done]; last first.
    { eapply extend_valid_exec; eauto. }
    iModIntro.
    rewrite -message_history_evolution_id; iFrame.
    iPureIntro; apply user_model_evolution_id.
  Qed.

  Lemma wp_fork n k E tid e Φ :
    ▷ Φ (mkVal n #()) ∗ (∀ tid', ▷ WP (mkExpr n e) @ k; (n, tid'); ⊤ {{ _, True }}) ⊢
    WP (mkExpr n (Fork e)) @ k; (n, tid); E {{ Φ }}.
  Proof.
    iIntros "[HΦ He]". iApply wp_lift_atomic_head_step; [done|].
    iIntros (ex atr K tp1 tp2 σ1 Hexvalid Hex Hlocale) "Hsi !>".
    iSplit.
    - iPureIntro. solve_exec_safe.
    - iIntros (e2 σ2 efs Hstep).
      assert (Hval: valid_exec (ex :tr[Some $ locale_of tp1 $ ectx_language.fill K (mkExpr n (Fork e))]:
                                  (tp1 ++ ectx_language.fill K e2 :: tp2 ++ efs, σ2))).
      { eapply extend_valid_exec; [done|done|]. econstructor 1; last econstructor; eauto. }
      inv_head_step.
      rewrite (last_eq_trace_ends_in _ _ Hex).
      iExists (trace_last atr), ().
      iIntros "!> !>". iSplit.
      + iPureIntro; apply user_model_evolution_id.
      + rewrite aneris_events_state_interp_pure; [| |done|done].
        * rewrite -message_history_evolution_id; iFrame; eauto.
        * rewrite ectx_language.locale_fill /= Hlocale // in Hval.
  Qed.

  Lemma wp_alloc_gen n lblo evs k E ζ v :
    {{{ ▷ is_node n ∗ ▷ match lblo with Some lbl => alloc_evs lbl evs | _ => True end }}}
      (mkExpr n (Alloc lblo (Val v))) @ k; ζ; E
    {{{ l, RET (mkVal n #l); l ↦[n] v ∗
        match lblo with
          Some lbl =>
          ∃ h (σ : state),
          ⌜valid_allocObs n l σ h⌝ ∗
          alloc_evs lbl (evs ++ [allocObs n lbl l v σ h])
       | _ => True end }}}.
  Proof.
    iIntros (Φ) "[>Hn Haevs] HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (is_node_heap_valid with "Hσ Hn") as (h) "%".
    iSplitR; [by iPureIntro; do 3 eexists; eapply LocalStepS; eauto | ].
    iIntros (v2 σ2 efs Hstep).
    destruct lblo as [lbl|].
    - pose proof (conj Hstep I) as Hstep'.
      inv_head_step. iNext.
      destruct Hstep' as [Hstep' _].
      iMod (aneris_state_interp_alloc_heap with "Hn Hσ") as "[Hσ Hl]"; [done..|].
      iMod (aneris_events_state_interp_alloc_triggered with "Haevs Hevs") as "[Hevs Haevs]";
      [done|done|done| |].
      { eexists _, _, _, _; eauto. }
      iExists (trace_last atr), (). iIntros "!>".
      iSplit; [ iPureIntro; apply user_model_evolution_id |].
      rewrite -message_history_evolution_id; iFrame.
      iSplitR; [done|].
      iApply "HΦ"; eauto with iFrame.
    - pose proof Hex as Htrig.
      eapply aneris_events_state_interp_no_triggered in Htrig;
        [|done|done|done|done|done].
      inv_head_step. iNext.
      iMod (aneris_state_interp_alloc_heap with "Hn Hσ") as "[Hσ Hl]"; [done..|].
      iExists (trace_last atr), (). iIntros "!>".
      iSplit; [ iPureIntro; apply user_model_evolution_id |].
      rewrite -message_history_evolution_id; iFrame.
      iSplitR; [done|].
      rewrite Htrig. iFrame.
      iApply "HΦ"; iFrame; done.
  Qed.

  Lemma wp_alloc n k E ζ v :
    {{{ ▷ is_node n }}}
      (mkExpr n (ref (Val v))) @ k; ζ; E
    {{{ l, RET (mkVal n #l); l ↦[n] v }}}.
  Proof.
    iIntros (Φ) "Hn HΦ".
    iApply (wp_alloc_gen _ None [] with "[$Hn //]").
    iNext. iIntros (?) "[? _]"; by iApply "HΦ".
  Qed.

  Lemma wp_alloc_tracked n lbl evs k E ζ v :
    {{{ ▷ is_node n ∗ ▷ alloc_evs lbl evs }}}
      (mkExpr n (ref<<lbl>> (Val v))) @ k; ζ; E
    {{{ l h (σ : state), RET (mkVal n #l); l ↦[n] v ∗
          ⌜valid_allocObs n l σ h⌝ ∗
          alloc_evs lbl (evs ++ [allocObs n lbl l v σ h]) }}}.
  Proof.
    iIntros (Φ) "Hn HΦ".
    iApply (wp_alloc_gen _ (Some lbl) with "[$Hn //]").
    iNext. iIntros (?) "[? Hevs]".
    iDestruct "Hevs" as (? ?) "[% ?]".
    iApply "HΦ"; iFrame; done.
  Qed.

  Lemma wp_load n k E ζ l q v :
    {{{ ▷ l ↦[n]{q} v }}}
      (mkExpr n (Load #l)) @ k; ζ; E
    {{{ RET (mkVal n v); l ↦[n]{q} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit.
    { iPureIntro; do 3 eexists; eapply LocalStepS; eauto; eapply LoadS; eauto. }
    iIntros (v2 σ2 efs Hstep).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step. iNext.
    rewrite insert_id //. rewrite insert_id //= in Htrig.
    destruct σ; iFrame. iModIntro. iExists (trace_last atr), ().
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    rewrite -message_history_evolution_id; iFrame.
    iSplit; first done.
    rewrite Htrig. iFrame.
    iApply "HΦ"; done.
  Qed.

  Lemma wp_store n k E ζ l v1 v2 :
    {{{ ▷ l ↦[n] v1 }}}
      (mkExpr n (Store #l (Val v2))) @ k; ζ; E
    {{{ RET (mkVal n #()); l ↦[n] v2 }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit. { iPureIntro; do 3 eexists. eapply LocalStepS; eauto. econstructor. }
    iIntros (? ? ? ?).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step. iNext.
    iMod (aneris_state_interp_heap_update with "[$Hσ $Hl]") as "[Hσ Hl]";
      [done|]. iModIntro. iExists (trace_last atr), ().
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    rewrite -message_history_evolution_id; iFrame.
    iSplit; first done.
    rewrite Htrig. iFrame.
    iApply "HΦ"; done.
  Qed.

  Lemma wp_cas_fail n k E ζ l q v v1 v2 :
    v ≠ v1 →
    {{{ ▷ l ↦[n]{q} v }}}
      (mkExpr n (CAS #l (Val v1) (Val v2))) @ k; ζ; E
    {{{ RET (mkVal n #false); l ↦[n]{q} v }}}.
  Proof.
    iIntros (Heq Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit.
    { iPureIntro; do 3 eexists. eapply LocalStepS; eauto. by econstructor. }
    iIntros (? ? ? ?).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step. iNext.
    rewrite insert_id //. rewrite insert_id // in Htrig.
    destruct σ; iFrame. iModIntro.
    iExists (trace_last atr), ().
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    rewrite -message_history_evolution_id; iFrame.
    iSplit; first done.
        rewrite Htrig. iFrame.
    iApply "HΦ"; done.
  Qed.

  Lemma wp_cas_suc n k E l v1 v2 :
    {{{ ▷ l ↦[n] v1 }}}
      (mkExpr n (CAS #l (Val v1) (Val v2))) @ k; E
    {{{ RET (mkVal n #true); l ↦[n] v2 }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit.
    { iPureIntro; do 3 eexists. eapply LocalStepS; eauto. by econstructor. }
    iIntros (? ? ? ?).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step. iNext.
    iMod (aneris_state_interp_heap_update with "[$Hσ $Hl]") as "[Hσ Hl]";
      [done|].
    iModIntro. iExists (trace_last atr), ().
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    rewrite -message_history_evolution_id; iFrame.
    iSplit; first done.
    rewrite Htrig; iFrame.
    iApply "HΦ"; done.
  Qed.

  Lemma wp_start ip ports k E ζ e Φ :
    ip ≠ "system" →
    ▷ free_ip ip ∗
    ▷ Φ (mkVal "system" #()) ∗
    ▷ (∀ tid, is_node ip -∗ free_ports ip ports -∗ WP (mkExpr ip e) @ k; (ip, tid); ⊤ {{ _, True }})
    ⊢ WP mkExpr "system" (Start (LitString ip) e) @ k; ζ; E {{ Φ }}.
  Proof.
    iIntros (?) "(>Hfip & HΦ & Hwp)".
    iApply (wp_lift_head_step with "[-]"); first auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex) "(Hevs & Hσ & Hm) /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
      first set_solver; auto.
    iDestruct (aneris_state_interp_free_ip_valid with "Hσ Hfip")
      as "(% & % & %)".
    iModIntro; iSplit.
    { iPureIntro. do 3 eexists. apply AssignNewIpStepS; eauto. }
    iNext. iIntros (e2 σ2 efs Hstep). iMod "Hmk" as "_".
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step.
    iMod (aneris_state_interp_alloc_node _ _ ports with "[$]")
      as "(%Hcoh & Hn & Hports & Hσ)".
    iModIntro.
    simplify_eq /=.
    iExists (trace_last atr), ().
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    rewrite -message_history_evolution_new_ip; last done.
    rewrite Htrig; iFrame.
    iSplitL "HΦ"; [by iApply wp_value|].
    iSplitL; [ by iApply ("Hwp" with "[$] [$]")|done].
  Qed.

  Lemma wp_new_socket ip s E ζ f t p :
    {{{ ▷ is_node ip }}}
      (mkExpr ip (NewSocket (Val $ LitV $ LitAddressFamily f)
                            (Val $ LitV $ LitSocketType t)
                            (Val $ LitV $ LitProtocol p))) @ s; ζ; E
    {{{ sh, RET (mkVal ip (LitV (LitSocket sh)));
        sh ↪[ip] (mkSocket f t p None true) }}}.
  Proof.
    iIntros (Φ) ">Hn HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (is_node_valid_sockets with "Hσ Hn") as (?) "%".
    iSplitR.
    { iPureIntro; do 3 eexists.
      eapply SocketStepS; eauto.
      apply newsocket_fresh. }
    set (sock := {| sfamily := f;
                    stype := t;
                    sprotocol := p;
                    saddress := None;
                    sblock := true |}).
    iIntros (????).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step. iNext.
    iMod (aneris_state_interp_alloc_socket sock with "Hn Hσ")
      as "[Hσ Hsh]"; try done.
    iModIntro.
    iExists (trace_last atr), ().
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    rewrite -message_history_evolution_new_socket; [|done|done].
    iSplitR; first done.
    rewrite Htrig; iFrame.
    iApply "HΦ"; done.
  Qed.

  Lemma wp_socketbind_static A E ζ sh skt k a :
    saddress skt = None →
    a ∈ A →
    {{{ ▷ fixed A ∗
        ▷ free_ports (ip_of_address a) {[port_of_address a]} ∗
        ▷ sh ↪[ip_of_address a] skt }}}
      (mkExpr (ip_of_address a)
              (SocketBind (Val $ LitV $ LitSocket sh)
                          (Val $ LitV $ LitSocketAddress a))) @ k; ζ; E
   {{{ RET (mkVal (ip_of_address a) #0);
       sh ↪[ip_of_address a] (skt<| saddress := Some a |>) ∗
       ∃ φ, a ⤇ φ }}}.
  Proof.
    iIntros (?? Φ) "(#Hfixed & >Hp & >Hsh) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iDestruct (aneris_state_interp_free_ports_valid with "Hσ Hp")
      as (?) "[% %]".
    iSplit.
    { iPureIntro; do 3 eexists.
      eapply SocketStepS; eauto.
      econstructor; naive_solver. }
    iIntros (v2' ? ? Hstep) "!>".
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step.
    iMod (aneris_state_interp_socketbind_static with "Hσ Hfixed Hsh Hp")
      as "(Hσ & Hsh & Hφ)"; [done..|].
    iModIntro.
    iExists (trace_last atr), ().
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    rewrite -message_history_evolution_socketbind; [|done|done].
    iSplitR; [done|].
    rewrite Htrig; iFrame.
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma wp_socketbind_dynamic skt A E ζ sh k a φ :
    saddress skt = None →
    a ∉ A →
    {{{ ▷ fixed A ∗
        ▷ free_ports (ip_of_address a) {[port_of_address a]} ∗
        ▷ sh ↪[ip_of_address a] skt
    }}}
      (mkExpr (ip_of_address a)
              (SocketBind (Val $ LitV $ LitSocket sh)
                          (Val $ LitV $ LitSocketAddress a))) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #0);
        sh ↪[ip_of_address a] (skt <| saddress := Some a |>) ∗
        a ⤇ φ }}}.
  Proof.
    iIntros (?? Φ) "(#Hfixed & >Hp & >Hsh) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iDestruct (aneris_state_interp_free_ports_valid with "Hσ Hp")
      as (?) "[% %]".
    iSplit.
    { iPureIntro; do 3 eexists. eapply SocketStepS; eauto.
      by econstructor; naive_solver. }
    iIntros (v2' ? ? Hstep) "!>".
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step.
    iMod (aneris_state_interp_socketbind_dynamic with "Hσ Hfixed Hsh Hp")
      as "(Hσ & Hsh & Hφ)"; [done..|].
    iModIntro.
    iExists (trace_last atr), ().
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    rewrite -message_history_evolution_socketbind; [|done|done].
    iSplitR; [done|].
    rewrite Htrig; iFrame.
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma wp_send_gen φ mbody (is_dup : bool) sh skt a strck rtrck evs to k E ζ R T
    (Ψ1 Ψ2 : state → iProp Σ):
    let msg := mkMessage a to (sprotocol skt) mbody  in
    saddress skt = Some a ->
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[strck, rtrck] (R, T) ∗
        (if is_dup then ⌜msg ∈ T⌝ else ▷ to ⤇ φ ∗ (▷ φ msg)) ∗
        if strck then
          ▷ sendon_evs a evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
          ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ)
        else True
    }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳[strck, rtrck] (R, {[ msg ]} ∪ T) ∗
        if strck then
          ∃ st skts r,
            ⌜valid_sendonObs a st sh skts skt r⌝ ∗
            sendon_evs a (evs ++ [sendonObs a st sh mbody to skt]) ∗
            Ψ1 st ∗ Ψ2 (sendonObs a st sh mbody to skt).(post_state) else True }}}.
  Proof.
    iIntros (msg Hskt Φ) "(>Hsh & >Hrt & Hmsg & Htrck) HΦ".
    iAssert (▷ if is_dup then ⌜msg ∈ T⌝ else to ⤇ φ ∗ φ msg)%I with "[Hmsg]" as "Hmsg".
    { destruct is_dup; iNext; done. }
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iSplitR.
    { iPureIntro; do 3 eexists. eapply SocketStepS; eauto.
        by econstructor; naive_solver. }
    iAssert (|={E}=>
             aneris_state_interp σ (trace_messages_history ex) ∗
             ▷ if strck then
               sendon_evs a evs ∗
               Ψ1 σ ∗
               (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ)
             else True)%I with "[Hσ Htrck]" as ">[Hσ Htrck]".
    { destruct strck; last by iFrame.
      iDestruct "Htrck" as "($&H&$)".
      iMod ("H" with "Hσ") as "[$ $]"; done. }
    iModIntro.
    iIntros (v2' ? ? Hstep).
    pose proof (λ a b c d f g h i j k,
                aneris_events_state_interp_send_untracked a b c d f g h _ i _ _ _ _ (Some ζ) j k Hstep)
      as Huntracked.
    pose proof (λ a b c d f g h i,
                aneris_events_state_interp_send_triggered a b c d f _ g _ _ _ _ (Some ζ) h i Hstep)
      as Htriggered.
    inv_head_step; iNext.
    rewrite (insert_id (state_sockets σ)); last done.
    rewrite (insert_id (state_sockets σ)) in Huntracked; last done.
    rewrite (insert_id (state_sockets σ)) in Htriggered; last done.
    destruct is_dup; last first.
    - iDestruct "Hmsg" as "[#Hφ Hmsg]".
      iMod (aneris_state_interp_send sh a _ _ skt
            with "[$Hsh] [$Hrt] [$Hφ] [$Hmsg] [$Hσ]")
        as "(%Hmhe & Hσ & Hsh & Hrt)"; [done..|].
      iAssert (|={E}=>
             aneris_state_interp _ _ ∗
             if strck then
               sendon_evs a _ ∗ Ψ1 σ ∗ Ψ2 _
             else True)%I with "[Hσ Htrck]" as ">[Hσ Htrck]".
      { destruct strck; last by iFrame "Hσ".
        iDestruct "Htrck" as "($&$&H)".
        iMod ("H" with "Hσ") as "[$ $]"; done. }
      rewrite - /msg.
      iExists (trace_last atr), ().
      destruct strck; last first.
      { iModIntro.
        iSplit; [ iPureIntro; apply user_model_evolution_id |].
        rewrite -Hmhe.
        iFrame.
        iSplitR; [done|].
        iDestruct (Huntracked with "Hrt Hevs") as "[$ Hrt]"; [done|done|by eauto 20 |].
        iApply ("HΦ" with "[$]"); done. }
      iDestruct "Htrck" as "(Hevs' & ? & ?)".
      iMod (Htriggered with "Hevs' Hevs") as "[Hevs' Hevs]"; [done|done|by eauto 20 |].
      iModIntro.
      iSplit; [ iPureIntro; apply user_model_evolution_id |].
      rewrite -Hmhe.
      iFrame.
      iSplitR; [done|].
      iApply "HΦ"; iFrame "Hrt Hsh"; eauto with iFrame.
    - iDestruct "Hmsg" as %?.
      iMod (aneris_state_interp_send_duplicate
            with "[$Hsh] [$Hrt] [$Hσ]")
      as "([%Hin %Hmhe] & Hσ & Hsh & Hrt)"; [done|done|done|done|].
      iAssert (|={E}=>
             aneris_state_interp _ _ ∗
             if strck then
               sendon_evs a _ ∗ Ψ1 σ ∗ Ψ2 _
             else True)%I with "[Hσ Htrck]" as ">[Hσ Htrck]".
      { destruct strck; last by iFrame "Hσ".
        iDestruct "Htrck" as "($&$&H)".
        iMod ("H" with "Hσ") as "[$ $]"; done. }
      rewrite - /msg.
      iExists (trace_last atr), ().
      destruct strck; last first.
      { iModIntro.
        iSplit; [ iPureIntro; apply user_model_evolution_id |].
        rewrite /= -Hmhe.
        destruct (trace_messages_history ex).
        iFrame.
        iSplitR; [done|].
        iDestruct (Huntracked with "Hrt Hevs") as "[$ Hrt]"; [done|done|by eauto 20 |].
        rewrite subseteq_union_1_L; last set_solver.
        iApply ("HΦ" with "[$]"); done. }
      iDestruct "Htrck" as "(Hevs' & ? & ?)".
      iMod (Htriggered with "Hevs' Hevs") as "[Hevs' Hevs]"; [done|done|by eauto 20 |].
      iModIntro.
      iSplit; [ iPureIntro; apply user_model_evolution_id |].
      rewrite /= -Hmhe.
      destruct (trace_messages_history ex).
      iFrame.
      iSplitR; [done|].
      rewrite subseteq_union_1_L; last set_solver.
      iApply "HΦ"; iFrame "Hrt Hsh"; eauto with iFrame.
  Qed.

  Lemma wp_send φ mbody sh skt a to rtrck k E ζ R T:
    let msg := mkMessage a to (sprotocol skt) mbody  in
    saddress skt = Some a ->
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[false, rtrck] (R, T) ∗
        ▷ to ⤇ φ ∗
        ▷ φ msg }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳[false, rtrck] (R, {[ msg ]} ∪ T) }}}.
  Proof.
    iIntros (msg Hskt Φ) "(>Hsh & >Hrt & #Hφ & Hmsg) HΦ".
    iApply (wp_send_gen _ _ false _ _ _ false _ inhabitant _ _ _ ζ _ _ (λ _, True) (λ _, True)
              with "[-HΦ]")%I; first done.
    - iFrame; eauto.
    - iNext. iIntros "(?&?&_)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_duplicate mbody sh skt a to rtrck k E ζ R T:
    let msg := mkMessage a to (sprotocol skt) mbody in
    saddress skt = Some a ->
    msg ∈ T →
    {{{  ▷ sh ↪[ip_of_address a] skt ∗
         ▷ a ⤳[false, rtrck] (R, T) }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳[false, rtrck] (R, T) }}}.
  Proof.
    iIntros (msg Hskt Hmsg Φ) "(>Hsh & >Hrt) HΦ".
    iApply (wp_send_gen (λ _, True) _ true _ _ _ false _ inhabitant _ _ _ ζ _ _ (λ _, True) (λ _, True)
              with "[-HΦ]")%I; first done.
    - iFrame; eauto.
    - rewrite subseteq_union_1_L; last set_solver.
      iNext. iIntros "(?&?&_)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_tracked φ mbody sh skt a rtrck evs to k E ζ R T
    (Ψ1 Ψ2 : state → iProp Σ) :
    let msg := mkMessage a to (sprotocol skt) mbody  in
    saddress skt = Some a ->
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[true, rtrck] (R, T) ∗
        ▷ to ⤇ φ ∗
        ▷ φ msg ∗
        ▷ sendon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ)
    }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳[true, rtrck] (R, {[ msg ]} ∪ T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs a st sh skts skt r⌝ ∗
          sendon_evs a (evs ++ [sendonObs a st sh mbody to skt]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs a st sh mbody to skt).(post_state) }}}.
  Proof.
    iIntros (msg Hskt Φ) "(>Hsh & >Hrt & #Hφ & Hmsg & Hevs) HΦ".
    iApply (wp_send_gen _ _ false _ _ _ true _ _ _ _ _ ζ _ _ Ψ1 Ψ2
              with "[-HΦ]")%I; first done.
    - iFrame; eauto.
    - iNext. iIntros "(?&?&?)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_duplicate_tracked mbody sh skt a rtrck evs to k E ζ R T
    (Ψ1 Ψ2 : state → iProp Σ):
    let msg := mkMessage a to (sprotocol skt) mbody  in
    saddress skt = Some a ->
    msg ∈ T →
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[true, rtrck] (R, T) ∗
        ▷ sendon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ)
    }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳[true, rtrck] (R, T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs a st sh skts skt r⌝ ∗
          sendon_evs a (evs ++ [sendonObs a st sh mbody to skt]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs a st sh mbody to skt).(post_state) }}}.
  Proof.
    iIntros (msg Hskt Hmsg Φ) "(>Hsh & >Hrt & Hevs) HΦ".
    iApply (wp_send_gen (λ _, True) _ true _ _ _ true _ _ _ _ _ ζ _ _ Ψ1 Ψ2
              with "[-HΦ]")%I; first done.
    - iFrame; eauto.
    - rewrite subseteq_union_1_L; last set_solver.
      iNext. iIntros "(?&?&?)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_receivefrom_gen'
          (Ψo : option (socket_interp Σ)) k a strck rtrck E ζ sh skt R T evs
          (Ψ1 Ψ2 : state → iProp Σ):
    saddress skt = Some a →
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[strck, rtrck] (R, T) ∗
        match Ψo with Some Ψ => a ⤇ Ψ | _ => True end ∗
        if rtrck then
          ▷ receiveon_evs a evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
          ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ)
          else True }}}
      (mkExpr (ip_of_address a)
              (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal (ip_of_address a) r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, rtrck] (R, T) ∗ ⌜sblock skt = false⌝) ∨
         (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, rtrck] ({[ msg ]} ∪ R, T) ∗
             match Ψo with Some Ψ => Ψ msg | _ => ∃ φ, a ⤇ φ ∗ φ msg end) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, rtrck] (R, T)) ∗
          if rtrck then
          ∃ st skts r,
            ⌜valid_receiveonObs a st sh msg skts skt r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts skt r).(post_state) else True))
    }}}.
  Proof.
    iIntros (Hskt Φ) "(>Hsh & >Hrt & #HΨ & Htrck) HΦ /=".
    iLöb as "IH".
    iApply wp_lift_head_step; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex) "(Hevs & Hσ & Hm) /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    destruct (decide (r = ∅)).
    - iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
        first set_solver; auto.
      iModIntro. iSplitR.
      { iPureIntro.
        destruct (sblock skt) eqn:?; destruct (set_choose_or_empty r) as [[]| ->%leibniz_equiv].
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail. }
      iIntros (v2' ? ? Hstep).
      pose proof (λ b c d f g h, aneris_events_state_interp_no_triggered' b c d _ f _ _ _ _ (Some ζ) g h Hstep)
        as Hnotriggered.
      inv_head_step; [done| |].
      + rewrite (insert_id (state_sockets σ)); last done.
        rewrite (insert_id (state_sockets σ)) in Hnotriggered; last done.
        iNext.
        iMod "Hmk".
        iModIntro.
        iExists (trace_last atr), ().
        iSplit; [ iPureIntro; apply user_model_evolution_id |].
        rewrite -message_history_evolution_id; iFrame.
        rewrite Hnotriggered;
          [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?) |
             by intros ? (?&?&?&?&?&?&?&?&?&?&?&?) | by intros ? (?&?&?&?&?&?&?&?&?)].
        iFrame.
        iApply wp_value.
        iApply "HΦ". iLeft. eauto with iFrame.
      + rewrite (insert_id (state_sockets σ)); last done.
        rewrite (insert_id (state_sockets σ)) in Hnotriggered; last done.
        iNext. iMod "Hmk".
        iModIntro.
        iExists (trace_last atr), ().
        iSplit; [ iPureIntro; apply user_model_evolution_id |].
        rewrite -message_history_evolution_id; iFrame.
        rewrite Hnotriggered;
          [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?) |
             by intros ? (?&?&?&?&?&?&?&?&?&?&?&?) | by intros ? (?&?&?&?&?&?&?&?&?)].
        iFrame.
        iApply ("IH" with "[$] [$] [$] [$]").
    - iClear "IH".
      iAssert (|={E}=>
               aneris_state_interp σ (trace_messages_history ex) ∗
               ▷ if rtrck then
                   receiveon_evs a evs ∗
                   Ψ1 σ ∗
                   (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ)
                 else True)%I with "[Hσ Htrck]" as ">[Hσ Htrck]".
      { destruct rtrck; last by iFrame.
        iDestruct "Htrck" as "($&H&$)".
        iMod ("H" with "Hσ") as "[$ $]"; done. }
      iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
        first set_solver; auto.
      iModIntro. iSplitR.
      { iPureIntro.
        destruct (sblock skt) eqn:?; destruct (set_choose_or_empty r) as [[]| ->%leibniz_equiv].
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail. }
      iIntros (v2' ? ? Hstep).
      pose proof (λ a b c d f g h i j k,
                  aneris_events_state_interp_receive_untracked a b c d f g h _ i _ _ _ _ (Some ζ) j k Hstep)
        as Huntracked.
      pose proof (λ a b c d f g h i,
                  aneris_events_state_interp_receive_triggered a b c d f _ g _ _ _ _ (Some ζ) h i Hstep)
        as Htriggered.
      inv_head_step.
      destruct (decide (m ∈ R)) as [Hin | Hni ].
      + iNext.
        iMod "Hmk".
        iPoseProof (aneris_state_interp_receive_some
                      with "[HΨ] [$Hσ] [$Hsh] [$Hrt]")
          as (R') "(% & %Hhist & Hrt & Hrest)"; [done..|].
        iDestruct "Hrt" as "[ (% & % & Hrt) | (_ & ->)]"; first done.
        iMod "Hrest" as "(Hσ & Hsh & Ha)".
        destruct rtrck.
        * iDestruct "Htrck" as "(Hrevs&HΨ1&HΨ2)".
          iMod ("HΨ2" with "Hσ") as "[Hσ HΨ2]".
          iMod (Htriggered with "Hrevs Hevs") as "[Hevs Hrevs]"; [done|done|by eauto 20|].
          iModIntro.
          iExists (trace_last atr), ().
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          rewrite Hhist.
          iFrame.
          iApply wp_value.
          iApply "HΦ". iRight; eauto.
          iExists m.
          iSplit; first done.
          iSplit; first done.
          iSplitL "Ha Hsh".
          { by iRight; iFrame. }
          eauto with iFrame.
        * iDestruct (Huntracked with "Ha Hevs") as "[Hevs Ha]"; [done|done|by eauto 20|].
          iModIntro.
          iExists (trace_last atr), ().
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          rewrite Hhist.
          iFrame.
          iApply wp_value.
          iApply "HΦ". iRight; eauto.
          iExists m.
          iSplit; first done.
          iSplit; first done.
          iSplitL "Ha Hsh".
          { by iRight; iFrame. }
          eauto with iFrame.
      + iPoseProof (aneris_state_interp_receive_some
                      with "[HΨ] [$Hσ] [$Hsh] [$Hrt]")
          as (R') "(% & %Hhst &  Hrt & Hrest)"; [done..|].
        iDestruct "Hrt" as "[ (% & -> & Hrt) | (% & %)]"; last done.
        iNext.
        iMod "Hrest" as "(Hσ & Hsh & Ha)".
        iMod "Hmk".
        destruct rtrck.
        * iDestruct "Htrck" as "(Hrevs&HΨ1&HΨ2)".
          iMod ("HΨ2" with "Hσ") as "[Hσ HΨ2]".
          iMod (Htriggered with "Hrevs Hevs") as "[Hevs Hrevs]"; [done|done|by eauto 20|].
          iModIntro.
          iExists (trace_last atr), ().
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          rewrite Hhst.
          iFrame.
          iApply wp_value.
          iApply "HΦ".
          iRight.
          iExists m.
          iSplit; first done.
          iSplit; first done.
          iSplitL "Ha Hsh Hrt".
          { by iLeft; iFrame. }
          eauto with iFrame.
        * iDestruct (Huntracked with "Ha Hevs") as "[Hevs Ha]"; [done|done|by eauto 20|].
          iModIntro.
          iExists (trace_last atr), ().
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          rewrite Hhst.
          iFrame.
          iApply wp_value.
          iApply "HΦ". iRight; eauto.
          iExists m.
          iSplit; first done.
          iSplit; first done.
          iSplitL "Ha Hsh Hrt".
          { by iLeft; iFrame. }
          eauto with iFrame.
  Qed.

  Lemma wp_receivefrom_nb_gen
        (Ψo : option (socket_interp Σ)) k a strck E ζ sh skt R T :
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[strck, false] (R, T) ∗
        match Ψo with Some Ψ => a ⤇ Ψ | _ => True end }}}
      (mkExpr (ip_of_address a)
              (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal (ip_of_address a) r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, false] (R, T) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, false] ({[ msg ]} ∪ R, T) ∗
             match Ψo with Some Ψ => Ψ msg | _ => ∃ φ, a ⤇ φ ∗ φ msg end) ∨
            ⌜msg ∈ R⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, false] (R, T))))) }}}.
  Proof.
    iIntros (Hskt Hblk Φ) "(>Hsh & >Hrt & #HΨ) HΦ /=".
    iApply (wp_receivefrom_gen' Ψo _ _ _ false _ _ _ _ _ _ [] (λ _, True) (λ _, True)
              with "[$Hsh $Hrt $HΨ] [HΦ]")%I; [done|].
    iNext.
    iIntros (?) "[(?&?&?&?)|H]"; iApply "HΦ"; first by iLeft; iFrame.
    iDestruct "H" as (? ? ?) "[[H|H] _]"; eauto 10.
  Qed.

  Lemma wp_receivefrom_nb k a E ζ sh skt R T :
    let ip := ip_of_address a in
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip] skt ∗ ▷ a ⤳ (R, T) }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ a ⤳ (R, T))) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗
             ∃ φ, a ⤇ φ ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳ (R, T))) }}}.
   Proof.
     iIntros (? ? Hs Φ) "(Hsh & Hsa) HΦ".
     iApply (wp_receivefrom_nb_gen None with "[$]"); [done|done|].
     iNext. iIntros (r) "Hr". iApply "HΦ"; eauto.
   Qed.

   Lemma wp_receivefrom_nb_alt k a E ζ sh skt R T φ :
    let ip := ip_of_address a in
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip] skt ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ a ⤳ (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
            ⌜msg ∈ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳ (R, T)) }}}.
   Proof.
     iIntros (? ? Hs Φ) "(Hsh & Hsa) HΦ".
     iApply (wp_receivefrom_nb_gen (Some φ) with "[$]"); [done|done|].
     iNext. iIntros (r) "Hr". iApply "HΦ"; eauto.
   Qed.

   Lemma wp_receivefrom k a E ζ h s R T φ :
     let ip := ip_of_address a in
     saddress s = Some a →
     sblock s = true →
  {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ}}}
    (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket h))) @ k; ζ; E
  {{{ m, RET (mkVal ip (SOMEV (PairV #(m_body m) #(m_sender m))));
      ⌜m_destination m = a⌝ ∗
      ((⌜m ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ φ m) ∨
        ⌜m ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T))
  }}}.
  Proof.
    simpl; iIntros (Haddr Hblk Φ) "(Hsh & Ha & #Hsi) HΦ".
    iApply (wp_receivefrom_gen' (Some φ) _ _ _ false _ _ _ _ _ _ [] (λ _, True) (λ _, True)
              with "[$Hsh $Ha $Hsi] [HΦ]")%I; [done|].
    iNext.
    iIntros (?) "[(?&?&?&%)|H]"; first by destruct (sblock s).
    iDestruct "H" as (? ? ->) "[[(?&?&?&?)|(?&?&?)] _]"; iApply "HΦ"; eauto with iFrame.
  Qed.

  Lemma wp_receivefrom_gen k a E ζ h s R T φ :
    let ip := ip_of_address a in
    saddress s = Some a →
  {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ}}}
    (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket h))) @ k; ζ; E
  {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)) }}}.
  Proof.
    simpl; iIntros (Haddr Φ) "(>Hsh & >Ha & #Hsi) HΦ".
    destruct (sblock s) eqn:Hblk.
    - iApply (wp_receivefrom with "[$Hsh $Ha]"); eauto.
      iNext. iIntros (m) "Hm".
      iApply "HΦ". iRight. iExists m.
      iDestruct "Hm" as (?) "[(% & Hh & Ha & _ & Hϕ) | Hm]";
        (repeat iSplit; first done; eauto).
      iLeft. eauto with iFrame.
    - iApply (wp_receivefrom_nb_alt with "[$Hsh $Ha]"); eauto.
  Qed.

  Lemma wp_receivefrom_nb_gen_tracked
          (Ψo : option (socket_interp Σ)) k a strck E ζ sh skt R T evs
      (Ψ1 Ψ2 : state → iProp Σ) :
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        ▷ receiveon_evs a evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ) ∗
        match Ψo with Some Ψ => a ⤇ Ψ | _ => True end }}}
      (mkExpr (ip_of_address a)
              (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal (ip_of_address a) r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, true] (R, T) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗
             match Ψo with Some Ψ => Ψ msg | _ => ∃ φ, a ⤇ φ ∗ φ msg end) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, true] (R, T)) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs a st sh msg skts skt r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts skt r).(post_state)))) }}}.
  Proof.
    iIntros (Hskt Hblk Φ) "(>Hsh & >Hrt & Hevs & HΨ1 & HΨ2 & #HΨ) HΦ /=".
    iApply (wp_receivefrom_gen' Ψo _ _ _ true with "[$Hsh $Hrt $Hevs $HΨ1 HΨ2 $HΨ //] [HΦ]")%I;
      [done|].
    iNext.
    iIntros (?) "[(?&?&?&?)|H]"; iApply "HΦ"; first by iLeft; iFrame.
    iDestruct "H" as (? ? ?) "[H1 H2]".
    iDestruct "H1" as "[H1|H1]"; by iRight; iExists _; iFrame.
  Qed.

  Lemma wp_receivefrom_nb_tracked k a strck E ζ sh skt R T evs (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address a in
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip] skt ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        ▷ receiveon_evs a evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ)}}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] (R, T))) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗
             ∃ φ, a ⤇ φ ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] (R, T)) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs a st sh msg skts skt r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts skt r).(post_state)) }}}.
   Proof.
     iIntros (? ? Hs Φ) "(Hsh & Hsa & Hevs & HΨ1 & HΨ2) HΦ".
     iApply (wp_receivefrom_nb_gen_tracked None with "[$]"); [done|done|].
     iNext. iIntros (r) "Hr". iApply "HΦ"; done.
   Qed.

  Lemma wp_receivefrom_nb_alt_tracked k a strck E ζ sh skt R T φ evs (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address a in
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip] skt ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ φ ∗
        ▷ receiveon_evs a evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ)}}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] (R, T)) ∗
           ∃ st skts r,
            ⌜valid_receiveonObs a st sh msg skts skt r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts skt r).(post_state) }}}.
   Proof.
     iIntros (? ? Hs Φ) "(Hsh & Hsa & Hproto & Hevs & HΨ1 & HΨ2) HΦ".
     iApply (wp_receivefrom_nb_gen_tracked (Some φ) with "[$]"); [done|done|].
     iNext.
     iIntros (r) "Hr"; iApply "HΦ"; eauto 10.
   Qed.

   Lemma wp_receivefrom_tracked k a strck E ζ sh s R T φ evs (Ψ1 Ψ2 : state → iProp Σ) :
     let ip := ip_of_address a in
     saddress s = Some a →
     sblock s = true →
     {{{ ▷ sh ↪[ip] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ φ ∗
        ▷ receiveon_evs a evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ) }}}
       (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
     {{{ m, RET (mkVal ip (SOMEV (PairV #(m_body m) #(m_sender m))));
      ⌜m_destination m = a⌝ ∗
      ((⌜m ∉ R⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] ({[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ φ m) ∨
        ⌜m ∈ R⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
      ∃ st skts r,
            ⌜valid_receiveonObs a st sh m skts s r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh m skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh m skts s r).(post_state) }}}.
  Proof.
    simpl; iIntros (Haddr Hblk Φ) "(Hsh & Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
    iApply (wp_receivefrom_gen' (Some φ) _ _ _ true
              with "[$Hsh $Ha $Hsi $Hevs $HΨ1 $HΨ2 //] [HΦ]")%I; [done|].
    iNext.
    iIntros (?) "[(?&?&?&%)|H]"; first by destruct (sblock s).
    iDestruct "H" as (? ? ->) "[[(?&?&?&?)|(?&?&?)] H]"; iApply "HΦ"; iFrame "H".
    - iSplit; first done. by iLeft; iFrame.
    - iSplit; first done. by iRight; iFrame.
  Qed.

  Lemma wp_receivefrom_gen_tracked k a strck E ζ sh s R T φ evs (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address a in
    saddress s = Some a →
  {{{ ▷ sh ↪[ip] s ∗
      ▷ a ⤳[strck, true] (R, T) ∗
      a ⤇ φ ∗
      ▷ receiveon_evs a evs ∗
      (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
      ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ) }}}
    (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
  {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs a st sh msg skts s r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh msg skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts s r).(post_state) }}}.
  Proof.
    simpl; iIntros (Haddr Φ) "(>Hsh & >Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
    destruct (sblock s) eqn:Hblk.
    - iApply (wp_receivefrom_tracked with "[$]"); eauto.
      iNext. iIntros (m) "Hm".
      iApply "HΦ". iRight. iExists m.
      iDestruct "Hm" as (?) "[[(% & Hh & Ha & _ & Hϕ) | Hm] $]";
        (repeat iSplit; first done; eauto).
      iLeft. eauto with iFrame.
    - iApply (wp_receivefrom_nb_alt_tracked with "[$]"); eauto.
  Qed.

  Lemma wp_rcvtimeo_unblock k a E ζ h s n1 n2 :
     let ip := ip_of_address a in
     saddress s = Some a →
     (0 ≤ n1 ∧ 0 <= n2 ∧ 0 < n1 + n2)%Z →
    {{{ ▷ h ↪[ip] s }}}
    (mkExpr ip (SetReceiveTimeout
                  (Val $ LitV $ LitSocket h)
                  (Val $ LitV $ LitInt n1)
                  (Val $ LitV $ LitInt n2))) @ k; ζ; E
     {{{ RET (mkVal ip #());
          h ↪[ip] s<|sblock := false|> }}}.
  Proof.
    iIntros (??? Φ) ">Hsh HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (ex atr K tp1 tp2 σ1 Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iMod (aneris_state_interp_sblock_update with "Hσ Hsh") as "(Hσ&Hsh)"; eauto.
    iModIntro. iSplitR.
    { iPureIntro; do 3 eexists.
      eapply SocketStepS; eauto.
      econstructor; naive_solver. }
    iIntros (v2' ? ? Hstep) "!>".
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step; last by lia.
    iModIntro.
    iExists (trace_last atr), ().
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    rewrite -message_history_evolution_update_sblock; [|done|done].
    iSplitR; [done|].
    rewrite Htrig.
    iFrame.
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma wp_rcvtimeo_block k a E ζ h s :
     let ip := ip_of_address a in
     saddress s = Some a →
     {{{ ▷ h ↪[ip] s }}}
    (mkExpr ip (SetReceiveTimeout
                  (Val $ LitV $ LitSocket h)
                  (Val $ LitV $ LitInt 0)
                  (Val $ LitV $ LitInt 0))) @ k; ζ; E
     {{{ RET (mkVal ip #());
          h ↪[ip] s<|sblock := true|> }}}.
  Proof.
    iIntros (?? Φ) ">Hsh HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (ex atr K tp1 tp2 σ1 Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm) /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iMod (aneris_state_interp_sblock_update with "Hσ Hsh") as "(Hσ&Hsh)"; eauto.
    iModIntro. iSplitR.
    { iPureIntro; do 3 eexists.
      eapply SocketStepS; eauto.
      econstructor; naive_solver. }
    iIntros (v2' ? ? Hstep) "!>".
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step; first by lia.
    iModIntro.
    iExists (trace_last atr), ().
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    rewrite -message_history_evolution_update_sblock; [|done|done].
    iSplitR; [done|].
    rewrite Htrig.
    iFrame.
    iApply ("HΦ" with "[$]").
  Qed.

End primitive_laws.
