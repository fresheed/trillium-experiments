From trace_program_logic.traces Require Export trace infinite_trace.
From trace_program_logic.program_logic Require Import language.

Import InfListNotations.

Definition execution_trace Λ := finite_trace (cfg Λ) (option (locale Λ)).

Record Model : Type := MkModel {
  mstate:> Type;
  mlabel: Type;
  mtrans: mstate -> mlabel -> mstate -> Prop;
}.

Arguments mtrans {_} _ _ _.

Notation olocale Λ := (option (locale Λ)).

Record AuxState Λ : Type := {
  (** Auxiliary state tracked along the physical state. *)
  aux_state :> Model;

  auxiliary_trace := finite_trace aux_state.(mstate) aux_state.(mlabel);

  (** The relation between the state before and after every step. *)
  valid_state_evolution :
    execution_trace Λ →
    finite_trace aux_state.(mstate) aux_state.(mlabel) →
    olocale Λ ->
    aux_state.(mlabel) ->
    cfg Λ →
    aux_state →
    Prop;
}.

Arguments aux_state {_}.
Arguments auxiliary_trace {_}.
Arguments valid_state_evolution {_ _}, {_} _.

Section execution_trace.
  Context {Λ : language}.

  Implicit Types c : cfg Λ.

  Definition valid_exec (ex : execution_trace Λ) : Prop := trace_steps locale_step ex.

  Lemma valid_singleton_exec c : valid_exec (trace_singleton c).
  Proof. constructor. Qed.

  Lemma extend_valid_exec ex c ζ c':
    valid_exec ex →
    trace_ends_in ex c →
    locale_step c ζ c' →
    valid_exec (ex :tr[ζ]: c').
  Proof. econstructor; done. Qed.

  Lemma valid_exec_exec_extend_inv ex ζ c':
    valid_exec (trace_extend ex ζ c') →
    valid_exec ex ∧
    ∃ c, trace_ends_in ex c ∧ locale_step c ζ c'.
  Proof. apply trace_steps_step_inv. Qed.

End execution_trace.

Section system_trace.
  Context `{AS : AuxState Λ}.

  Inductive valid_system_trace : execution_trace Λ → auxiliary_trace AS → Prop :=
  | valid_system_trace_singleton c δ :
      valid_system_trace (trace_singleton c) (trace_singleton δ)
  | valid_system_trace_step ex atr c c' δ' ζ ℓ:
      trace_ends_in ex c →
      locale_step c ζ c' →
      valid_state_evolution ex atr ζ ℓ c' δ' →
      valid_system_trace ex atr →
      valid_system_trace (trace_extend ex ζ c') (trace_extend atr ℓ δ').

  Lemma valid_system_trace_valid_exec_trace ex atr :
    valid_system_trace ex atr → valid_exec ex.
  Proof. induction 1; econstructor; eauto. Qed.

  Lemma valid_system_trace_singletons c δ :
    valid_system_trace (trace_singleton c) (trace_singleton δ).
  Proof. constructor. Qed.

  Lemma valid_system_trace_extend ex atr c c' δ' ζ ℓ:
    valid_system_trace ex atr →
    trace_ends_in ex c →
    locale_step c ζ c' →
    valid_state_evolution ex atr ζ ℓ c' δ' →
    valid_system_trace (trace_extend ex ζ c') (trace_extend atr ℓ δ').
  Proof.
    intros Heatr; revert c c' δ' ζ ℓ.
    induction ex; econstructor; eauto.
  Qed.

  Lemma valid_system_trace_extend_inv ex atr c' δ' ζ ℓ:
    valid_system_trace (trace_extend ex ζ c') (trace_extend atr ℓ δ') →
    ∃ c,
      valid_system_trace ex atr ∧
      trace_ends_in ex c ∧
      locale_step c ζ c' ∧
      valid_state_evolution ex atr ζ ℓ c' δ'.
  Proof. inversion 1; eauto 10. Qed.

  Lemma valid_system_trace_ends_in ex atr :
    valid_system_trace ex atr → ∃ c δ, trace_ends_in ex c ∧ trace_ends_in atr δ.
  Proof.
    inversion 1;
      eauto using trace_extend_ends_in, trace_singleton_ends_in,
      trace_extend_ends_in, trace_singleton_ends_in.
  Qed.

  Lemma valid_system_trace_invariant ex atr (I : cfg Λ → aux_state AS → Prop) :
    (∀ ex atr c δ c' δ' ζ ℓ,
        I c δ →
        trace_ends_in ex c →
        locale_step c ζ c' →
        valid_state_evolution ex atr ζ ℓ c' δ' →
        I c' δ') →
    I (trace_first ex) (trace_first atr) →
    valid_system_trace ex atr →
    I (trace_last ex) (trace_last atr).
  Proof.
    intros HI I0 Hexs.
    induction Hexs as [|??????? Hends]; [done|].
    eapply HI; [|done|done|done].
    rewrite -Hends. by apply IHHexs.
  Qed.

  Lemma trace_steps2_trace_steps (R : aux_state AS -> (mlabel $ aux_state AS) -> aux_state AS -> Prop) :
    (∀ ex atr c δ c' δ' ζ ℓ,
        trace_ends_in ex c →
        trace_ends_in atr δ →
        locale_step c ζ c' →
        valid_state_evolution ex atr ζ ℓ c' δ' →
        R δ ℓ δ') →
    ∀ ex atr, valid_system_trace ex atr → valid_exec ex ∧ trace_steps R atr.
  Proof.
    intros HR ex ex' Hexs.
    induction Hexs as [|??????????? []].
    - split; constructor.
    - split; econstructor; [done|done|done|done|eapply HR=>//|done].
  Qed.

End system_trace.

Section simulation.
  Context {Λ : language} {AS : AuxState Λ}.

  Implicit Types ex : execution_trace Λ.
  Implicit Types atr : auxiliary_trace AS.

  Definition continued_simulation_pre
             (φ : execution_trace Λ → auxiliary_trace AS → Prop)
             (continued_simulation :
                execution_trace Λ → auxiliary_trace AS → Prop) :
    execution_trace Λ → auxiliary_trace AS → Prop :=
    λ ex atr,
    valid_system_trace ex atr ∧
    φ ex atr ∧
    ∀ c c' δ ζ,
      trace_ends_in ex c →
      trace_ends_in atr δ →
      locale_step c ζ c' →
      ∃ δ' ℓ, continued_simulation (trace_extend ex ζ c') (trace_extend atr ℓ δ').

  Local Definition continued_simulation_pre_curried
        (φ : execution_trace Λ → auxiliary_trace AS → Prop) :
    (execution_trace Λ * auxiliary_trace AS → Prop) →
    (execution_trace Λ * auxiliary_trace AS → Prop) :=
    λ ψ (exatr : execution_trace Λ * auxiliary_trace AS),
    (continued_simulation_pre φ (λ ex atr, ψ (ex, atr)) exatr.1 exatr.2).

  Lemma continued_simulation_pre_curried_mono
        (φ : execution_trace Λ → auxiliary_trace AS → Prop) :
    monotone (continued_simulation_pre_curried φ).
  Proof.
    intros P Q HPQ [ex atr] (?&?&HP); repeat (split; first done).
    intros ? ? ? ? ? ? ?.
    edestruct HP as (?&?&?); eauto.
  Qed.

  Definition continued_simulation
             (φ : execution_trace Λ → auxiliary_trace AS → Prop) :=
    λ ex atr, GFX (continued_simulation_pre_curried φ) (ex, atr).

  Lemma continued_simulation_unfold
        (φ : execution_trace Λ → auxiliary_trace AS → Prop) ex atr :
    continued_simulation φ ex atr ↔
    continued_simulation_pre φ (continued_simulation φ) ex atr.
  Proof.
    symmetry; rewrite /continued_simulation /=.
    apply (λ H, GFX_fixpoint (continued_simulation_pre_curried φ) H (_, _)).
    apply continued_simulation_pre_curried_mono.
  Qed.

  Lemma continued_simulation_valid_system_trace Φ ex tr:
    continued_simulation Φ ex tr → valid_system_trace ex tr.
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre; intuition.
  Qed.

  Lemma continued_simulation_rel Φ ex tr:
    continued_simulation Φ ex tr → Φ ex tr.
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre; intuition.
  Qed.

  Lemma continued_simulation_next_aux_state_exists
             (φ : execution_trace Λ → auxiliary_trace AS → Prop)
             (ex : execution_trace Λ) (atr : auxiliary_trace AS)
             (c : cfg Λ) ζ:
    continued_simulation φ ex atr →
    valid_exec (trace_extend ex ζ c) →
    ∃ δℓ ,
      continued_simulation φ (trace_extend ex ζ c) (trace_extend atr δℓ.2 δℓ.1).
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre.
    intros (Hvst & HΦ & Hext) Hvex.
    pose proof (valid_system_trace_ends_in _ _ Hvst) as (c1 & δ1 & Hc1 & Hδ1).
    apply valid_exec_exec_extend_inv in Hvex as [Hvex (c1' & Hc1' & Hstep)].
    pose proof (trace_ends_in_inj _ _ _ Hc1 Hc1'); subst.
    destruct (Hext _ _ _ _ Hc1 Hδ1 Hstep) as (x&y&?).
    by exists (x,y).
  Qed.

  Lemma simulation_does_continue e σ δ φ :
    continued_simulation φ (trace_singleton ([e], σ)) (trace_singleton δ) →
    ∀ ex, trace_starts_in ex ([e], σ) → valid_exec ex →
          ∃ atr, trace_starts_in atr δ ∧ continued_simulation φ ex atr.
  Proof.
    intros Hsm ex Hexstr Hex.
    induction Hex as [|? ? ? ? ? ? ? IHex].
    - apply trace_singleton_starts_in_inv in Hexstr as ->.
      exists (trace_singleton δ). split; [done|].
      eauto using valid_system_trace_singletons.
    - destruct IHex as [atr [Hstarts Hsim]].
      { eapply trace_extend_starts_in_inv; eauto. }
      edestruct (continued_simulation_next_aux_state_exists φ ex atr) as ([??]&?);
        [done| |].
      { econstructor; eauto. }
      eexists. split; [|done].
      by apply trace_extend_starts_in.
  Qed.

End simulation.

Definition inf_execution_trace Λ := inflist (olocale Λ * cfg Λ).

Section inf_execution_trace.
  Context {Λ : language}.

  Definition inf_exec_prepend ζ (c : cfg Λ)
             (iex : inf_execution_trace Λ) : inf_execution_trace Λ :=
    ((ζ, c) :: iex)%inflist.

  CoInductive valid_inf_exec :
    execution_trace Λ → inf_execution_trace Λ → Prop :=
  | valid_inf_exec_singleton ex :
      valid_exec ex → valid_inf_exec ex []%inflist
  | valid_inf_exec_step ex c c' iex ζ:
      valid_exec ex →
      trace_ends_in ex c →
      locale_step c ζ c' →
      valid_inf_exec (trace_extend ex ζ c') iex →
      valid_inf_exec ex (inf_exec_prepend ζ c' iex).

End inf_execution_trace.

Definition inf_auxiliary_trace {Λ} (AS : AuxState Λ) := inflist ((mlabel $ aux_state AS) * AS).

Definition inf_auxtr_prepend `{AS : AuxState Λ}
           ℓ (δ : aux_state AS) (atr : inf_auxiliary_trace AS) := infcons (ℓ,δ) atr.

CoInductive valid_inf_system_trace `{AS : AuxState Λ}
            (Ψ : execution_trace Λ → auxiliary_trace AS → Prop) :
  execution_trace Λ → auxiliary_trace AS →
  inf_execution_trace Λ → inf_auxiliary_trace AS → Prop :=
| valid_inf_system_trace_singleton ex atr :
    Ψ ex atr →
    valid_inf_system_trace Ψ ex atr []%inflist []%inflist
| valid_inf_system_trace_step ex atr c c' δ' iex iatr ζ ℓ:
    Ψ ex atr →
    trace_ends_in ex c →
    locale_step c ζ c' →
    valid_state_evolution ex atr ζ ℓ c' δ' →
    valid_inf_system_trace
      Ψ (trace_extend ex ζ c') (trace_extend atr ℓ δ') iex iatr →
    valid_inf_system_trace
      Ψ ex atr (inf_exec_prepend ζ c' iex) (inf_auxtr_prepend ℓ δ' iatr).

Section simulation.
  Context {Λ : language} {AS : AuxState Λ}
          {φ : execution_trace Λ → auxiliary_trace AS → Prop}.

  Implicit Types ex : execution_trace Λ.
  Implicit Types iex : inf_execution_trace Λ.
  Implicit Types atr : auxiliary_trace AS.

  Lemma valid_system_trace_start_or_contract ex atr :
    valid_system_trace ex atr →
    (ex = {tr[trace_first ex]} ∧ atr = {tr[trace_first atr]}) ∨
    (∃ ex' atr' oζ ℓ, trace_contract ex oζ ex' ∧ trace_contract atr ℓ atr').
  Proof. rewrite /trace_contract; inversion 1; simplify_eq; eauto 10. Qed.

  Lemma valid_system_trace_length ex atr :
    valid_system_trace ex atr → trace_length ex = trace_length atr.
  Proof.
    induction 1 as [|??????????? IHvst]; first done.
    rewrite /= IHvst; done.
  Qed.

  Lemma valid_inf_exec_prepend_valid_exec_extend ex c iex ζ:
    valid_inf_exec ex (inf_exec_prepend ζ c iex) →
    valid_exec (trace_extend ex ζ c).
  Proof.
    inversion 1 as [|???????? Hex]; simplify_eq.
    inversion Hex; done.
  Qed.

  Lemma produce_inf_aux_trace_next_aux_state_exists
        (ex : execution_trace Λ) (atr : auxiliary_trace AS)
        (Hcsm : continued_simulation φ ex atr)
        (c : cfg Λ)
        (ζ: olocale Λ)
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex)) :
    ∃ δℓ, continued_simulation φ (trace_extend ex ζ c) (trace_extend atr δℓ.2 δℓ.1).
  Proof.
    apply continued_simulation_next_aux_state_exists; first done.
    eapply valid_inf_exec_prepend_valid_exec_extend; eauto.
  Qed.

  Definition produce_inf_aux_trace_next_aux_state
             (ex : execution_trace Λ) (atr : auxiliary_trace AS)
             (Hcsm : continued_simulation φ ex atr)
             (c : cfg Λ)
             (ζ: olocale Λ)
             (iex : inf_execution_trace Λ)
             (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex))
    : (aux_state AS * (mlabel $ aux_state AS))%type :=
    epsilon
      (produce_inf_aux_trace_next_aux_state_exists ex atr Hcsm c ζ iex Hvex).

  Definition trace_extend_uncurry (tr: auxiliary_trace AS) xy := trace_extend tr xy.2 xy.1.

  Lemma produce_inf_aux_trace_next_aux_state_continued_simulation
        (ex : execution_trace Λ) (atr : auxiliary_trace AS)
        (Hcsm : continued_simulation φ ex atr)
        (c : cfg Λ)
        (ζ: olocale Λ)
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex)) :
    continued_simulation
      φ
      (trace_extend ex ζ c)
      (trace_extend_uncurry
         atr (produce_inf_aux_trace_next_aux_state ex atr Hcsm c ζ iex Hvex)).
  Proof.
    rewrite /produce_inf_aux_trace_next_aux_state.
    apply epsilon_correct.
  Qed.

  Local Lemma valid_inf_exec_adjust {ex c iex ζ} :
    valid_inf_exec ex ((ζ, c) :: iex)%inflist →
    valid_inf_exec (trace_extend ex ζ c) iex.
  Proof. inversion 1; done. Qed.


  Lemma valid_inf_exe_valid_exec ex iex :
    valid_inf_exec ex iex → valid_exec ex.
  Proof. by destruct 1. Qed.
  Lemma valid_inf_exe_take_drop ex iex n :
    valid_inf_exec ex iex → valid_inf_exec (ex +trl+ inflist_take n iex) (inflist_drop n iex).
  Proof.
    revert ex iex; induction n as [|n IHn]; intros ex iex Hvl; simpl; first done.
    destruct iex as [|[??]]; simpl; first done.
    apply IHn.
    apply valid_inf_exec_adjust; done.
  Qed.

  CoFixpoint produce_inf_aux_trace
          (ex : execution_trace Λ) (atr : auxiliary_trace AS)
          (Hcsm : continued_simulation φ ex atr)
          (iex : inf_execution_trace Λ)
          (Hvex : valid_inf_exec ex iex) :
    inf_auxiliary_trace AS :=
    match iex as l return valid_inf_exec ex l → inf_auxiliary_trace AS with
    | [] => λ _, []
    | (ζ, c) :: iex' =>
      λ Hvex',
      let δℓ :=
          produce_inf_aux_trace_next_aux_state ex atr Hcsm c ζ iex' Hvex'
      in
      (δℓ.2, δℓ.1) :: (produce_inf_aux_trace
              (trace_extend ex ζ c)
              (trace_extend atr δℓ.2 δℓ.1)
              (produce_inf_aux_trace_next_aux_state_continued_simulation
                 ex atr Hcsm c ζ iex' Hvex')
              iex'
              (valid_inf_exec_adjust Hvex'))
    end%inflist Hvex.

  Theorem produced_inf_aux_trace_valid_inf
        (ex : execution_trace Λ) (atr : auxiliary_trace AS)
        (Hcsm : continued_simulation φ ex atr)
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex iex)
    : valid_inf_system_trace
        (continued_simulation φ)
        ex atr
        iex
        (produce_inf_aux_trace ex atr Hcsm iex Hvex).
  Proof.
    revert ex atr Hcsm iex Hvex; cofix CIH; intros ex atr Hcsm iex Hvex.
    destruct iex as [|[ζ c] iex].
    - rewrite [produce_inf_aux_trace _ _ _ _ _]inflist_unfold_fold /=.
      constructor; trivial.
    - rewrite [produce_inf_aux_trace _ _ _ _ _]inflist_unfold_fold /=.
      pose proof (produce_inf_aux_trace_next_aux_state_continued_simulation
                    ex atr Hcsm c ζ iex Hvex) as Hcsm'.
      pose proof (continued_simulation_valid_system_trace _ _ _ Hcsm') as Hvst.
      apply valid_system_trace_extend_inv in Hvst as (?&?&?&?&?).
      econstructor; eauto.
  Qed.

End simulation.
