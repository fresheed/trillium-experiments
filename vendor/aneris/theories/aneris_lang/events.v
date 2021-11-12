From trace_program_logic.events Require Export event.
From trace_program_logic.program_logic Require Import
     language ectx_language ectxi_language.
From aneris.aneris_lang Require Import aneris_lang base_lang.
From RecordUpdate Require Import RecordSet.

Import ast.
Import RecordSetNotations.

Lemma fill_mkExpr ip K e :
  fill K (mkExpr ip e) = mkExpr ip (fill (Λ := base_ectxi_lang) K e).
Proof.
  induction K as [|? ? IH] using rev_ind; first done.
  rewrite /= !fill_app /= IH //=.
Qed.

Lemma is_Some_to_val_mkExpr ip e :
  is_Some (ectx_language.to_val (mkExpr ip e)) ↔ is_Some (ectx_language.to_val e).
Proof.
  rewrite /= /aneris_to_val /=; destruct (to_val e); simpl.
  - split; eauto.
  - split; intros [? ?]; done.
Qed.

Program Definition allocEV (lbl : string) : Event aneris_lang :=
  {| is_triggered e σ e' σ' :=
       ∃ ip v h (ℓ : loc),
         e = (mkExpr ip (ref<<lbl>> (Val v))%E) ∧
         e' = (mkExpr ip #ℓ) ∧
         σ.(state_heaps) !! ip = Some h ∧
         h !! ℓ = None ∧
         σ' = σ <| state_heaps := <[ip:=<[ℓ:=v]>h]>(state_heaps σ) |>
  |}.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&->&?); done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&h&?&->&?&?&?&?).
  intros K [ip' e1'] He1.
  rewrite fill_mkExpr in He1.
  simplify_eq He1; intros -> He1'.
  rewrite is_Some_to_val_mkExpr.
  eapply (ectx_language.head_ctx_step_val (Λ := base_ectx_lang) _ _ h).
  rewrite /= -He1'; constructor; done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&->&->&?).
  intros Heq; simplify_eq/=.
Qed.

Lemma allocEV_impure lbl eo :
  validEventObservation (allocEV lbl) eo → eo.(pre_state) ≠ eo.(post_state).
Proof.
  destruct 1 as (ip&v&h&ℓ&?&?&Hiplu&Hℓ&Hsts); intros Heq.
  rewrite -Heq in Hsts.
  pose proof (f_equal (λ σ, σ.(state_heaps) !! ip) Hsts) as Hsts2.
  rewrite /= lookup_insert Hiplu in Hsts2.
  simplify_eq Hsts2; intros Hsts3.
  pose proof (f_equal (λ h, h !! ℓ) Hsts3) as Hsts4.
  rewrite /= lookup_insert Hℓ in Hsts4; done.
Qed.

Lemma allocEV_inj lbl lbl' e1 σ1 e2 σ2 :
  allocEV lbl e1 σ1 e2 σ2 → allocEV lbl' e1 σ1 e2 σ2 → lbl = lbl'.
Proof. by intros (?&?&?&?&?&?&?&?&?) (?&?&?&?&?&?&?&?&?); simplify_eq. Qed.

Definition allocObs (ip : ip_address) (lbl : string) (l : loc) (v : val)
           (σ : state) (h : heap) :=
  mkEventObservation
    (mkExpr ip (ref<<lbl>> (Val v)))
    σ
    (mkExpr ip #l)
    (σ <| state_heaps := <[ip:=<[l:=v]>h]>(state_heaps σ) |>).

Definition valid_allocObs (ip : ip_address) (l : loc) (σ : state) (h : heap) :=
  σ.(state_heaps) !! ip = Some h ∧ h !! l = None.

Program Definition sendonEV (sa : socket_address) : Event aneris_lang :=
  {| is_triggered e σ e' σ' :=
       ∃ (sh: socket_handle) (mbody: string) (to: socket_address)
         skts skt r,
         σ.(state_sockets) !! (ip_of_address sa) = Some skts ∧
         skts !! sh = Some (skt, r) ∧
         saddress skt = Some sa ∧
         e = (mkExpr (ip_of_address sa) (SendTo #(LitSocket sh) #mbody #to)) ∧
         e' = (mkExpr (ip_of_address sa) #(String.length mbody)) ∧
         σ' = σ <| state_ms := {[+ mkMessage sa to (sprotocol skt) mbody +]} ⊎ σ.(state_ms) |>
  |}.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&->&?); done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&->&?&?).
  intros K [ip' e1'] He1.
  rewrite fill_mkExpr in He1.
  simplify_eq He1; intros <- He1'.
  eapply (ectx_language.head_ctx_step_val (Λ := aneris_ectx_lang) _ _ σ1).
  rewrite /= fill_mkExpr.
  rewrite /= -He1'. eapply SocketStepS; last done.
  econstructor; done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&->&->&?).
  intros Heq; simplify_eq/=.
Qed.

Lemma sendonEV_impure sa eo :
  validEventObservation (sendonEV sa) eo → eo.(pre_state) ≠ eo.(post_state).
Proof.
  destruct 1 as (sh&mbody&to&skts&skt&r&Hiplu&Hskts&Hskt&?&?&Hsts); intros Heq.
  rewrite -Heq in Hsts.
  set (msg := {| m_sender := sa; m_destination := to; m_protocol := sprotocol skt; m_body := mbody |}).
  pose proof (f_equal (λ σ, multiplicity msg σ.(state_ms)) Hsts) as Hsts2.
  rewrite /= multiplicity_disj_union multiplicity_singleton in Hsts2; lia.
Qed.

Lemma sendonEV_inj sa sa' e1 σ1 e2 σ2 :
  sendonEV sa e1 σ1 e2 σ2 → sendonEV sa' e1 σ1 e2 σ2 → sa = sa'.
Proof.
  destruct sa; destruct sa'.
  intros (?&?&?&?&?&?&?&?&?&?&?&?) (?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=; done.
Qed.

Definition sendonObs (sa : socket_address) (σ : state) (sh : socket_handle) (mbody: string)
           (to : socket_address) (skt : socket) :=
  mkEventObservation
    (mkExpr (ip_of_address sa) (SendTo #(LitSocket sh) #mbody #to))
    σ
    (mkExpr (ip_of_address sa) #(String.length mbody))
    (σ <| state_ms := {[+ mkMessage sa to (sprotocol skt) mbody +]} ⊎ σ.(state_ms) |>).

Definition valid_sendonObs (sa : socket_address) (σ : state) (sh : socket_handle)
           (skts : sockets) (skt : socket) (r : message_soup) :=
  σ.(state_sockets) !! (ip_of_address sa) = Some skts ∧
  skts !! sh = Some (skt, r) ∧
  saddress skt = Some sa.

Program Definition receiveonEV (sa : socket_address) : Event aneris_lang :=
  {| is_triggered e σ e' σ' :=
       ∃ (sh: socket_handle) skts skt r m,
         σ.(state_sockets) !! (ip_of_address sa) = Some skts ∧
         skts !! sh = Some (skt, r) ∧
         saddress skt = Some sa ∧
         m ∈ r ∧
         e = (mkExpr (ip_of_address sa) (ReceiveFrom #(LitSocket sh))) ∧
         e' = (mkExpr (ip_of_address sa) (SOMEV (#(m_body m),#(m_sender m)))) ∧
         σ' = σ <| state_sockets :=
                     <[(ip_of_address sa):= <[sh := (skt, r ∖ {[m]})]>skts]> σ.(state_sockets) |>
  |}.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&->&?); done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&->&?&?).
  intros K [ip' e1'] He1.
  rewrite fill_mkExpr in He1.
  simplify_eq He1; intros <- He1'.
  eapply (ectx_language.head_ctx_step_val (Λ := aneris_ectx_lang) _ _ σ1).
  rewrite /= fill_mkExpr.
  rewrite /= -He1'. eapply SocketStepS; last done.
  econstructor; done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&->&->&?).
  intros Heq; simplify_eq/=.
Qed.

Lemma receiveonEV_impure sa eo :
  validEventObservation (receiveonEV sa) eo → eo.(pre_state) ≠ eo.(post_state).
Proof.
  destruct 1 as (sh&skts&skt&r&m&Hiplu&Hskts&Hskt&Hmr&?&?&Hsts); intros Heq.
  rewrite -Heq in Hsts.
  pose proof (f_equal (λ σ, σ.(state_sockets) !! (ip_of_address sa)) Hsts) as Hsts2.
  rewrite /= lookup_insert Hiplu in Hsts2.
  simplify_eq Hsts2; intros Hsts3.
  pose proof (f_equal (λ h, h !! sh) Hsts3) as Hsts4.
  rewrite /= lookup_insert Hskts in Hsts4.
  set_solver.
Qed.

Lemma receiveonEV_inj sa sa' e1 σ1 e2 σ2 :
  receiveonEV sa e1 σ1 e2 σ2 → receiveonEV sa' e1 σ1 e2 σ2 → sa = sa'.
Proof.
  destruct sa; destruct sa';
    by intros (?&?&?&?&?&?&?&?&?&?&?&?) (?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq/=.
Qed.

Definition receiveonObs (sa : socket_address) (σ : state) (sh : socket_handle) (m: message)
           (skts : sockets) (skt : socket) (r : message_soup) :=
  mkEventObservation
    (mkExpr (ip_of_address sa) (ReceiveFrom #(LitSocket sh)))
    σ
    (mkExpr (ip_of_address sa) (SOMEV (#(m_body m),#(m_sender m))))
    (σ <| state_sockets :=
         <[(ip_of_address sa):= <[sh := (skt, r ∖ {[m]})]>skts]> σ.(state_sockets) |>).

Definition valid_receiveonObs (sa : socket_address) (σ : state) (sh : socket_handle) (m: message)
           (skts : sockets) (skt : socket) (r : message_soup) :=
  σ.(state_sockets) !! (ip_of_address sa) = Some skts ∧
  skts !! sh = Some (skt, r) ∧ saddress skt = Some sa ∧ m ∈ r.

(** if one event is triggered, the other two are not *)
Lemma ev_not_others_alloc lbl e1 σ1 e2 σ2 :
  allocEV lbl e1 σ1 e2 σ2 → (∀ sa, ¬ sendonEV sa e1 σ1 e2 σ2) ∧ (∀ sa, ¬ receiveonEV sa e1 σ1 e2 σ2).
Proof.
  destruct 1 as (?&?&?&?&?&?&?&?&?); simplify_eq.
  split.
  - intros ? (?&?&?&?&?&?&?&?&?&?&?&?); done.
  - intros ? (?&?&?&?&?&?&?&?&?&?&?&?); done.
Qed.

Lemma ev_not_others_sendon sa e1 σ1 e2 σ2 :
  sendonEV sa e1 σ1 e2 σ2 → (∀ lbl, ¬ allocEV lbl e1 σ1 e2 σ2) ∧ (∀ sa, ¬ receiveonEV sa e1 σ1 e2 σ2).
Proof.
  destruct 1 as (?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq.
  split.
  - intros ? (?&?&?&?&?&?&?&?&?); done.
  - intros ? (?&?&?&?&?&?&?&?&?&?&?&?); done.
Qed.

Lemma ev_not_others_receiveon sa e1 σ1 e2 σ2 :
  receiveonEV sa e1 σ1 e2 σ2 → (∀ sa, ¬ sendonEV sa e1 σ1 e2 σ2) ∧ (∀ sa, ¬ allocEV sa e1 σ1 e2 σ2).
Proof.
  destruct 1 as (?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq.
  split.
  - intros ? (?&?&?&?&?&?&?&?&?&?&?&?); done.
  - intros ? (?&?&?&?&?&?&?&?&?); done.
Qed.
