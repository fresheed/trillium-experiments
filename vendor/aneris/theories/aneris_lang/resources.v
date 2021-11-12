From stdpp Require Import fin_maps gmap.
From iris.algebra Require Import auth gmap frac agree coPset
     gset frac_auth ofe excl.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.proofmode Require Import tactics.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export aneris_lang network.
From trace_program_logic.events Require Import event.
From aneris.aneris_lang Require Import events.
Set Default Proof Using "Type".

Import uPred.
Import ast.

Record Model := model {
  model_state :> Type;
  model_rel :> model_state → model_state → Prop;
  model_state_initial : model_state;
}.

Definition aneris_to_trace_model (M: Model): traces.Model := {|
  mstate := model_state M;
  mlabel := unit;
  mtrans x _ y := model_rel M x y;
  |}.

Record node_gnames := Node_gname {
  heap_name : gname;
  sockets_name : gname;
}.

Definition node_gnamesO :=
  leibnizO node_gnames.
Definition node_gnames_mapUR : ucmra :=
  gmapUR ip_address (agreeR node_gnamesO).
Definition local_heapUR : ucmra :=
  gen_heapUR loc val.
Definition local_socketsUR : ucmra := gen_heapUR socket_handle socket.
Definition free_ipsUR : ucmra :=
  (gset_disjUR ip_address).
Definition free_portsUR : ucmra :=
  gmapUR ip_address (gset_disjUR port).
Definition socket_interpUR : ucmra :=
  gmapUR socket_address (agreeR (leibnizO gname)).
Definition socket_addressesUR : ucmra :=
  gsetUR socket_address.
Definition messagesUR : ucmra :=
  gen_heapUR socket_address (message_soup * message_soup).

Instance system_state_mapUR_unit : Unit (gmap ip_address (agree node_gnames))
  := (∅ : gmap ip_address (agree node_gnames)).
Global Instance system_state_core_id (x : node_gnames_mapUR) : CoreId x.
Proof. apply _. Qed.

Definition socket_interp Σ := message -d> iPropO Σ.

Canonical Structure ModelO (Mdl : Model) := leibnizO Mdl.

Canonical Structure socket_addressO := leibnizO socket_address.

Definition aneris_events := event_obs aneris_lang.

Canonical Structure aneris_eventsO := leibnizO aneris_events.

(** The system CMRA *)
Class anerisG (Mdl : Model) Σ := AnerisG {
  aneris_invG :> invGS Σ;
  (** global tracking of the ghost names of node-local heaps *)
  aneris_node_gnames_mapG :> inG Σ (authR node_gnames_mapUR);
  aneris_node_gnames_name : gname;
  (** local heap *)
  aneris_heapG :> inG Σ (authR local_heapUR);
  (** local sockets *)
  aneris_socketG :> inG Σ (authR local_socketsUR);
  (** free ips *)
  aneris_freeipsG :> inG Σ (authUR free_ipsUR);
  aneris_freeips_name : gname;
  (** free ports  *)
  aneris_freeportsG :> inG Σ (authUR free_portsUR);
  aneris_freeports_name : gname;
  (** socket interpretations *)
  aneris_siG :> inG Σ (authR socket_interpUR);
  aneris_savedPredG :> savedPredG Σ message;
  aneris_si_name : gname;
  (** socket addresses with fixed socket interpretations *)
  aneris_socket_addressesG :> inG Σ (agreeR socket_addressesUR);
  aneris_fixed_name : gname;
  (** message history *)
  aneris_messagesG :> inG Σ (authR messagesUR);
  aneris_messages_name : gname;
  (** model *)
  aneris_model_name : gname;
  anerisG_model :> inG Σ (authUR (optionUR (exclR (ModelO Mdl))));
  (** events *)
  anerisG_allocEVS :> inG Σ (authUR (gmapUR string (exclR aneris_eventsO)));
  anerisG_sendreceiveEVS :>
    inG Σ (authUR (gmapUR socket_address (exclR aneris_eventsO)));
  aneris_allocEVS_name : gname;
  aneris_sendonEVS_name : gname;
  aneris_receiveonEVS_name : gname;
  aneris_observed_send_name : gname;
  aneris_observed_recv_name : gname;
}.

Class anerisPreG Σ (Mdl : Model) := AnerisPreG {
  anerisPre_invGS :> invGpreS Σ;
  anerisPre_node_gnames_mapG :> inG Σ (authR node_gnames_mapUR);
  anerisPre_heapG :> inG Σ (authR local_heapUR);
  anerisPre_socketG :> inG Σ (authR local_socketsUR);
  anerisPre_freeipsG :> inG Σ (authUR free_ipsUR);
  anerisPre_freeportsG :> inG Σ (authUR free_portsUR);
  anerisPre_siG :> inG Σ (authR socket_interpUR);
  anerisPre_savedPredG :> savedPredG Σ message;
  anerisPre_socket_addressesG :> inG Σ (agreeR socket_addressesUR);
  anerisPre_messagesG :> inG Σ (authR messagesUR);
  anerisPre_model :> inG Σ (authUR (optionUR (exclR (ModelO Mdl))));
  anerisPre_allocEVSG :> inG Σ (authUR (gmapUR string (exclR aneris_eventsO)));
  anerisPre_sendreceiveEVSG :>
    inG Σ (authUR (gmapUR socket_address (exclR aneris_eventsO)));
}.

Definition anerisΣ (Mdl : Model) : gFunctors :=
  #[invΣ;
   GFunctor (authR node_gnames_mapUR);
   GFunctor (authR local_heapUR);
   GFunctor (authR local_socketsUR);
   GFunctor (authUR free_ipsUR);
   GFunctor (authUR free_portsUR);
   GFunctor (authR socket_interpUR);
   savedPredΣ message;
   GFunctor (agreeR socket_addressesUR);
   GFunctor (authR messagesUR);
   GFunctor (authUR (optionUR (exclR (ModelO Mdl))));
   GFunctor (authUR (gmapUR string (exclR aneris_eventsO)));
   GFunctor (authUR (gmapUR socket_address (exclR aneris_eventsO)))
].

Global Instance subG_anerisPreG {Σ Mdl} :
  subG (anerisΣ Mdl) Σ → anerisPreG Σ Mdl.
Proof. constructor; solve_inG. Qed.

Section definitions.
  Context `{aG : !anerisG Mdl Σ}.

  Definition auth_st (st : Mdl) : iProp Σ :=
    own aneris_model_name (● Excl' st) ∗ ⌜rtc Mdl Mdl.(model_state_initial) st⌝.
  Definition frag_st (st : Mdl) : iProp Σ :=
    own aneris_model_name (◯ Excl' st) ∗ ⌜rtc Mdl Mdl.(model_state_initial) st⌝.

  (** Authoritative view of the system ghost names *)
  Definition node_gnames_auth (m : gmap ip_address node_gnames) :=
    own (A := authR node_gnames_mapUR)
        aneris_node_gnames_name (● (to_agree <$> m)).

  (** Fragmental view of the system ghost names. *)
  Definition mapsto_node_def (ip : ip_address) (γn : node_gnames) :=
    own (aneris_node_gnames_name) (◯ {[ ip := to_agree γn ]}).
  Definition mapsto_node_aux : seal (@mapsto_node_def). by eexists. Qed.
  Definition mapsto_node := unseal mapsto_node_aux.
  Definition mapsto_node_eq : @mapsto_node = @mapsto_node_def :=
    seal_eq mapsto_node_aux.

  Definition is_node (ip : ip_address) : iProp Σ := ∃ γn, mapsto_node ip γn.

  (** Local heap *)
  Definition heap_ctx (γn : node_gnames) (h : gmap loc val) : iProp Σ :=
    gen_heap_light_ctx (heap_name γn) h.

  Definition mapsto_heap (ip : ip_address)
             (l : loc) (q : Qp) (v : val) : iProp Σ :=
    (∃ γn, mapsto_node ip γn ∗ lmapsto (heap_name γn) l q v)%I.

  (** Local sockets *)
  Definition sockets_ctx (γn : node_gnames)
      (s : gmap socket_handle socket) : iProp Σ :=
    gen_heap_light_ctx (sockets_name γn) s.

  Definition mapsto_socket (ip : ip_address) (z : socket_handle)
             (q : Qp) (s: socket) : iProp Σ :=
    (∃ γn, mapsto_node ip γn ∗ lmapsto (sockets_name γn) z q s)%I.

  (** Free ip addresses *)
  Definition free_ips_auth (A : gset ip_address) : iProp Σ :=
    own aneris_freeips_name (● GSet A).

  Definition free_ip (ip : ip_address) : iProp Σ :=
    own aneris_freeips_name (◯ GSet {[ ip ]}).

  (** Free ports *)
  Definition free_ports_auth (P : gmap ip_address (gset_disjUR port)) : iProp Σ :=
    own aneris_freeports_name (● P).

  Definition free_ports (ip : ip_address) (ports : gset port) : iProp Σ :=
    own aneris_freeports_name (◯ ({[ ip := (GSet ports)]})).

  (** Ghost names of saved socket interpretations *)
  Definition saved_si_auth (sis : gmap socket_address gname) : iProp Σ :=
      own (A:=(authR socket_interpUR)) aneris_si_name (● (to_agree <$> sis)).

  Definition saved_si (a : socket_address) (γ : gname) : iProp Σ :=
    own aneris_si_name (◯ {[ a := to_agree γ ]}).

  (** Socket interpretation [Φ] of address [a] *)
  Definition si_pred a (Φ : socket_interp Σ) : iProp Σ :=
    (∃ γ, saved_si a γ ∗ saved_pred_own γ Φ)%I.

  (** The set [A] of addresses with fixed socket interpretations *)
  Definition fixed (A : gset socket_address) : iProp Σ :=
    own aneris_fixed_name (to_agree A).

    (** The set [A] of addresses for which we track send events. *)
  Definition observed_send (A : gset socket_address) : iProp Σ :=
    own aneris_observed_send_name (to_agree A).

  (** The set [A] of addresses for which we track receive events. *)
  Definition observed_receive (A : gset socket_address) : iProp Σ :=
    own aneris_observed_recv_name (to_agree A).

  Definition alloc_evs_ctx (M : gmap string aneris_events) : iProp Σ :=
    own (A := authUR (gmapUR string (exclR aneris_eventsO)))
        aneris_allocEVS_name (● (Excl <$> M)).

  Definition alloc_evs (lbl : string) (evs : aneris_events) : iProp Σ :=
    own (A := authUR (gmapUR string (exclR aneris_eventsO)))
        aneris_allocEVS_name (◯ {[ lbl := Excl evs]}).

  Definition sendon_evs_ctx (M : gmap socket_address aneris_events) : iProp Σ :=
    own (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
        aneris_sendonEVS_name (● (Excl <$> M)).

  Definition sendon_evs (sa : socket_address) (evs : aneris_events) : iProp Σ :=
    own (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
        aneris_sendonEVS_name (◯ {[ sa := Excl evs]}).

  Definition receiveon_evs_ctx (M : gmap socket_address aneris_events) : iProp Σ :=
    own (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
        aneris_receiveonEVS_name (● (Excl <$> M)).

  Definition receiveon_evs (sa : socket_address) (evs : aneris_events) : iProp Σ :=
    own (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
        aneris_receiveonEVS_name (◯ {[ sa := Excl evs]}).

  (** Messages *)
  Definition messages_ctx
      (s : gmap socket_address (message_soup * message_soup)) : iProp Σ :=
    gen_heap_light_ctx (aneris_messages_name) s.

  Definition mapsto_messages (sa : socket_address) q
             (send_obs receive_obs : bool) (mh : message_soup * message_soup) : iProp Σ :=
    ∃ As Ar, observed_send As ∗ observed_receive Ar ∗
      ⌜(sa ∈ As ↔ (send_obs = true)) ∧ (sa ∈ Ar ↔ (receive_obs = true))⌝ ∗
      lmapsto aneris_messages_name sa q mh.

End definitions.

(** Heap points-to (LaTeX: [\mapsto]) *)
Notation "l ↦[ ip ]{ q } v" := (mapsto_heap ip l q v)
  (at level 20, q at level 50, format "l  ↦[ ip ]{ q }  v") : bi_scope.
Notation "l ↦[ ip ] v" := (l ↦[ip]{1} v)%I
  (at level 20, format "l  ↦[ ip ]  v") : bi_scope.
Notation "l ↦[ ip ]{ q } -" := (∃ v, l ↦[ip]{q} v)%I
  (at level 20, q at level 50, format "l  ↦[ ip ]{ q }  -") : bi_scope.
Notation "l ↦[ ip ] -" := (l ↦[ip]{1} -)%I
  (at level 20, format "l  ↦[ ip ]  -") : bi_scope.

(** Socket points-to (LaTeX: [\hookrightarrow]) *)
Notation "z ↪[ ip ]{ q } s" := (mapsto_socket ip z q s)
  (at level 20, q at level 50, format "z  ↪[ ip ]{ q }  s") : bi_scope.
Notation "z ↪[ ip ] s" := (z ↪[ ip ]{1} s)%I (at level 20) : bi_scope.

(** Messages points-to *)
Notation "a ⤳{ q } s" := (mapsto_messages a q false false s)
  (at level 20, q at level 50, format "a  ⤳{ q }  s") : bi_scope.
Notation "a ⤳ s" := (a ⤳{ 1 } s)%I (at level 20) : bi_scope.
Notation "a ⤳[ bs , br ]{ q } s" := (mapsto_messages a q bs br s)
  (at level 20, q at level 50, format "a  ⤳[ bs ,  br ]{ q }  s") : bi_scope.
Notation "a ⤳[ bs , br ] s" := (a ⤳[bs,br]{ 1 } s)%I (at level 20) : bi_scope.

(** Socket inteerpretation (LaTeX: [\Mapsto]) *)
Notation "a ⤇ Φ" := (si_pred a Φ) (at level 20).

Lemma node_gnames_auth_init `{anerisPreG Σ Mdl} :
  ⊢ |==> ∃ γ, own (A:=authR node_gnames_mapUR) γ (● (to_agree <$> ∅)).
Proof. apply own_alloc. by apply auth_auth_valid. Qed.

Lemma saved_si_init `{anerisPreG Σ Mdl} :
  ⊢ |==> ∃ γ, own (A := authR socket_interpUR) γ (● (to_agree <$> ∅) ⋅ ◯ (to_agree <$> ∅)).
Proof. apply own_alloc. by apply auth_both_valid_discrete. Qed.

Lemma saved_si_update `{anerisG Mdl Σ} (A : gset socket_address) γsi f :
  ⊢ own (A := authR socket_interpUR) γsi (● (to_agree <$> ∅)) ∗
    own (A := authR socket_interpUR) γsi (◯ (to_agree <$> ∅)) ==∗
    ∃ M : gmap socket_address gname,
      ⌜elements (dom (gset socket_address) M) ≡ₚ elements A⌝ ∗
       own (A:=authR socket_interpUR) γsi (● (to_agree <$> M)) ∗
       [∗ map] a ↦ γ ∈ M, own (A:=authR socket_interpUR)
                              γsi (◯ {[ a := (to_agree γ) ]}) ∗
                              saved_pred_own (A:=message) γ (f a).
  iIntros "[Hsi Hsi']".
  pose proof (NoDup_elements A) as Hnd.
  iInduction (elements A) as [|a l] "IHl" forall "Hsi Hsi'".
   - iModIntro. iExists ∅.
     rewrite big_sepM_empty fmap_empty; iFrame.
     iPureIntro. by rewrite dom_empty_L.
   - inversion Hnd as [|? ? ? Hrd']; subst.
     iMod ("IHl" $! Hrd' with "Hsi Hsi'") as (M HMl) "[HM HML]"; iFrame.
     iMod (saved_pred_alloc (f a)) as (γ) "Hγ".
     assert (a ∉ dom (gset _) M) as Hnm.
     { by rewrite -elem_of_elements HMl. }
     iMod (own_update (A:=authR socket_interpUR) _ _
                      (● (<[a := to_agree γ]>(to_agree <$> M)) ⋅
                         (◯ ({[a := to_agree γ]}))) with "HM") as "[HM Hγ']".
     { apply auth_update_alloc. rewrite -insert_empty.
       rewrite /ε /=. apply alloc_local_update; [|done].
       apply not_elem_of_dom. by rewrite dom_fmap. }
     iModIntro.
     iExists (<[a:= γ]> M).
     rewrite !fmap_insert; iFrame.
     rewrite big_sepM_insert; [|by apply not_elem_of_dom].
     iFrame. iPureIntro.
     rewrite dom_insert_L elements_union_singleton //. auto.
Qed.

Lemma socket_addresses_init `{anerisPreG Σ Mdl} A :
  ⊢ |==> ∃ γ, own (A := agreeR (gsetUR socket_address)) γ (to_agree A).
Proof. by apply own_alloc. Qed.

(** Free ports lemmas *)
Lemma free_ports_auth_init `{anerisPreG Σ Mdl} :
  ⊢ |==> ∃ γ, own (A:=authUR (gmapUR ip_address (gset_disjUR port))) γ (● ∅).
Proof. apply own_alloc. by apply auth_auth_valid. Qed.

Lemma free_ips_init `{anerisPreG Σ Mdl} A :
  ⊢ |==> ∃ γ, own γ (● GSet A) ∗ [∗ set] ip ∈ A, own γ (◯ GSet {[ ip ]}).
Proof.
  iMod (own_alloc (● GSet ∅)) as (γ) "HM"; [by apply auth_auth_valid|].
  iAssert (|==>
             ∃ M : gset ip_address,
               (⌜elements M ≡ₚ elements A⌝)
                 ∗ own γ (● GSet M) ∗ [∗ set] ip ∈ M, own γ (◯ GSet {[ ip ]}))%I
    with "[HM]" as "HF".
  { pose proof (NoDup_elements A) as Hnd.
    iInduction (elements A) as [|a l] "IHl".
    - iModIntro. iExists ∅.
      rewrite big_sepS_empty. iFrame.
        by iPureIntro.
    - inversion Hnd as [|? ? ? Hrd']; subst.
      iMod ("IHl" $! Hrd' with "HM") as (M HMl) "[HM HML]"; iFrame.
      assert (a ∉ M) as Hnm.
      { by rewrite -elem_of_elements HMl. }
      iMod (own_update _ _ (● GSet ({[a]} ∪ M) ⋅ ◯ GSet {[a]}) with "HM")
        as "[HM Ha]".
      { apply auth_update_alloc, gset_disj_alloc_empty_local_update.
        set_solver. }
      iModIntro.
      iExists ({[a]} ∪ M); iFrame.
      iSplit; first by iPureIntro; rewrite elements_union_singleton // HMl.
      rewrite big_sepS_insert //. iFrame. }
  iMod "HF" as (M HMF) "[? ?]".
  replace M with A; first by iModIntro; iExists _; iFrame.
  apply set_eq => x.
  rewrite -!elem_of_elements HMF //.
Qed.

Lemma messages_ctx_init `{anerisPreG Σ Mdl} (B As Ar: gset socket_address) γ1 γ2 :
 own γ1 (to_agree As) -∗ own γ2 (to_agree Ar) ==∗ ∃ γ,
      gen_heap_light_ctx
        γ (gset_to_gmap ((∅, ∅) : message_soup * message_soup) B) ∗
        [∗ set] b ∈ B, ∃ As' Ar', own γ1 (to_agree As') ∗ own γ2 (to_agree Ar') ∗
      ⌜(b ∈ As' ↔ ((bool_decide (b ∈ As)) = true)) ∧ (b ∈ Ar' ↔ ((bool_decide (b ∈ Ar)) = true))⌝ ∗
      lmapsto γ b 1 (∅, ∅).
Proof.
  iIntros "#HAs #HAr".
  iMod (gen_heap_light_init
          (∅ : gmap socket_address (message_soup * message_soup))) as (γ) "Hctx".
  set σ' := (gset_to_gmap ((∅, ∅) : message_soup * message_soup) B).
  iMod (gen_heap_light_alloc_gen _ σ' with "Hctx") as "[Hctx HB]".
  { apply map_disjoint_empty_r. }
  rewrite map_union_empty.
  iModIntro. iExists _. iFrame.
  subst σ'.
  iAssert ([∗ map] l↦v ∈ gset_to_gmap ((∅, ∅) : message_soup * message_soup) B, lmapsto γ l 1 (∅, ∅))%I
    with "[HB]" as "HB".
  { iApply big_sepM_mono; simpl; last done.
    intros ??; rewrite lookup_gset_to_gmap_Some; intros [? <-]; done. }
  rewrite big_sepM_dom dom_gset_to_gmap.
  iApply (big_sepS_impl with "HB").
  iIntros "!#" (? ?) "?"; iExists _, _; iFrame "#"; iFrame.
  rewrite !bool_decide_eq_true; eauto.
Qed.

Lemma model_init `{anerisPreG Σ Mdl} (st : Mdl) :
  ⊢ |==> ∃ γ, own γ (● Excl' st) ∗ own γ (◯ Excl' st).
Proof.
  iMod (own_alloc (● Excl' st ⋅ ◯ Excl' st)) as (γ) "[Hfl Hfr]".
  { by apply auth_both_valid_2. }
  iExists _. by iFrame.
Qed.

Lemma alloc_evs_init `{anerisPreG Σ Mdl} (lbls : gset string) :
  ⊢ |==> ∃ γ, own
                (A := authUR (gmapUR string (exclR aneris_eventsO)))
                γ (● (Excl <$> (gset_to_gmap [] lbls))) ∗
              [∗ set] lbl ∈ lbls,
                 own (A := authUR (gmapUR string (exclR aneris_eventsO)))
                     γ (◯ {[ lbl := Excl [] ]}).
Proof.
  iMod (own_alloc (A := authUR (gmapUR string (exclR aneris_eventsO))) (● ∅))
    as (γ) "HM"; [by apply auth_auth_valid|].
  iAssert (|==>
             ∃ M : gset string,
               ⌜elements M ≡ₚ elements lbls⌝
                 ∗ own (A := authUR (gmapUR string (exclR aneris_eventsO)))
                       γ (● (Excl <$> (gset_to_gmap [] M))) ∗
                   [∗ set] lbl ∈ M,
                     own (A := authUR (gmapUR string (exclR aneris_eventsO)))
                         γ (◯ {[ lbl := Excl [] ]}))%I
    with "[HM]" as "HF".
  { pose proof (NoDup_elements lbls) as Hnd.
    iInduction (elements lbls) as [|lbl lbls'] "IHl".
    - iModIntro. iExists ∅.
      rewrite gset_to_gmap_empty fmap_empty big_sepS_empty. iFrame.
        by iPureIntro.
    - inversion Hnd as [|? ? ? Hrd']; subst.
      iMod ("IHl" $! Hrd' with "HM") as (M HMl) "[HM HML]"; iFrame.
      assert (lbl ∉ M) as Hnm.
      { by rewrite -elem_of_elements HMl. }
      iMod (own_update (A := authUR (gmapUR string (exclR aneris_eventsO)))
                       _ _ (● (Excl <$> gset_to_gmap [] ({[lbl]} ∪ M)) ⋅
                            ◯ {[ lbl := Excl [] ]}) with "HM")
        as "[HM Ha]".
      { rewrite gset_to_gmap_union_singleton fmap_insert.
        apply auth_update_alloc. apply: alloc_singleton_local_update; last done.
        rewrite lookup_fmap. by eapply lookup_gset_to_gmap_None in Hnm as ->. }
      iModIntro.
      iExists ({[lbl]} ∪ M); iFrame.
      iSplit; first by iPureIntro; rewrite elements_union_singleton // HMl.
      rewrite big_sepS_insert //. iFrame. }
  iMod "HF" as (M HMF) "[? ?]".
  replace M with lbls; first by iModIntro; iExists _; iFrame.
  apply set_eq => x.
  rewrite -!elem_of_elements HMF //.
Qed.

Lemma sendreceive_evs_init `{anerisPreG Σ Mdl} (sas : gset socket_address) :
  ⊢ |==> ∃ γ, own
                (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
                γ (● (Excl <$> (gset_to_gmap [] sas))) ∗
              [∗ set] sa ∈ sas,
                 own (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
                     γ (◯ {[ sa := Excl [] ]}).
Proof.
  iMod (own_alloc
          (A := authUR (gmapUR socket_address (exclR aneris_eventsO))) (● ∅))
    as (γ) "HM"; [by apply auth_auth_valid|].
  iAssert (|==>
             ∃ M : gset socket_address,
               ⌜elements M ≡ₚ elements sas⌝
                 ∗ own (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
                       γ (● (Excl <$> (gset_to_gmap [] M))) ∗
                   [∗ set] sa ∈ M,
                     own (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
                         γ (◯ {[ sa := Excl [] ]}))%I
    with "[HM]" as "HF".
  { pose proof (NoDup_elements sas) as Hnd.
    iInduction (elements sas) as [|sa sas'] "IHl".
    - iModIntro. iExists ∅.
      rewrite gset_to_gmap_empty fmap_empty big_sepS_empty. iFrame.
        by iPureIntro.
    - inversion Hnd as [|? ? ? Hrd']; subst.
      iMod ("IHl" $! Hrd' with "HM") as (M HMl) "[HM HML]"; iFrame.
      assert (sa ∉ M) as Hnm.
      { by rewrite -elem_of_elements HMl. }
      iMod (own_update (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
                       _ _ (● (Excl <$> gset_to_gmap [] ({[sa]} ∪ M)) ⋅
                            ◯ {[ sa := Excl [] ]}) with "HM")
        as "[HM Ha]".
      { rewrite gset_to_gmap_union_singleton fmap_insert.
        apply auth_update_alloc. apply: alloc_singleton_local_update; last done.
        rewrite lookup_fmap. by eapply lookup_gset_to_gmap_None in Hnm as ->. }
      iModIntro.
      iExists ({[sa]} ∪ M); iFrame.
      iSplit; first by iPureIntro; rewrite elements_union_singleton // HMl.
      rewrite big_sepS_insert //. iFrame. }
  iMod "HF" as (M HMF) "[? ?]".
  replace M with sas; first by iModIntro; iExists _; iFrame.
  apply set_eq => x.
  rewrite -!elem_of_elements HMF //.
Qed.

Section resource_lemmas.
  Context `{aG : !anerisG Mdl Σ}.

  Global Instance mapsto_node_persistent ip γn : Persistent (mapsto_node ip γn).
  Proof. rewrite mapsto_node_eq /mapsto_node_def. apply _. Qed.
  Global Instance mapsto_node_timeless ip γn : Timeless (mapsto_node ip γn).
  Proof. rewrite mapsto_node_eq /mapsto_node_def. apply _. Qed.

  Global Instance is_node_persistent ip : Persistent (is_node ip).
  Proof. apply _. Qed.

  Lemma auth_frag_st_agree st st' :
    auth_st st -∗ frag_st st' -∗ ⌜st = st'⌝.
  Proof.
    iIntros "[Ha %] [Hf %]".
    by iDestruct (own_valid_2 with "Ha Hf") as
        %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete.
  Qed.

  Lemma auth_frag_st_update st st' :
    rtc Mdl Mdl.(model_state_initial) st' →
    auth_st st -∗ frag_st st ==∗ auth_st st' ∗ frag_st st'.
  Proof.
    iIntros (?) "[Hauth %] [Hfrag %]".
    iMod ((own_update _ (● (Excl' st) ⋅ ◯ (Excl' st))
                        (● (Excl' st') ⋅ ◯ (Excl' st')))
             with "[Hauth Hfrag]") as "[??]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    { rewrite own_op //. iFrame. }
    by iFrame "∗ %".
  Qed.

  Lemma frag_st_rtc st :
    frag_st st -∗ ⌜rtc Mdl Mdl.(model_state_initial) st⌝.
  Proof. by iIntros "[_ %]". Qed.

  Lemma mapsto_node_agree ip γn γn' :
    mapsto_node ip γn -∗ mapsto_node ip γn' -∗ ⌜γn = γn'⌝.
  Proof.
    apply wand_intro_r.
    rewrite /node_gnames_auth mapsto_node_eq -own_op own_valid discrete_valid.
    f_equiv=> /auth_frag_valid /=. rewrite singleton_op singleton_valid.
    apply (to_agree_op_inv_L (A := node_gnamesO)).
  Qed.

  Lemma node_gnames_valid ip γn m :
   node_gnames_auth m -∗ mapsto_node ip γn -∗ ⌜m !! ip = Some γn⌝.
  Proof.
    iIntros "H1 H2".
    iCombine "H2" "H1" as "H".
    rewrite /node_gnames_auth mapsto_node_eq -own_op own_valid.
    iDestruct "H" as %HvalidR. iPureIntro.
    revert HvalidR.
    rewrite comm auth_both_valid_discrete.
    rewrite singleton_included_l=> -[[y [Hlookup Hless]] Hvalid].
    assert (Hvalidy := lookup_valid_Some _ ip y Hvalid Hlookup).
    revert Hlookup.
    rewrite lookup_fmap fmap_Some_equiv=> -[v' [Hl Heq]]. revert Hless Heq.
    rewrite Some_included_total.
    destruct (to_agree_uninj y Hvalidy) as [y' <-].
    rewrite to_agree_included.
    intros Heq%leibniz_equiv Heq'%(to_agree_inj y' v')%leibniz_equiv.
    by simplify_eq.
  Qed.

  Lemma node_gnames_alloc γn m ip :
    m !! ip = None →
    node_gnames_auth m ==∗ node_gnames_auth (<[ip:=γn]> m) ∗ mapsto_node ip γn.
  Proof.
    iIntros (?) "Hm". rewrite mapsto_node_eq /mapsto_node_def.
    iMod (own_update _ _
               (● (to_agree <$> (<[ip:=γn]> m)) ⋅ (◯ {[ ip := to_agree γn ]})
                : authR node_gnames_mapUR) with "Hm") as "[Hm Hn]".
    { rewrite fmap_insert. eapply auth_update_alloc.
      apply (alloc_singleton_local_update
               (A := (agreeR node_gnamesO))); last done.
      rewrite -not_elem_of_dom dom_fmap_L not_elem_of_dom //. }
    iModIntro. iFrame.
  Qed.

  Global Instance mapsto_heap_timeless l ip q v :
    Timeless (l ↦[ip]{q} v).
  Proof. apply _. Qed.
  Global Instance mapsto_heap_fractional l ip v :
    Fractional (λ q, l ↦[ip]{q} v)%I.
  Proof.
    rewrite /mapsto_heap /Fractional=> p q. iSplit.
    - iDestruct 1 as (?) "[#? [H1 H2]]".
      iSplitL "H1"; iExists _; eauto.
    - iDestruct 1 as "[H1 H2]".
      iDestruct "H1" as (?) "[Hn1 Hp]".
      iDestruct "H2" as (?) "[Hn2 Hq]".
      iDestruct (mapsto_node_agree with "Hn1 Hn2") as %->.
      iExists _. iFrame.
  Qed.
  Global Instance mapsto_heap_as_fractional l ip q v :
    AsFractional (l ↦[ip]{q} v) (λ q, l ↦[ip]{q} v)%I q.
  Proof. split; [done|]. apply _. Qed.

  Global Instance mapsto_socket_timeless z ip q s :
    Timeless (z ↪[ ip ]{ q } s).
  Proof. apply _. Qed.

  Global Instance mapsto_socket_fractional z ip s :
    Fractional (λ q, z ↪[ip]{q} s)%I.
  Proof.
    rewrite /Fractional=> p q. iSplit.
    - iDestruct 1 as (?) "[#? [H1 H2]]".
      iSplitL "H1"; iExists _; eauto.
    - iDestruct 1 as "[H1 H2]".
      iDestruct "H1" as (?) "[Hn1 Hp]".
      iDestruct "H2" as (?) "[Hn2 Hq]".
      iDestruct (mapsto_node_agree with "Hn1 Hn2") as %->.
      iExists _. iFrame.
  Qed.

  Global Instance mapsto_socket_as_fractional z ip q s :
    AsFractional (z ↪[ip]{q} s) (λ q, z ↪[ip]{q} s)%I q.
  Proof. split; [done|]. apply _. Qed.

  Lemma observed_send_agree A A' :
    observed_send A -∗ observed_send A' -∗ ⌜A = A'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%to_agree_op_valid%leibniz_equiv.
    done.
  Qed.

  Lemma observed_receive_agree A A' :
    observed_receive A -∗ observed_receive A' -∗ ⌜A = A'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%to_agree_op_valid%leibniz_equiv.
    done.
  Qed.

  Global Instance mapsto_messages_timeless a q bs br s :
    Timeless (a ⤳[bs, br]{ q } s).
  Proof. apply _. Qed.

  Global Instance mapsto_messages_fractional a bs br s :
    Fractional (λ q, a ⤳[bs, br]{q} s)%I.
  Proof.
    iIntros (? ?); rewrite /mapsto_messages.
    iSplit.
    - iDestruct 1 as (? ?) "(#?&#?&#?&[H1 H2])"; iSplitL "H1"; iExists _, _; iFrame "#"; done.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (? ?) "(#HAs1&#HAr1&#?&?)".
      iDestruct "H2" as (? ?) "(#HAs2&#HAr2&#?&?)".
      iDestruct (observed_send_agree with "HAs1 HAs2") as %->.
      iDestruct (observed_receive_agree with "HAr1 HAr2") as %->.
      iExists _, _; iFrame "#"; iFrame.
  Qed.

  Global Instance mapsto_messages_as_fractional a q s :
    AsFractional (a ⤳{q} s) (λ q, a ⤳{q} s)%I q.
  Proof. constructor; last apply _; done. Qed.

  Lemma messages_mapsto_observed a q bs br s :
    a ⤳[bs, br]{ q } s -∗
    a ⤳[bs, br]{ q } s ∗
    ∃ As Ar, observed_send As ∗ observed_receive Ar ∗
      ⌜(a ∈ As ↔ (bs = true)) ∧ (a ∈ Ar ↔ (br = true))⌝.
  Proof.
    iDestruct 1 as (? ?) "(#?&#?&#?&?)".
    iSplitL; last by eauto.
    iExists _, _; eauto.
  Qed.

  Lemma heap_mapsto_agree l ip q1 q2 v1 v2 :
    l ↦[ip]{q1} v1 -∗ l ↦[ip]{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "(% & Hn1 & Hv1) (% & Hn2 & Hv2)".
    iDestruct (mapsto_node_agree with "Hn1 Hn2") as %->.
    iApply (lmapsto_agree with "Hv1 Hv2").
  Qed.

  Lemma socket_mapsto_agree z ip q1 q2 s1 s2 :
    z ↪[ip]{q1} s1 -∗ z ↪[ip]{q2} s2 -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "(% & Hn1 & Hv1) (% & Hn2 & Hv2)".
    iDestruct (mapsto_node_agree with "Hn1 Hn2") as %->.
    iApply (lmapsto_agree with "Hv1 Hv2").
  Qed.

  Lemma messages_mapsto_update a bs br R T R' T' mh :
    a ⤳[bs, br] (R, T) ∗ messages_ctx mh ==∗
    a ⤳[bs, br] (R', T') ∗ messages_ctx (<[a := (R',T')]>mh).
  Proof.
    iIntros "(Hl & Ha)".
    iDestruct "Hl" as (??) "(?&?&?&Hl)".
    iMod (gen_heap_light_update _ _ a (R,T) (R', T')
            with "Ha Hl") as "[Ha Hf]".
    eauto with iFrame.
  Qed.

  Lemma messages_mapsto_valid a bs br R T mh :
    a ⤳[bs, br] (R, T) -∗ messages_ctx mh -∗ ⌜mh !! a = Some (R,T)⌝.
  Proof.
    iIntros "Hf Ha".
    iDestruct "Hf" as (??) "(?&?&?&Hf)".
    iApply (gen_heap_light_valid with "Ha Hf"); done.
  Qed.

  Lemma messages_mapsto_agree a bs br bs' br' R T R' T' q1 q2 :
    a ⤳[bs, br]{q1} (R, T) -∗ a ⤳[bs', br']{q2} (R', T') -∗ ⌜bs = bs' ∧ br = br' ∧ R = R' ∧ T = T'⌝.
  Proof.
    iIntros "Ha Ha'".
    iDestruct "Ha" as (??) "(HAs1&HAr1&[%Heq1 %Heq2]&Ha)".
    iDestruct "Ha'" as (??) "(HAs2&HAr2&[%Heq3 %Heq4]&Ha')".
    iDestruct (observed_send_agree with "HAs1 HAs2") as %->.
    iDestruct (observed_receive_agree with "HAr1 HAr2") as %->.
    revert Heq3; rewrite Heq1; intros Heq3.
    revert Heq4; rewrite Heq2; intros Heq4.
    assert (bs = bs' ∧ br = br') as [-> ->].
    { destruct bs; destruct bs'; destruct br; destruct br'; intuition done. }
    iDestruct (lmapsto_agree with "Ha Ha'") as %?.
    by simplify_eq.
  Qed.

  Lemma node_ctx_init σ s :
    ⊢ |==> ∃ (γn : node_gnames), heap_ctx γn σ ∗ sockets_ctx γn s.
  Proof.
    iMod (gen_heap_light_init σ) as (γh) "Hh".
    iMod (gen_heap_light_init s) as (γs) "Hs".
    iExists {| heap_name := γh; sockets_name := γs |}.
    iModIntro. iFrame.
  Qed.

  Lemma fixed_agree A B : fixed A -∗ fixed B -∗ ⌜A = B⌝.
  Proof.
    iIntros "HA HB".
    by iDestruct (own_valid_2 with "HA HB") as %?%to_agree_op_inv_L.
  Qed.

  Global Instance saved_pred_proper `{savedPredG Σ A} n γ:
    Proper ((dist n) ==> (dist n))
           (@saved_pred_own Σ A _ γ : (A -d> iPropO Σ) -d> iPropO Σ).
  Proof.
    intros Φ Ψ Hps.
    f_equiv. destruct n; [done|].
    by apply dist_S.
  Qed.
  Global Instance saved_pred_proper' `{savedPredG Σ A} γ:
    Proper ((≡) ==> (≡)) (@saved_pred_own Σ A _ γ
                          : (A -d> iPropO Σ) -d> iPropO Σ).
  Proof. solve_proper. Qed.
  Global Instance si_pred_prop `{anerisG Mdl Σ} a :
    Proper ((≡) ==> (≡)) (si_pred a).
  Proof. solve_proper. Qed.

  Lemma free_ip_included A ip :
    free_ips_auth A -∗ free_ip ip -∗ ⌜ip ∈ A⌝.
  Proof.
    iIntros "HF Hip". iDestruct (own_valid_2 with "HF Hip") as %[_ Hi].
    iPureIntro.
    move: (Hi 0%nat). rewrite /= left_id.
    move => [? [/to_agree_injN /discrete
                /leibniz_equiv_iff <- [/gset_disj_included ? _]]].
    by apply elem_of_subseteq_singleton.
  Qed.

  Lemma free_ip_dealloc A ip :
    free_ips_auth A -∗ free_ip ip ==∗ free_ips_auth (A ∖ {[ ip ]}).
  Proof.
    iIntros "HF Hip".
    iDestruct (free_ip_included with "HF Hip") as %Hip.
    replace A with ({[ ip ]} ∪ (A ∖ {[ ip ]})) at 1; last first.
    { rewrite (comm_L _ {[ _ ]}) difference_union_L
      -(comm_L _ {[ _ ]}) subseteq_union_1_L //.
        by apply elem_of_subseteq_singleton. }
    iCombine "HF" "Hip" as "H".
    iMod (own_update with "H") as "H"; last by iFrame "H".
    apply auth_update_dealloc.
    rewrite -gset_disj_union; last by set_solver.
      by apply gset_disj_dealloc_empty_local_update.
  Qed.

  Lemma free_ports_included P ip ports :
    free_ports_auth P -∗
    free_ports ip ports -∗
    ∃ ports', ⌜P !! ip = Some (GSet ports') ∧ ports ⊆ ports'⌝.
  Proof.
    iIntros "HP Hip"; rewrite /free_ports_auth /free_ports.
    iDestruct (own_valid_2 with "HP Hip") as
        %[[y [Hy1%leibniz_equiv Hy2]]%singleton_included_l Hv]
         %auth_both_valid_discrete.
    iPureIntro.
    revert Hy2; rewrite Some_included_total.
    destruct y as [ports'|].
    - eexists; split; first by rewrite Hy1.
      by apply gset_disj_included.
    - by specialize (Hv ip); rewrite Hy1 in Hv.
  Qed.

  Lemma free_ports_split ip ports ports' :
    ports ## ports' →
    free_ports ip (ports ∪ ports') ⊣⊢ free_ports ip ports ∗ free_ports ip ports'.
  Proof.
    intros ?.
    by rewrite /free_ports -gset_disj_union //
       -own_op -auth_frag_op singleton_op.
  Qed.

  Lemma free_ports_alloc P ip ports :
    ip ∉ (dom (gset _) P) →
    free_ports_auth P ==∗
    free_ports_auth (<[ ip := GSet ports ]>P) ∗ free_ports ip ports.
  Proof.
    iIntros (?) "HP"; rewrite /free_ports_auth /free_ports.
    iMod (own_update _ _ (● _ ⋅ ◯ {[ ip := (GSet ports)]}) with "HP")
      as "[HP Hip]"; last by iFrame.
    apply auth_update_alloc, alloc_singleton_local_update; last done.
    by eapply (not_elem_of_dom (D := gset ip_address)).
  Qed.

  Lemma free_ports_dealloc P ip ports :
    free_ports_auth P -∗
    free_ports ip ports ==∗
    ∃ ports', ⌜P !! ip = Some (GSet ports') ∧ ports ⊆ ports'⌝ ∗
              free_ports_auth (<[ip := GSet (ports' ∖ ports)]> P).
  Proof.
    iIntros "HP Hip".
    iDestruct (free_ports_included with "HP Hip") as (ports') "[% %]".
    iMod (own_update_2 _ _ _
                       (● <[ip := GSet (ports' ∖ ports)]>P ⋅
                        ◯ <[ ip := GSet ∅ ]>{[ ip := (GSet ports)]})
            with "HP Hip")
      as "[? ?]".
    { apply auth_update.
      eapply insert_local_update;
        [done|eapply (lookup_singleton (M := gmap _))|].
      apply gset_disj_dealloc_local_update. }
      by iExists _; iFrame.
  Qed.

  Lemma socket_interp_alloc a φ sis:
    sis !! a = None →
    saved_si_auth sis ==∗
    ∃ γsi, saved_si_auth (<[a:=γsi]>sis) ∗ a ⤇ φ.
  Proof.
    iIntros (Hnone) "Hsi".
    iMod (saved_pred_alloc φ) as (γsi) "#Hsipred".
    iMod (own_update _ _
            (● (to_agree <$> (<[a:=γsi]> sis)) ⋅ (◯ {[ a := to_agree γsi ]})
             : authR socket_interpUR) with "Hsi") as "[Hsi #sip]".
    { rewrite fmap_insert.
      apply auth_update_alloc, alloc_singleton_local_update; [|done].
      rewrite lookup_fmap Hnone //. }
    iModIntro. iExists _. iFrame. iExists _. iFrame "#".
  Qed.

  Lemma socket_interp_agree a Φ Ψ x :
    a ⤇ Φ -∗ a ⤇ Ψ -∗ ▷ (Φ x ≡ Ψ x).
  Proof.
    iIntros "#H1 #H2".
    iDestruct "H1" as (γ) "[H1 H1']".
    iDestruct "H2" as (γ') "[H2 H2']".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite -auth_frag_op singleton_op in Hvalid.
    apply auth_frag_valid_1, singleton_valid in Hvalid.
    apply (to_agree_op_inv_L γ γ') in Hvalid.
    rewrite Hvalid.
    iDestruct (saved_pred_agree _ _ _ x with "H1' H2'") as "H".
    iExact "H".
  Qed.

  Lemma socket_interp_pred_equiv a Φ Ψ :
    a ⤇ Φ -∗ a ⤇ Ψ -∗ ▷ (Φ ≡ Ψ).
  Proof.
    iIntros "#H1 #H2".
    rewrite discrete_fun_equivI; iIntros (?).
    iApply socket_interp_agree; eauto.
  Qed.

  Lemma alloc_evs_lookup M lbl evs :
    alloc_evs_ctx M -∗ alloc_evs lbl evs -∗ ⌜M !! lbl = Some evs⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hvl ?]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_exclusive_l in Hvl; [|apply _|done].
    apply leibniz_equiv in Hvl.
    rewrite lookup_fmap in Hvl.
    revert Hvl; case: (M !! lbl); intros; simplify_eq/=; done.
  Qed.

  Lemma alloc_evs_update M lbl evs evs' :
    alloc_evs_ctx M -∗
    alloc_evs lbl evs ==∗
    alloc_evs_ctx (<[lbl := evs']>M) ∗ alloc_evs lbl evs'.
  Proof.
    iIntros "H1 H2".
    iDestruct (alloc_evs_lookup with "H1 H2") as %Hlu.
    iMod (own_update_2 (A := authUR (gmapUR string (exclR aneris_eventsO)))
                       _ _ _ (● (Excl <$> <[lbl := evs']>M) ⋅
                              ◯ {[lbl := Excl evs']}) with "H1 H2") as "[$ $]";
      last done.
    apply auth_update.
    rewrite fmap_insert.
    apply: singleton_local_update; last by apply exclusive_local_update.
    rewrite lookup_fmap Hlu; done.
  Qed.

  Lemma sendon_evs_lookup M sa evs :
    sendon_evs_ctx M -∗ sendon_evs sa evs -∗ ⌜M !! sa = Some evs⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hvl ?]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_exclusive_l in Hvl; [|apply _|done].
    apply leibniz_equiv in Hvl.
    rewrite lookup_fmap in Hvl.
    revert Hvl; case: (M !! sa); intros; simplify_eq/=; done.
  Qed.

  Lemma sendon_evs_update M sa evs evs' :
    sendon_evs_ctx M -∗
    sendon_evs sa evs ==∗
    sendon_evs_ctx (<[sa := evs']>M) ∗ sendon_evs sa evs'.
  Proof.
    iIntros "H1 H2".
    iDestruct (sendon_evs_lookup with "H1 H2") as %Hlu.
    iMod (own_update_2 (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
                       _ _ _ (● (Excl <$> <[sa := evs']>M) ⋅
                              ◯ {[sa := Excl evs']}) with "H1 H2") as "[$ $]";
      last done.
    apply auth_update.
    rewrite fmap_insert.
    apply: singleton_local_update; last by apply exclusive_local_update.
    rewrite lookup_fmap Hlu; done.
  Qed.

  Lemma receiveon_evs_lookup M sa evs :
    receiveon_evs_ctx M -∗ receiveon_evs sa evs -∗ ⌜M !! sa = Some evs⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hvl ?]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_exclusive_l in Hvl; [|apply _|done].
    apply leibniz_equiv in Hvl.
    rewrite lookup_fmap in Hvl.
    revert Hvl; case: (M !! sa); intros; simplify_eq/=; done.
  Qed.

  Lemma receiveon_evs_update M sa evs evs' :
    receiveon_evs_ctx M -∗
    receiveon_evs sa evs ==∗
    receiveon_evs_ctx (<[sa := evs']>M) ∗ receiveon_evs sa evs'.
  Proof.
    iIntros "H1 H2".
    iDestruct (receiveon_evs_lookup with "H1 H2") as %Hlu.
    iMod (own_update_2 (A := authUR (gmapUR socket_address (exclR aneris_eventsO)))
                       _ _ _ (● (Excl <$> <[sa := evs']>M) ⋅
                              ◯ {[sa := Excl evs']}) with "H1 H2") as "[$ $]";
      last done.
    apply auth_update.
    rewrite fmap_insert.
    apply: singleton_local_update; last by apply exclusive_local_update.
    rewrite lookup_fmap Hlu; done.
  Qed.

End resource_lemmas.
