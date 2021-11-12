From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics.
From trace_program_logic.prelude Require Import quantifiers classical_instances.
From trace_program_logic.program_logic Require Export weakestpre adequacy.
From aneris.lib Require Import gen_heap_light.
From aneris.prelude Require Export gmultiset.
From aneris.aneris_lang.state_interp Require Export state_interp.
From aneris.aneris_lang Require Export lang resources network.
Set Default Proof Using "Type".

Definition aneris_model_rel_finitary (Mdl : Model) :=
  ∀ mdl : Mdl, smaller_card {mdl' : Mdl | Mdl mdl mdl'} nat.

Theorem adequacy `{anerisPreG Σ Mdl} IPs A B
        (lbls: gset string)
        (obs_send_sas obs_rec_sas : gset socket_address)
        s e ip σ φ :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=> ∃ (f : socket_address → socket_interp Σ),
     fixed A -∗
     ([∗ set] a ∈ A, a ⤇ (f a)) -∗
     ([∗ set] b ∈ B, b ⤳[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     is_node ip -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas ={⊤}=∗
     WP (mkExpr ip e) @ s; (ip, 0); ⊤ {{v, ⌜φ v⌝ }}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  adequate s (mkExpr ip e) σ (λ v _, φ v).
Proof.
  intros HMdlfin Hwp Hipdom Hpiiu Hip Hfixdom Hste Hsce Hmse.
  eapply (wp_adequacy _ _ _ _ _ _  (Mdl.(model_state_initial) : mstate (aneris_to_trace_model Mdl))).
  { apply aneris_AS_valid_state_evolution_finitary; auto. }
  iIntros (?) "/=".
  iMod node_gnames_auth_init as (γmp) "Hmp".
  iMod saved_si_init as (γsi) "[Hsi Hsi']".
  iMod (socket_addresses_init A) as (γsif) "#Hsif".
  iMod (free_ips_init IPs) as (γips) "[HIPsCtx HIPs]".
  iMod free_ports_auth_init as (γpiu) "HPiu".
  iMod (socket_addresses_init obs_send_sas) as
      (γobserved_send) "#Hobserved_send".
  iMod (socket_addresses_init obs_rec_sas) as
      (γobserved_receive) "#Hobserved_receive".
  iMod (messages_ctx_init B with "Hobserved_send Hobserved_receive" ) as (γms) "[Hms HB]".
  iMod (model_init Mdl.(model_state_initial)) as (γm) "[Hmfull Hmfrag]".
  assert (rtc Mdl Mdl.(model_state_initial) Mdl.(model_state_initial)).
  { constructor. }
  iMod (alloc_evs_init lbls) as (γalevs) "[Halobctx Halobs]".
  iMod (sendreceive_evs_init obs_send_sas) as
      (γsendevs) "[Hsendevsctx Hsendevs]".
  iMod (sendreceive_evs_init obs_rec_sas) as
      (γreceiveevs) "[Hreceiveevsctx Hreceiveevs]".
  set (dg :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_fixed_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
           aneris_messages_name := γms;
           aneris_model_name := γm;
           aneris_allocEVS_name := γalevs;
           aneris_sendonEVS_name := γsendevs;
           aneris_receiveonEVS_name := γreceiveevs;
           aneris_observed_send_name := γobserved_send;
           aneris_observed_recv_name := γobserved_receive;
         |}).
  iMod (Hwp dg) as (f) "Hwp".
  iMod (saved_si_update A with "[$Hsi $Hsi']") as (M HMfs) "[HM #Hsa]".
  assert (dom (gset _) M = A) as Hdmsi.
  { apply set_eq => ?.
    split; intros ?%elem_of_elements;
      apply elem_of_elements; [by rewrite -HMfs|].
    by rewrite HMfs. }
  iAssert ([∗ set] s ∈ A, s ⤇ f s)%I as "#Hsa'".
  { rewrite -Hdmsi -!big_sepM_dom.
    iApply (big_sepM_mono with "[$Hsa]"); simpl; auto.
    iIntros (? ? Hx) "[? ?]"; iExists _; iFrame. }
  iMod (node_ctx_init ∅ ∅) as (γn) "[Hh Hs]".
  iMod (node_gnames_alloc γn _ ip with "[$]") as "[Hmp #Hγn]"; [done|].
  iAssert (is_node ip) as "Hn".
  { iExists _. eauto. }
  iExists
    (λ ex atr,
     aneris_events_state_interp ex ∗
     aneris_state_interp
       (trace_last ex).2
       (trace_messages_history ex) ∗
     auth_st (trace_last atr))%I, (λ _ _, True)%I.
  simpl.
  iSplitR; [iApply config_wp_correct|].
  iSplitR "Hwp HIPs HB Hmfrag Halobs Hsendevs Hreceiveevs"; last first.
  { iMod ("Hwp" with "Hsif Hsa' HB [$Hmfrag //] HIPs Hn Halobs Hsendevs
                        Hreceiveevs Hobserved_send Hobserved_receive") ; done. }
  iModIntro.
  iPoseProof (aneris_events_state_interp_init with "[$] [$] [$] [$] [$]") as "$".
  rewrite Hmse gset_of_gmultiset_empty.
  iPoseProof (@aneris_state_interp_init _ _ dg IPs _ _ _ _ _
                with "[$Hmp] [//] [$Hh] [$Hs] [$Hms] [//] [$HM] [//] [$HIPsCtx] [$HPiu] ")
    as "$"; [done|done|done|done|done|done|done|done|].
  iFrame "Hmfull".
  done.
Qed.

Definition safe e σ := @adequate aneris_lang NotStuck e σ (λ _ _, True).

Theorem adequacy_safe `{anerisPreG Σ Mdl} IPs A B
        lbls obs_send_sas obs_rec_sas e ip σ :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=> ∃ (f : socket_address → socket_interp Σ),
     fixed A -∗
     ([∗ set] a ∈ A, a ⤇ (f a)) -∗
     ([∗ set] b ∈ B, b ⤳[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     is_node ip -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas ={⊤}=∗
     WP (mkExpr ip e) @ (ip, 0) {{v, True }}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  safe (mkExpr ip e) σ.
Proof. by apply adequacy. Qed.

Theorem adequacy_hoare `{anerisPreG Σ Mdl} IPs A B
        lbls obs_send_sas obs_rec_sas e σ φ ip :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ ∃ (f : socket_address → socket_interp Σ),
          {{{ fixed A ∗
              ([∗ set] a ∈ A, a ⤇ (f a)) ∗
              ([∗ set] b ∈ B, b ⤳[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) ∗
              frag_st Mdl.(model_state_initial) ∗
              ([∗ set] ip ∈ IPs, free_ip ip) ∗
              is_node ip ∗
              ([∗ set] lbl ∈ lbls, alloc_evs lbl []) ∗
              ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) ∗
              ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) ∗
              observed_send obs_send_sas ∗
              observed_receive obs_rec_sas }}}
          (mkExpr ip e) @ (ip, 0)
          {{{ v, RET v; ⌜φ v⌝ }}}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ i, i ∈ IPs → state_ports_in_use σ !! i = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  adequate NotStuck (mkExpr ip e) σ (λ v _, φ v).
Proof.
  intros ? Hwp ???????.
  eapply adequacy; try eauto.
  intros ?. iModIntro.
  iDestruct Hwp as (f) "#Hwp".
  iExists f. iIntros "???????????".
  iApply ("Hwp" with "[$]"); auto.
Qed.

Definition simulation_adequacy_with_trace_inv Σ Mdl `{!anerisPreG Σ Mdl} (s: stuckness)
           (IPs: gset ip_address)
           (lbls : gset string)
           (A B obs_send_sas obs_rec_sas : gset socket_address)
           (ξ: execution_trace aneris_lang → auxiliary_trace aneris_AS → Prop)
           ip e1 σ1 :
  (* The model has finite branching *)
  valid_state_evolution_finitary (@aneris_AS Mdl) ξ ->
  (* The initial configuration satisfies certain properties *)
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ1) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ1 !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ1 = {[ip:=∅]} →
  state_sockets σ1 = {[ip:=∅]} →
  state_ms σ1 = ∅ →
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!anerisG Mdl Σ},
      ⊢ |={⊤}=>
        (* There exists a trace invariant, a postcondition and a socket interpretation function *)
        ∃ (trace_inv : execution_trace aneris_lang → auxiliary_trace aneris_AS → iProp Σ)
          Φ (f : socket_address → socket_interp Σ),
          (* Given resources reflecting initial configuration, we need to prove two goals *)
          fixed A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
          ([∗ set] b ∈ B, b ⤳[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
          ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
          ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
          ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
          ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
          observed_send obs_send_sas -∗
          observed_receive obs_rec_sas -∗
          frag_st Mdl.(model_state_initial) ={⊤}=∗
          WP (mkExpr ip e1) @ s; (ip, 0); ⊤ {{ Φ }} ∗
          (∀ (ex : execution_trace aneris_lang) (atr : auxiliary_trace aneris_AS) δ3 c3,
              ⌜valid_system_trace ex atr⌝ -∗
              ⌜trace_starts_in ex ([mkExpr ip e1], σ1)⌝ -∗
              ⌜trace_starts_in atr Mdl.(model_state_initial)⌝ -∗
              ⌜trace_ends_in ex c3⌝ -∗
              ⌜trace_ends_in atr δ3⌝ -∗
              ⌜∀ ex' atr' oζ ℓ,
                trace_contract ex oζ ex' → trace_contract atr ℓ atr' →
                ξ ex' atr' ∧
                valid_state_evolution aneris_AS ex' atr' oζ ℓ (trace_last ex) (trace_last atr)⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c3.1 → not_stuck e2 c3.2⌝ -∗
         state_interp ex atr -∗
         posts_of c3.1 (Φ :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [mkExpr ip e1] (drop (length [mkExpr ip e1]) c3.1)))) -∗
         □ (state_interp ex atr ∗
             (∀ ex' atr' oζ ℓ, ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
            ={⊤}=∗ state_interp ex atr ∗ trace_inv ex atr) ∗
         ((∀ ex' atr' oζ ℓ,
              ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
          ={⊤, ∅}=∗ ⌜ξ ex atr⌝))) →
  (* The coinductive pure coq proposition given by adequacy *)
  (continued_simulation ξ (trace_singleton ([(mkExpr ip e1)], σ1))
                          (trace_singleton Mdl.(model_state_initial)) ∧
     adequate s (mkExpr ip e1) σ1 (λ v _, True)).
Proof.
  intros Hsc Hips Hdom Hports Hsa Hheaps Hsockets Hms Hwp.
  unfold safe.
  assert (EqDecision (aneris_AS (Mdl := Mdl))).
  { intros ??. apply make_decision. }
  apply (sim_and_adequacy_xi aneris_lang aneris_AS Σ s ξ (mkExpr ip e1) σ1 Mdl.(model_state_initial)) =>//.
  iIntros (?) "".
  iMod node_gnames_auth_init as (γmp) "Hmp".
  iMod saved_si_init as (γsi) "[Hsi Hsi']".
  iMod (socket_addresses_init A) as (γsif) "#Hsif".
  iMod (free_ips_init IPs) as (γips) "[HIPsCtx HIPs]".
  iMod free_ports_auth_init as (γpiu) "HPiu".
  iMod (socket_addresses_init obs_send_sas) as
      (γobserved_send) "#Hobserved_send".
  iMod (socket_addresses_init obs_rec_sas) as
      (γobserved_receive) "#Hobserved_receive".
  iMod (messages_ctx_init B with "Hobserved_send Hobserved_receive") as (γms) "[Hms HB]".
  iMod (model_init Mdl.(model_state_initial)) as (γm) "[Hmdl_auth Hmdl_frag]".
  iMod (alloc_evs_init lbls) as (γalevs) "[Halobctx Halobs]".
  iMod (sendreceive_evs_init obs_send_sas) as
      (γsendevs) "[Hsendevsctx Hsendevs]".
  iMod (sendreceive_evs_init obs_rec_sas) as
      (γreceiveevs) "[Hreceiveevsctx Hreceiveevs]".
  set (distG :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_fixed_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
           aneris_messages_name := γms;
           aneris_model_name := γm;
           aneris_allocEVS_name := γalevs;
           aneris_sendonEVS_name := γsendevs;
           aneris_receiveonEVS_name := γreceiveevs;
           aneris_observed_send_name := γobserved_send;
           aneris_observed_recv_name := γobserved_receive;
         |}).
  iMod (Hwp distG) as "Hwp". iDestruct "Hwp" as (trace_inv Φ f) "Himpl".
  iMod (saved_si_update A with "[$Hsi $Hsi']") as (M HMfs) "[HM #Hsa]".
  assert (dom (gset _) M = A) as Hdmsi.
  { apply set_eq => ?.
    split; intros ?%elem_of_elements;
      apply elem_of_elements; [by rewrite -HMfs|].
    by rewrite HMfs. }
  iAssert ([∗ set] s ∈ A, s ⤇ f s)%I as "#Hsa'".
  { rewrite -Hdmsi -!big_sepM_dom.
    iApply (big_sepM_mono with "[$Hsa]"); simpl; auto.
    iIntros (? ? Hx) "[? ?]"; iExists _; iFrame. }
  iMod (node_ctx_init ∅ ∅) as (γn) "[Hh Hs]".
  iMod (node_gnames_alloc γn _ ip with "[$]") as "[Hmp #Hγn]"; [done|].
  iAssert (is_node ip) as "Hn".
  { iExists _. eauto. }
  iMod ("Himpl" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$Hmdl_frag //]")
    as "[Hwp Himpl]".
  iModIntro. iExists state_interp, trace_inv, Φ, fork_post.
  iSplitL ""; first by iApply config_wp_correct.
  iFrame "Hwp".
  iPoseProof (aneris_events_state_interp_init with "[$] [$] [$] [$] [$]") as "$".
  iPoseProof (@aneris_state_interp_init _ _ distG IPs _ _ _ _ _
                with "[Hmp] [] [Hh] [Hs] [Hms] [] [HM] [] [HIPsCtx] [HPiu] ")
    as "Hsi"; eauto; [].
  rewrite /= Hms gset_of_gmultiset_empty.
  iFrame; done.
Qed.

Definition simulation_adequacy_advanced_finiteness Σ Mdl `{!anerisPreG Σ Mdl} (s: stuckness)
           (IPs: gset ip_address)
           (lbls : gset string)
           (A B obs_send_sas obs_rec_sas : gset socket_address)
           (ξ: execution_trace aneris_lang → auxiliary_trace aneris_AS → Prop)
           ip e1 σ1 :
  (* The model has finite branching *)
  valid_state_evolution_finitary (@aneris_AS Mdl) ξ ->
  (* The initial configuration satisfies certain properties *)
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ1) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ1 !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ1 = {[ip:=∅]} →
  state_sockets σ1 = {[ip:=∅]} →
  state_ms σ1 = ∅ →
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!anerisG Mdl Σ},
      ⊢ |={⊤}=>
        (* There exists a postcondition and a socket interpretation function *)
        ∃ Φ (f : socket_address → socket_interp Σ),
          (* Given resources reflecting initial configuration, we need *)
  (*            to prove two goals *)
          fixed A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
          ([∗ set] b ∈ B, b ⤳[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
          ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
          ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
          ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
          ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
          observed_send obs_send_sas -∗
          observed_receive obs_rec_sas -∗
          frag_st Mdl.(model_state_initial) ={⊤}=∗
          WP (mkExpr ip e1) @ s; (ip, 0); ⊤ {{ Φ }} ∗
          (∀ (ex : execution_trace aneris_lang) (atr : auxiliary_trace aneris_AS) δ3 c3,
            ⌜valid_system_trace ex atr⌝ -∗
            ⌜trace_starts_in ex ([mkExpr ip e1], σ1)⌝ -∗
            ⌜trace_starts_in atr Mdl.(model_state_initial)⌝ -∗
            ⌜trace_ends_in ex c3⌝ -∗
            ⌜trace_ends_in atr δ3⌝ -∗
            ⌜∀ ex' atr' oζ ℓ,
             trace_contract ex oζ ex' → trace_contract atr ℓ atr' →
             ξ ex' atr' ∧
             valid_state_evolution aneris_AS ex' atr' oζ ℓ (trace_last ex) (trace_last atr)⌝ -∗
            ⌜∀ e2, s = NotStuck → e2 ∈ c3.1 → not_stuck e2 c3.2⌝ -∗
            state_interp ex atr -∗
            posts_of c3.1 (Φ :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [mkExpr ip e1] (drop (length [mkExpr ip e1]) c3.1)))) -∗
            |={⊤, ∅}=> ⌜ξ ex atr⌝)) →
  (* The coinductive pure coq proposition given by adequacy *)
  (continued_simulation
    ξ
    (trace_singleton ([(mkExpr ip e1)], σ1))
    (trace_singleton Mdl.(model_state_initial)) ∧
     adequate s (mkExpr ip e1) σ1 (λ v _, True)).
Proof.
  intros Hsc Hips Hdom Hports Hsa Hheaps Hsockets Hms Hwp.
  eapply simulation_adequacy_with_trace_inv; [done..|].
  iIntros (?) "".
  iMod Hwp as (Φ f) "Hwp".
  iModIntro.
  iExists (λ _ _, True)%I, Φ, f.
  iIntros "? ? ? ? ? ? ? ? ? ? ?".
  iMod ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "[$ Hstep]".
  iModIntro.
  iIntros (ex atr δ3 c3 ? ? ? ? ? ? ?) "HSI Hposts".
  iSplit; last first.
  { iIntros "_". iApply ("Hstep" with "[] [] [] [] [] [] [] HSI"); auto. }
  iModIntro; iIntros "[$ _]"; done.
Qed.

(* Notations on executions
 * |-----------ex'-------|
 * |-----------ex-----------|
 * x1 ----------------- x2 x3
 *)
Definition simulation_adequacy Σ Mdl `{!anerisPreG Σ Mdl} (s: stuckness)
           (IPs: gset ip_address)
           (lbls : gset string)
           (A B obs_send_sas obs_rec_sas : gset socket_address)
           (ξ: execution_trace aneris_lang → auxiliary_trace aneris_AS → Prop)
           ip e1 σ1 :
  (* The model has finite branching *)
  aneris_model_rel_finitary Mdl →
  (* The initial configuration satisfies certain properties *)
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ1) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ1 !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ1 = {[ip:=∅]} →
  state_sockets σ1 = {[ip:=∅]} →
  state_ms σ1 = ∅ →
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!anerisG Mdl Σ},
      ⊢ |={⊤}=>
        (* There exists a postcondition and a socket interpretation function *)
        ∃ Φ (f : socket_address → socket_interp Σ),
          (* Given resources reflecting initial configuration, we need *)
  (*            to prove two goals *)
          fixed A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
          ([∗ set] b ∈ B, b ⤳[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
          ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
          ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
          ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
          ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
          observed_send obs_send_sas -∗
          observed_receive obs_rec_sas -∗
          frag_st Mdl.(model_state_initial) ={⊤}=∗
          WP (mkExpr ip e1) @ s; (ip, 0); ⊤ {{ Φ }} ∗
          (∀ (ex : execution_trace aneris_lang) (atr : auxiliary_trace aneris_AS) δ3 c3,
            ⌜valid_system_trace ex atr⌝ -∗
            ⌜trace_starts_in ex ([mkExpr ip e1], σ1)⌝ -∗
            ⌜trace_starts_in atr Mdl.(model_state_initial)⌝ -∗
            ⌜trace_ends_in ex c3⌝ -∗
            ⌜trace_ends_in atr δ3⌝ -∗
            ⌜∀ ex' atr' oζ ℓ,
             trace_contract ex oζ ex' → trace_contract atr ℓ atr' →
             ξ ex' atr' ∧
             valid_state_evolution aneris_AS ex' atr' oζ ℓ (trace_last ex) (trace_last atr)⌝ -∗
            ⌜∀ e2, s = NotStuck → e2 ∈ c3.1 → not_stuck e2 c3.2⌝ -∗
            state_interp ex atr -∗
            posts_of c3.1 (Φ :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [mkExpr ip e1] (drop (length [mkExpr ip e1]) c3.1)))) -∗
            |={⊤, ∅}=> ⌜ξ ex atr⌝)) →
  (* The coinductive pure coq proposition given by adequacy *)
  continued_simulation
    ξ
    (trace_singleton ([(mkExpr ip e1)], σ1))
    (trace_singleton Mdl.(model_state_initial)).
Proof.
  intros Hsc Hips Hdom Hports Hsa Hheaps Hsockets Hms Hwp.
  eapply simulation_adequacy_with_trace_inv =>//.
  { apply aneris_AS_valid_state_evolution_finitary; auto. }
  iIntros (?) "".
  iMod Hwp as (Φ f) "Hwp".
  iModIntro.
  iExists (λ _ _, True)%I, Φ, f.
  iIntros "? ? ? ? ? ? ? ? ? ? ?".
  iMod ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "[$ Hstep]".
  iModIntro.
  iIntros (ex atr δ3 c3 ? ? ? ? ? ? ?) "HSI Hposts".
  iSplit; last first.
  { iIntros "_". iApply ("Hstep" with "[] [] [] [] [] [] [] HSI"); auto. }
  iModIntro; iIntros "[$ _]"; done.
Qed.
