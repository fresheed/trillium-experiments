From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import network adequacy.
From aneris.aneris_lang.program_logic Require Export aneris_weakestpre.


Definition aneris_adequate (e :expr) (ip : ip_address) (σ : state)
           (φ : val → Prop) :=
  adequate NotStuck (mkExpr ip e) σ (λ v _, ∃ w, v = mkVal ip w ∧ φ w).

Theorem adequacy `{anerisPreG Σ Mdl} IPs A B
        lbls obs_send_sas obs_rec_sas e ip σ φ :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=> ∃ (f : socket_address → socket_interp Σ),
     fixed A -∗
     ([∗ set] a ∈ A, a ⤇ (f a)) -∗
     ([∗ set] b ∈ B, b ⤳[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas -∗
     WP e @[ip] ⊤ {{ v, ⌜φ v⌝ }}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros HMdlfin Hwp Hipdom Hpiiu Hip Hfixdom Hste Hsce Hmse.
  eapply adequacy; [done| |done|done|done|done|done|done|done].
  intros dg.
  iMod (Hwp dg) as (f) "Hwp".
  iModIntro. iExists _. iIntros "??????????? /=".
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iSpecialize ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  iApply (wp_wand with "Hwp").
  eauto.
Qed.

Theorem adequacy_hoare `{anerisPreG Σ Mdl} IPs A B
        lbls obs_send_sas obs_rec_sas e σ φ ip :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ ∃ (f : socket_address → socket_interp Σ),
          {{{ fixed A ∗
              ([∗ set] a ∈ A, a ⤇ (f a)) ∗
              ([∗ set] b ∈ B, b ⤳[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) ∗
              frag_st Mdl.(model_state_initial) ∗
              ([∗ set] ip ∈ IPs, free_ip ip) ∗
              ([∗ set] lbl ∈ lbls, alloc_evs lbl []) ∗
              ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) ∗
              ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) ∗
              observed_send obs_send_sas ∗
              observed_receive obs_rec_sas }}}
          e @[ip]
      {{{ v, RET v; ⌜φ v⌝ }}}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ i, i ∈ IPs → state_ports_in_use σ !! i = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros ? Hwp ???????.
  eapply adequacy; eauto.
  intros ?. iModIntro.
  iDestruct Hwp as (f) "#Hwp".
  iExists f. iIntros "??????????".
  iApply ("Hwp" with "[$]"); auto.
Qed.
