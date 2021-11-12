From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import
     aneris_lang network resources.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  (** socket_interp_coh *)
  Lemma socket_interp_coh_init ips A M σ f :
    dom (gset _) M = A →
    dom (gset _) (state_ports_in_use σ) = ips →
    (∀ ip, ip ∈ ips → state_ports_in_use σ !! ip = Some ∅) →
    (∀ a, a ∈ A → ip_of_address a ∈ ips) →
    ([∗ set] a ∈ A, a ⤇ f a)%I -∗
    fixed A -∗
    saved_si_auth M -∗
    socket_interp_coh (state_ports_in_use σ).
  Proof.
    iIntros (<- <- Hpiiu Hfixdom) "? ? ?".
    rewrite /socket_interp_coh. iExists _; iFrame.
    iExists _; iFrame; iFrame "#".
    iSplit.
    { iExists _. iFrame. iSplit; [eauto|].
      iApply (big_sepS_mono with "[$]"); auto. }
    iPureIntro. intros b. split; auto.
    intros [Hb | [Hb HP]]; [done|].
    simplify_eq.
    destruct HP as [ps [Hlookup Hin]].
    assert (ip_of_address b ∈ dom (gset string) (state_ports_in_use σ)) as Hdom.
    { apply elem_of_dom. eexists _. apply Hlookup. }
    specialize (Hpiiu (ip_of_address b) Hdom).
    rewrite Hlookup in Hpiiu.
    assert (ps = ∅) by naive_solver; subst. done.
  Qed.

  Lemma socket_interp_coh_fixed_valid a A ips :
    a ∈ A →
    socket_interp_coh ips -∗ fixed A -∗ ∃ φ, a ⤇ φ.
  Proof.
    iIntros (HaA) "Hscoh #HA".
    iDestruct "Hscoh" as (si A') "(HA' & Hsas & H)".
    iDestruct "Hsas" as (sis) "[Hsisauth [<- Hsis]]".
    iDestruct "H" as %Hdom.
    iDestruct (fixed_agree with "HA HA'") as %->.
    iDestruct (big_sepS_elem_of with "Hsis") as "$".
    erewrite Hdom; eauto.
  Qed.

  Lemma socket_interp_coh_socketbind_static ps P a A:
    a ∈ A →
    P !! ip_of_address a = Some ps →
    port_of_address a ∉ ps →
    fixed A -∗
    socket_interp_coh P -∗
    socket_interp_coh (<[ip_of_address a:={[port_of_address a]} ∪ ps]> P).
  Proof.
    iIntros (? Hpsin ?) "HA". rewrite /socket_interp_coh.
    iDestruct 1 as (si A') "(HA' & Hsas & %Hdms)".
    iDestruct (fixed_agree with "HA HA'") as %->.
    iExists _,_. iFrame. iPureIntro.
    intros b.
    rewrite Hdms.
    split; intros [|[Hnb [ps' [HPlookup Hpsin']]]]; auto.
    { right. split; [done|].
      destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
      - eexists _. rewrite Heq lookup_insert. split; [done|].
        rewrite -Heq Hpsin in HPlookup.
        assert (ps = ps') by naive_solver; subst.
        by apply elem_of_union_r.
      - eexists _. by rewrite lookup_insert_ne //. }
    destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
    { right. split; [done|]. eexists _. split; [by rewrite -Heq|].
      rewrite Heq lookup_insert in HPlookup.
      assert ({[port_of_address a]} ∪ ps = ps') by naive_solver; subst.
      apply elem_of_union in Hpsin'.
      destruct Hpsin' as [Hdm%elem_of_singleton_1 | Hdm].
      - destruct a, b; simpl in *. by subst.
      - done. }
    right. split; [done|].
    eexists _. rewrite lookup_insert_ne in HPlookup; done.
  Qed.

  Lemma socket_interp_coh_socketbind_dynamic ps P a A φ :
    a ∉ A →
    P !! ip_of_address a = Some ps →
    port_of_address a ∉ ps →
    fixed A -∗
    socket_interp_coh P ==∗
    socket_interp_coh (<[ip_of_address a:={[port_of_address a]} ∪ ps]> P) ∗
    a ⤇ φ.
  Proof.
    iIntros (? Hpa Hps) "#HA". rewrite /socket_interp_coh.
    iDestruct 1 as (si A') "(HA' & Hsas & %Hdms)".
    iDestruct (fixed_agree with "HA HA'") as %<-.
    iDestruct ("Hsas") as (sis) "[Hsisauth [<- Hsis]]".
    assert (sis !! a = None).
    { destruct (sis !! a) eqn:Heq; last done.
      destruct (Hdms a) as [[|] _]; [ by eapply elem_of_dom_2 | | ]; set_solver. }
    iMod (socket_interp_alloc a φ with "Hsisauth")
      as (?) "[Hsisauth #Hφ]"; [done|].
    iFrame "Hφ". iModIntro. iExists _, _; iFrame "HA'".
    iSplitL "Hsis Hsisauth".
    { iExists _. iFrame "Hsisauth". iSplit; [by iPureIntro|].
      rewrite dom_insert_L big_sepS_insert;
        last rewrite not_elem_of_dom //.
      iFrame. iExists _. iFrame "Hφ". }
    iPureIntro. intros b.
    rewrite dom_insert elem_of_union elem_of_singleton Hdms.
    split.
    - intros [Hb | Hdom]; subst.
      + right. split; [done|]. rewrite lookup_insert. eexists _. split; [done|].
        by apply elem_of_union_l, elem_of_singleton.
      + destruct Hdom as [? | [Hb [ps' [HPlookup Hpsin']]]]; first by left.
        right. split; first done.
        destruct (decide (ip_of_address a = ip_of_address b)) as [Heq |Hneq].
        * destruct Heq. rewrite lookup_insert. intros; simplify_eq.
          eexists _. split; [done|].
          by apply elem_of_union_r.
        * eexists _. by rewrite lookup_insert_ne.
    - intros [Hb | [Hb [ps' [HPlookup Hpsin']]]]; [by auto|].
      destruct (decide (a = b)) as [Heq | Hneq]; [by auto|].
      right; right. split; [done|].
      destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
      + eexists _.
        rewrite Heq lookup_insert in HPlookup.
        rewrite -Heq. split; [eauto|].
        assert ({[port_of_address a]} ∪ ps = ps') by naive_solver; subst.
        apply elem_of_union in Hpsin'. destruct Hpsin' as [Hpsin' | Hport].
        * apply elem_of_singleton_1 in Hpsin'.
          destruct a,b; simpl in *; simplify_eq.
        * intros. destruct Heq; simplify_eq; eauto.
      + intros. eexists _. by rewrite lookup_insert_ne in HPlookup.
  Qed.

End state_interpretation.
