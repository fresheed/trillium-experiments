From iris.proofmode Require Import tactics.
From trace_program_logic.program_logic Require Export adequacy.
From aneris.aneris_lang Require Import
     aneris_lang network resources.
From aneris.prelude Require Import gmultiset.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def
     state_interp_local_coh
     state_interp_gnames_coh
     state_interp_free_ips_coh
     state_interp_network_sockets_coh
     state_interp_socket_interp_coh
     state_interp_messages_resource_coh
     state_interp_messages_history_coh
     state_interp_events
     state_interp_messages_history.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  Lemma config_wp_correct : ⊢ config_wp.
  Proof.
    rewrite /config_wp. iIntros. iModIntro.
    iIntros (ex atr c σ2 Hexvalid Hex Hstep) "(Hevs & Hsi & Hm)". simpl.
    rewrite /state_interp; simplify_eq /=.
    rewrite (last_eq_trace_ends_in ex c) /=; last done.
    iDestruct "Hsi" as (γm mh)
           "(%Hhist & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iApply step_fupd_fupd; iApply step_fupd_intro; first done.
    destruct c as [tp1 σ1]; simpl in *.
    iExists (trace_last atr), ().
    iIntros "!> !>".
    rewrite (aneris_events_state_interp_same_tp _ (tp1, _)); [| |done|done]; last first.
    { econstructor; [done| |done]. econstructor 2; eauto. }
    pose proof Hstep as Hstep'.
    inversion Hstep as [ip σ Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr | σ];
      simplify_eq/=.
    - iFrame "Hm Hevs".
      iSplit; first by iPureIntro; left.
      iExists γm, mh. iFrame "Hsi".
      iSplit.
      { erewrite  <- message_history_evolution_deliver_message; eauto with set_solver. }
      iSplitR; [eauto using gnames_coh_update_sockets|].
      iSplitR; [eauto using network_sockets_coh_deliver_message|].
      iSplitR; [eauto using messages_history_coh_deliver_message|].
      iFrame. iSplitL "Hlcoh".
      { by iApply (local_state_coh_deliver_message with "[Hlcoh]"). }
      iSplitL "Hfreeips". by iApply free_ips_coh_deliver_message.
      rewrite /messages_resource_coh. iApply (big_sepS_mono with "Hmres").
      iIntros (??) "[Hmr|%Hmr]"; last eauto with iFrame. iLeft.
      iDestruct "Hmr" as (phi) "(Hphi & Hphi2)". eauto with iFrame.
    - iSplit; first by iPureIntro; left.
      iFrame "Hevs Hm". iExists γm, mh. iFrame; simpl.
      iSplit.
      { iPureIntro.
        rewrite -message_history_evolution_drop_message; first done.
        apply gmultiset_difference_subseteq. }
      iSplitR; first done.
      iSplitR; first done.
      iSplitR; first by iPureIntro; eapply messages_history_drop_message.
      rewrite /messages_resource_coh. iApply (big_sepS_mono with "Hmres").
      iIntros (??) "[Hmr|%Hmr]"; last eauto with iFrame. iLeft.
      iDestruct "Hmr" as (phi) "(Hphi & Hphi2)". eauto with iFrame.
  Qed.

End state_interpretation.
