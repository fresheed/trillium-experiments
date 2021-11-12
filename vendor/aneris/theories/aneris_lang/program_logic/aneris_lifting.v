From iris.proofmode Require Import tactics.
From trace_program_logic.program_logic Require Export weakestpre lifting.
From aneris.aneris_lang Require Import lang base_lang lifting state_interp.
From aneris.aneris_lang.program_logic Require Export aneris_weakestpre.
From aneris.aneris_lang.state_interp Require Import state_interp_def.
From RecordUpdate Require Import RecordSet.

Set Default Proof Using "Type".

Import uPred.

Import RecordSetNotations.

Section lifting_pure_exec.
  Context `{anerisG Mdl Σ}.

  Implicit Types ip : ip_address.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.

  Lemma aneris_wp_pure_step_fupd ip E E' e1 e2 φ n Φ :
    PureExec φ n (mkExpr ip e1) (mkExpr ip e2) →
    φ →
    (|={E}[E']▷=>^n WP e2 @[ip] E {{ Φ }}) ⊢ WP e1 @[ip] E {{ Φ }}.
  Proof.
    rewrite (aneris_wp_unfold _ _ e1) /aneris_wp_def.
    iIntros (Hexec Hφ) "Hwp %tid #Hin".
    iApply (wp_pure_step_fupd _ _ E'); first done.
    clear φ Hφ e1 Hexec.
    iInduction n as [|n] "IH"; simpl.
    - rewrite aneris_wp_unfold /aneris_wp_def.
      iApply "Hwp"; done.
    - iMod "Hwp"; iModIntro; iNext; iMod "Hwp"; iModIntro.
      iApply ("IH" with "Hwp"); eauto.
  Qed.

  Lemma aneris_wp_pure_step_later ip E e1 e2 φ n Φ :
    PureExec φ n (mkExpr ip e1) (mkExpr ip e2) →
    φ →
    ▷^n WP e2 @[ip] E {{ Φ }} ⊢ WP e1 @[ip] E {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -aneris_wp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed.

End lifting_pure_exec.

Section lifting_mdl.
  Context `{anerisG Mdl Σ}.

  Lemma aneris_wp_atomic_take_step_model ip Φ e E1 E2
        `{!Atomic WeaklyAtomic (mkExpr ip e)} :
    TCEq (to_val e) None →
    (|={E1,E2}=>
     ∃ m m', frag_st m ∗ ⌜m = m' ∨ Mdl m m'⌝ ∗
     WP e @[ip] E2 {{ v, frag_st m' ={E2,E1}=∗ Φ v }}) ⊢ WP e @[ip] E1 {{ Φ }}.
  Proof.
    iIntros (He) "H".
    iApply (aneris_wp_atomic_take_step ip E1 E2).
    iMod "H" as "H".
    iModIntro. iIntros (ex atr c1 Hex) "Hsi".
    iDestruct "H" as (m m') "(Hfrag & %Hm & Hwp)".
    iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as %Heq.
    iModIntro.
    iExists (True)%I, (frag_st m')%I.
    iFrame "Hsi".
    iSplitR "Hwp".
    - iIntros (c2 δ2 [] ?).
      iExists m', tt.
      iIntros "(Hsi&%Hval&_)".
      iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as %<-.
      iMod (aneris_state_interp_model_extend with "Hsi Hfrag [//]") as "[[? ?] ?]".
      iModIntro; iFrame; simplify_eq/=; done.
    - iSplitR; [by iFrame; iIntros "$"|]. by iApply "Hwp".
  Qed.

  Lemma aneris_wp_suttering_atomic_take_step_model ip Φ e E1 E2
        `{!StutteringAtomic WeaklyAtomic (mkExpr ip e)} :
    TCEq (to_val e) None →
    (|={E1,E2}=>
     ∃ m m', frag_st m ∗ ⌜m = m' ∨ Mdl m m'⌝ ∗
     WP e @[ip] E2 {{ v, frag_st m' ={E2,E1}=∗ Φ v }}) ⊢ WP e @[ip] E1 {{ Φ }}.
  Proof.
    iIntros (He) "H".
    iApply (aneris_wp_stuttering_atomic_take_step ip E1 E2).
    iMod "H" as "H".
    iModIntro. iIntros (ex atr c1 Hex) "Hsi".
    iDestruct "H" as (m m') "(Hfrag & %Hm & Hwp)".
    iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as %Heq.
    iModIntro.
    iExists (True)%I, (frag_st m')%I.
    iFrame "Hsi".
    iSplitR "Hwp".
    - iIntros (c2 δ2 ? ?).
      iExists m'.
      iIntros "(Hsi&%Hval&_)".
      iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as %<-.
      iMod (aneris_state_interp_model_extend _ _ _ atr with "Hsi Hfrag [//]") as "[[? ?] ?]".
      iModIntro; iFrame; simplify_eq/=; done.
    - iSplitR; [by iFrame; iIntros "$"|]. by iApply "Hwp".
  Qed.

End lifting_mdl.

Section lifting_node_local.
  Context `{anerisG Mdl Σ}.

  Implicit Types ip : ip_address.
  Implicit Types P : iProp Σ.
  Implicit Types Ψ Φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.
  Implicit Types σ : state.
  Implicit Types M R T : message_soup.
  Implicit Types m : message.
  Implicit Types A B : gset socket_address.
  Implicit Types a : socket_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.

  (** Fork *)
  Lemma aneris_wp_fork ip E e Φ :
    ▷ Φ #() ∗ ▷ WP e @[ip] ⊤ {{ _, True }} ⊢ WP Fork e @[ip] E {{ Φ }}.
  Proof.
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "[HΦ Hwp] %tid Hin".
    iApply wp_fork.
    iSplitL "HΦ"; first by eauto.
    iIntros (?). iNext.
    iApply wp_wand_r; iSplitL; first by iApply "Hwp".
    auto.
  Qed.

  (** Heap *)
  Lemma aneris_wp_alloc ip E v :
    {{{ True }}} ref (Val v) @[ip] E {{{ l, RET #l; l ↦[ip] v }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply wp_alloc; first done.
    iNext.
    iIntros (l) "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_alloc_tracked ip E v lbl evs :
    {{{ ▷ alloc_evs lbl evs }}}
      ref<<lbl>> (Val v) @[ip] E
    {{{ l h (σ : state), RET #l; l ↦[ip] v ∗
          ⌜valid_allocObs ip l σ h⌝ ∗ alloc_evs lbl (evs ++ [allocObs ip lbl l v σ h]) }}}.
  Proof.
    iIntros (Φ) "Hevs HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply (wp_alloc_tracked with "[$]").
    iNext.
    iIntros (l h σ) "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_load ip E l q v :
    {{{ ▷ l ↦[ip]{q} v }}} Load #l @[ip] E {{{ RET v; l ↦[ip]{q} v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply (wp_load with "Hl").
    iNext.
    iIntros "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_store ip E l v' v :
  {{{ ▷ l ↦[ip] v' }}} Store #l (Val v) @[ip] E {{{ RET #(); l ↦[ip] v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply (wp_store with "Hl").
    iNext.
    iIntros "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_cas_fail ip E l q v' v1 v2 :
    v' ≠ v1 →
    {{{ ▷ l ↦[ip]{q} v' }}}
      CAS #l (Val v1) (Val v2) @[ip] E
    {{{ RET #false; l ↦[ip]{q} v' }}}.
  Proof.
    iIntros (Hneq Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply (wp_cas_fail with "Hl"); first done.
    iNext.
    iIntros "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_cas_suc ip E l v1 v2 :
    {{{ ▷ l ↦[ip] v1 }}}
      CAS #l (Val v1) (Val v2) @[ip] E
    {{{ RET #true; l ↦[ip] v2 }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply (wp_cas_suc with "Hl").
    iNext.
    iIntros "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

End lifting_node_local.

Section lifting_network.
  Context `{anerisG Mdl Σ}.

  Implicit Types ip : ip_address.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types e : expr.

  (** Network *)
  Lemma aneris_wp_start ports ip E e Ψ :
    ip ≠ "system" →
    ▷ free_ip ip ∗ ▷ Ψ #() ∗
    ▷ (free_ports ip ports -∗ WP e @[ip] ⊤ {{ _, True }}) ⊢
    WP (Start (LitString ip) e) @["system"] E {{ Ψ }}.
  Proof.
    iIntros (Hip) "(Hip & HΦ & He)".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply wp_start; [done|].
    iFrame.
    iSplitL "HΦ".
    { iNext. iExists _. eauto. }
    iNext.
    iIntros "%tid' Hin' Hfp".
    iApply wp_wand_r; iSplitL; first iApply ("He" with "Hfp Hin'").
    done.
  Qed.

  Lemma aneris_wp_new_socket ip E v1 v2 v3 :
    {{{ True }}}
      NewSocket
      (Val $ LitV $ LitAddressFamily v1)
      (Val $ LitV $ LitSocketType v2)
      (Val $ LitV $ LitProtocol v3) @[ip] E
    {{{ h, RET (LitV (LitSocket h));
          h ↪[ip] (mkSocket v1 v2 v3 None true) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply wp_new_socket; first done.
    iNext.
    iIntros (h) "?".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_socketbind_static ip A E h s a :
    ip_of_address a = ip →
    saddress s = None →
    a ∈ A →
    {{{ ▷ fixed A ∗
        ▷ free_ports (ip_of_address a) {[port_of_address a]} ∗
        ▷ h ↪[ip_of_address a] s }}}
      SocketBind
      (Val $ LitV $ LitSocket h)
      (Val $ LitV $ LitSocketAddress a) @[ip] E
    {{{ RET #0;
        h ↪[ip_of_address a] (s<| saddress := Some a |>) ∗
        ∃ φ, a ⤇ φ }}}.
  Proof.
    iIntros (Hip Hskt Ha Φ) "(>HA & Hfp & Hsh) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_socketbind_static with "[$HA $Hfp $Hsh]"); [done|done|].
    iNext.
    iIntros "(Hsh & Hproto)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_socketbind_dynamic ip s A E h a φ :
    ip_of_address a = ip →
    saddress s = None →
    a ∉ A →
    {{{ ▷ fixed A ∗
        ▷ free_ports (ip_of_address a) {[port_of_address a]} ∗
        ▷ h ↪[ip_of_address a] s
    }}}
      SocketBind
      (Val $ LitV $ LitSocket h)
      (Val $ LitV $ LitSocketAddress a) @[ip] E
    {{{ RET #0;
        h ↪[ip_of_address a] (s <| saddress := Some a |>) ∗
        a ⤇ φ }}}.
  Proof.
    iIntros (Hip Hskt Ha Φ) "(HA & Hfp & Hsh) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_socketbind_dynamic with "[$HA $Hfp $Hsh]"); [done|done|].
    iNext.
    iIntros "(Hsh & Hproto)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send ip φ m h a f rtrck E s R T :
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := {|
          m_sender := f;
          m_destination := a;
          m_protocol := sprotocol s;
          m_body := m;
        |} in
    {{{ ▷ h ↪[ip] s ∗ ▷ f ⤳[false, rtrck] (R, T) ∗ ▷ a ⤇ φ ∗ ▷ φ msg }}}
      SendTo (Val $ LitV $ LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m);
        h ↪[ip] s ∗ f ⤳[false, rtrck] (R, {[ msg ]} ∪ T) }}}.
  Proof.
    iIntros (Hip Hskt msg Φ) "(Hsh & Hm & Hproto & Hmsg) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send with "[$]"); first done.
    iNext.
    iIntros "(Hsh & Hm)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send_duplicate ip m h a f rtrck E s R T:
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := mkMessage f a (sprotocol s) m in
    msg ∈ T →
    {{{ ▷ h ↪[ip] s ∗ ▷ f ⤳[false, rtrck] (R, T) }}}
      SendTo (Val $ LitV $ LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m); h ↪[ip] s ∗ f ⤳[false, rtrck] (R, T) }}}.
  Proof.
    iIntros (Hip Hskt msg Hmsg Φ) "(Hsh & Hm) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send_duplicate with "[$Hsh $Hm]"); [done|done|].
    iNext.
    iIntros "(Hsh & Hm)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_tracked ip φ m h a f rtrck s E R T evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := {|
          m_sender := f;
          m_destination := a;
          m_protocol := sprotocol s;
          m_body := m;
        |} in
    {{{ ▷ h ↪[ip_of_address f] s ∗
        ▷ f ⤳[true, rtrck] (R, T) ∗
        ▷ a ⤇ φ ∗
        ▷ φ msg ∗
        ▷ sendon_evs f evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      SendTo (Val $ LitV $ LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m);
        h ↪[ip_of_address f] s ∗
        f ⤳[true, rtrck] (R, {[ msg ]} ∪ T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs f st h skts s r⌝ ∗
          sendon_evs f (evs ++ [sendonObs f st h (m_body msg) a s]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs f st h (m_body msg) a s).(post_state) }}}.
  Proof.
    iIntros (Hip Hskt msg Φ) "(Hsh & Hm & Hproto & Hmsg & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send_tracked with "[$]"); first done.
    iNext.
    iIntros "(Hsh & Hm & Hevs)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_duplicate_tracked ip m h a f E rtrck s R T evs (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := mkMessage f a (sprotocol s) m in
    msg ∈ T →
    {{{ ▷ h ↪[ip] s ∗
        ▷ f ⤳[true, rtrck] (R, T) ∗
        ▷ sendon_evs f evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      SendTo (Val $ LitV $ LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m); h ↪[ip] s ∗ f ⤳[true, rtrck] (R, T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs f st h skts s r⌝ ∗
          sendon_evs f (evs ++ [sendonObs f st h (m_body msg) a s]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs f st h (m_body msg) a s).(post_state) }}}.
  Proof.
    iIntros (Hip Hskt msg Hmsg Φ) "(Hsh & Hm & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send_duplicate_tracked with "[$]"); [done|done|].
    iNext.
    iIntros "(Hsh & Hm & Hevs)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_nb_gen
        (Ψo : option (socket_interp Σ)) ip a E h s R T :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ h ↪[ip_of_address a] s ∗
        ▷ a ⤳ (R, T) ∗
        match Ψo with Some Ψ => a ⤇ Ψ | _ => True end }}}
      (ReceiveFrom (Val $ LitV $ LitSocket h)) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳ (R, T) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗
             match Ψo with Some Ψ => Ψ msg | _ => ∃ φ, a ⤇ φ ∗ φ msg end) ∨
            ⌜msg ∈ R⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳ (R, T))))) }}}.
  Proof.
    iIntros (Hip Hskt Hblock Φ) "Hshprot HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_receivefrom_nb_gen with "[$Hshprot]"); [done|done|].
    iNext.
    iIntros (r) "Hr".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
   Qed.

  Lemma aneris_wp_receivefrom_nb ip a E h s R T :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T))) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗
             ∃ φ, a ⤇ φ ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T))) }}}.
  Proof.
    iIntros (Hip Hs Hb Φ) "(Hsh & Hm) HΦ".
    rewrite -Hip.
    iApply (aneris_wp_receivefrom_nb_gen None with "[$]");  eauto.
  Qed.

  Lemma aneris_wp_receivefrom_alt ip a E sh s R T φ :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ sh ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ }}}
      ReceiveFrom (Val $ LitV $ LitSocket sh) @[ip] E
    {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ sh ↪[ip] s ∗ a ⤳ (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
            ⌜msg ∈ R⌝ ∗ sh ↪[ip] s ∗ a ⤳ (R, T)) }}}.
   Proof.
     iIntros (Hip Hs Hb Φ) "Hsh HΦ". rewrite -Hip.
     iApply (aneris_wp_receivefrom_nb_gen (Some φ) with "[$]"); eauto.
   Qed.

   Lemma aneris_wp_receivefrom ip a E h s R T φ :
     ip_of_address a = ip →
     saddress s = Some a →
     sblock s = true →
     {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ}}}
       ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
     {{{ m, RET SOMEV (PairV #(m_body m) #(m_sender m));
         ⌜m_destination m = a⌝ ∗
         ((⌜m ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ φ m) ∨
          ⌜m ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)) }}}.
   Proof.
     iIntros (<- Haddr Hblk Φ) "(>Hsh & >Ha & #Hsi) HΦ".
     rewrite !aneris_wp_unfold /aneris_wp_def.
     iIntros "%tid #Hin". iApply (wp_receivefrom with "[$Hsh $Ha]"); eauto.
     iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
     iApply "HΦ"; iFrame.
   Qed.

   Lemma aneris_wp_receivefrom_gen ip a E h s R T φ :
     ip = ip_of_address a →
     saddress s = Some a →
     {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ}}}
       ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
     {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)) }}}.
   Proof.
     iIntros (-> Haddr Φ) "(>Hsh & >Ha & #Hsi) HΦ".
     rewrite !aneris_wp_unfold /aneris_wp_def.
     iIntros "%tid #Hin". iApply (wp_receivefrom_gen with "[$Hsh $Ha]"); eauto.
     iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
     iApply "HΦ"; iFrame.
   Qed.

   Lemma aneris_wp_receivefrom_nb_gen_tracked
         (Ψo : option (socket_interp Σ)) ip a strck E h s R T evs
         (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ h ↪[ip_of_address a] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        match Ψo with Some Ψ => a ⤇ Ψ | _ => True end ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      (ReceiveFrom (Val $ LitV $ LitSocket h)) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳[strck, true] (R, T) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗
             match Ψo with Some Ψ => Ψ msg | _ => ∃ φ, a ⤇ φ ∗ φ msg end) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳[strck, true] (R, T)) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs a st h msg skts s r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st h msg skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st h msg skts s r).(post_state)))) }}}.
  Proof.
    iIntros (Hip Hskt Hblock Φ) "(Hsh & Ha & HΨ & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_receivefrom_nb_gen_tracked Ψo with "[$]"); [done|done|].
    iNext.
    iIntros (r) "Hr".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
   Qed.

  Lemma aneris_wp_receivefrom_nb_tracked ip a strck E h s R T evs
         (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ h ↪[ip] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ)
    }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] (R, T))) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗
             ∃ φ, a ⤇ φ ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
           ∃ st skts r,
            ⌜valid_receiveonObs a st h msg skts s r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st h msg skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st h msg skts s r).(post_state)) }}}.
  Proof.
    iIntros (Hip Hs Hb Φ) "(Hsh & Hm & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite -Hip.
    iApply (aneris_wp_receivefrom_nb_gen_tracked None with "[$]"); eauto.
  Qed.

  Lemma aneris_wp_receivefrom_alt_tracked ip a strck E sh s R T φ evs
         (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ sh ↪[ip] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ φ ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      ReceiveFrom (Val $ LitV $ LitSocket sh) @[ip] E
    {{{ r, RET r;
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
     iIntros (Hip Hs Hb Φ) "Hsh HΦ". rewrite -Hip.
     iApply (aneris_wp_receivefrom_nb_gen_tracked (Some φ) with "[$]"); eauto.
   Qed.

   Lemma aneris_wp_receivefrom_tracked ip a strck E h s R T φ evs
         (Ψ1 Ψ2 : state → iProp Σ) :
     ip_of_address a = ip →
     saddress s = Some a →
     sblock s = true →
     {{{ ▷ h ↪[ip] s ∗
         ▷ a ⤳[strck, true] (R, T) ∗
         a ⤇ φ ∗
         ▷ receiveon_evs a evs ∗
         (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
         ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ) }}}
       ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
     {{{ m, RET SOMEV (PairV #(m_body m) #(m_sender m));
         ⌜m_destination m = a⌝ ∗
         ((⌜m ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] ({[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ φ m) ∨
          ⌜m ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
         ∃ st skts r,
            ⌜valid_receiveonObs a st h m skts s r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st h m skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st h m skts s r).(post_state) }}}.
   Proof.
     iIntros (<- Haddr Hblk Φ) "(>Hsh & >Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
     rewrite !aneris_wp_unfold /aneris_wp_def.
     iIntros "%tid #Hin". iApply (wp_receivefrom_tracked with "[$]"); eauto.
     iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
     iApply "HΦ"; iFrame.
   Qed.

   Lemma aneris_wp_receivefrom_gen_tracked ip a strck E h s R T φ evs
         (Ψ1 Ψ2 : state → iProp Σ) :
     ip = ip_of_address a →
     saddress s = Some a →
     {{{ ▷ h ↪[ip] s ∗
         ▷ a ⤳[strck, true] (R, T) ∗
         a ⤇ φ ∗
         ▷ receiveon_evs a evs ∗
         (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ1 σ) ∗
         ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗ aneris_state_interp σ δ ∗ Ψ2 σ) }}}
       ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
     {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs a st h msg skts s r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st h msg skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st h msg skts s r).(post_state) }}}.
   Proof.
     iIntros (-> Haddr Φ) "(>Hsh & >Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
     rewrite !aneris_wp_unfold /aneris_wp_def.
     iIntros "%tid #Hin". iApply (wp_receivefrom_gen_tracked with "[$]"); eauto.
     iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
     iApply "HΦ"; iFrame.
   Qed.

   Lemma aneris_wp_rcvtimeo_unblock ip a E h s n1 n2 :
     ip_of_address a = ip →
     saddress s = Some a →
     (0 <= n1 ∧ 0 <= n2 ∧ 0 < n1 + n2)%Z →
     {{{ ▷ h ↪[ip] s }}}
       SetReceiveTimeout
       (Val $ LitV $ LitSocket h)
       (Val $ LitV $ LitInt n1)
       (Val $ LitV $ LitInt n2) @[ip] E
     {{{ RET #(); h ↪[ip] s<|sblock := false|> }}}.
   Proof.
     iIntros (Hip Hskt Hcnd Φ) "Hsh HΦ".
     rewrite !aneris_wp_unfold /aneris_wp_def.
     iIntros "%tid #Hin".
     rewrite -Hip.
     iApply (wp_rcvtimeo_unblock _ a E _ h s n1 n2 with "[$Hsh]"); [done|done|].
     iNext. iIntros "Hsh". iExists _; iSplit; first done. iApply "HΦ"; iFrame.
   Qed.

  Lemma aneris_wp_rcvtimeo_block ip a E h s :
    ip_of_address a = ip →
    saddress s = Some a →
    {{{ ▷ h ↪[ip] s }}}
      SetReceiveTimeout
      (Val $ LitV $ LitSocket h)
      (Val $ LitV $ LitInt 0)
      (Val $ LitV $ LitInt 0) @[ip] E
    {{{ RET #(); h ↪[ip] s<|sblock := true|> }}}.
  Proof.
    iIntros (Hip Hskt Φ) "Hsh HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_rcvtimeo_block _ a E _ h s with "[$Hsh]"); [done|].
    iNext. iIntros "Hsh". iExists _; iSplit; first done. iApply "HΦ"; iFrame.
  Qed.

End lifting_network.
