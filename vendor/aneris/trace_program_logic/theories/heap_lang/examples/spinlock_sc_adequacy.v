From trace_program_logic.heap_lang.examples Require Import spinlock_sc.
From iris.proofmode Require Import tactics.
From trace_program_logic.program_logic Require Export weakestpre.
From trace_program_logic.prelude Require Export finitary quantifiers sigma classical_instances.
From trace_program_logic.heap_lang Require Export lang lifting tactics.
From trace_program_logic.heap_lang Require Import notation.
From trace_program_logic.fairness Require Import fairness fair_termination fairness_finiteness.
From trace_program_logic.heap_lang.examples Require Import fair_termination_natural.
From stdpp Require Import finite.


Definition sm_order (s1 s2: spinlock_model): Prop :=
  Forall2 le s1 s2.
                                                     
Instance sm_order_po: PartialOrder sm_order. 
Proof.
  constructor.
  - apply PreOrder_instance_1. econstructor; red; lia.
  - apply AntiSymm_instance_1. red. lia. 
Qed.


Definition rem_actions (st: spinlock_model): nat := list_sum st. 

Lemma not_Forall2 {A B: Type} (f: A -> B -> Prop) (la: list A) (lb: list B)
      (LEN: length la = length lb)
      (NF2: ¬ Forall2 f la lb)
      (DEC: RelDecision f):
  exists i a b, la !! i = Some a /\ lb !! i = Some b /\ not (f a b).
Proof.
  generalize dependent lb. induction la.
  { intros. simpl in LEN. symmetry in LEN. apply nil_length_inv in LEN. subst.
    by destruct NF2. }
  intros. destruct lb.
  { by simpl in LEN. }
  simpl in LEN. apply eq_add_S in LEN.
  destruct (DEC a b).
  2: { exists 0, a, b. auto. }
  edestruct @Forall2_dec with (x := la) (y := lb); eauto.
  { destruct NF2. eauto. }
  specialize (IHla _ LEN n). destruct IHla as (i & a' & b' & ? & ? & ?).
  exists (S i), a', b'. simpl. eauto.
Qed. 
  
Lemma sm_order_sum_le (st1 st2: spinlock_model) (LE: sm_order st1 st2):
  list_sum st1 <= list_sum st2.
Proof.
  generalize dependent st2. induction st1.
  { intros. red in LE. apply Forall2_nil_inv_l in LE. subst. lia. }
  intros. destruct st2.
  { red in LE. by apply Forall2_nil_inv_r in LE. }
  inversion LE. subst.
  simpl. specialize (IHst1 _ H4). lia.
Qed.

Lemma sm_order_insert st i v v' (ITH: st !! i = Some v) (LE: v' <= v):
  sm_order (<[i:=v']> st) st.
Proof.
  red. apply Forall2_same_length_lookup_2; [by apply insert_length| ].
  intros j x y JTH' ITH_. destruct (dec_eq_nat j i).
  + subst j. rewrite ITH_ in ITH. inversion ITH. subst v. 
    rewrite list_lookup_insert in JTH'.
    2: { by eapply lookup_lt_Some. }
    inversion JTH'. lia.
  + rewrite list_lookup_insert_ne in JTH'; auto.
    rewrite ITH_ in JTH'. inversion JTH'. lia.
Qed. 

Lemma strict_sm_order_insert st i v v' (ITH: st !! i = Some v) (LT: v' < v):
  strict sm_order (<[i:=v']> st) st.
Proof.
  red. split; [eapply sm_order_insert; eauto; lia| ].
  intros ORD. red in ORD.
  eapply Forall2_lookup_lr with (y := v') in ORD; eauto; [lia| ].
  apply list_lookup_insert. by eapply lookup_lt_Some. 
Qed. 

Lemma unlocked_dec (st: spinlock_model): Decision (state_unlocked st).
Proof.
  red. induction st.
  { by left. }
  destruct IHst.
  2: { right. unfold state_unlocked in *. intros UNL. destruct n.
       intros. by apply UNL with (j := S j). }
  destruct (nat_eq_dec a 1) as [-> | A].
  { right. intros UNL. red in UNL. specialize (UNL 0 1 eq_refl). lia. }
  left. red. intros. destruct j.
  { simpl in JV. inversion JV. lia. }
  simpl in JV. by eapply s.
Qed. 

Lemma locked_dec (st: spinlock_model): {i | state_locked_by st i} +
                                       {not (exists i, state_locked_by st i)}. 
Proof.
  destruct (list_find (eq 1) st) eqn:IN1.
  2: { right. intros [i [ITH NOJ]]. 
       apply list_find_None in IN1.
       eapply Forall_lookup_1 in ITH; eauto. done. }
  destruct p as [i v].
  (* pose proof IN1 as IN_. *)
  apply list_find_Some in IN1. destruct IN1 as (ITH & <- & PREV).  
  destruct (list_find (eq 1) (drop (S i) st)) eqn:IN2. 
  2: { apply list_find_None in IN2. 
       left. exists i. red. split; auto.
       intros. destruct (Nat.lt_trichotomy i j) as [LT | [? | LT]]; [| done| ].
       2: { specialize (PREV _ _ JV). lia. }
       eapply Forall_lookup_1 with (i0 := j - (S i)) in IN2.
       2: { rewrite lookup_drop. rewrite le_plus_minus_r; eauto. }
       lia. }
  destruct p as [j v].
  apply list_find_Some in IN2. destruct IN2 as (JTH & <- & PREV').
  right. intros [k [KTH NOOTHER]].
  destruct (Nat.lt_trichotomy k i) as [LT | [? | LT]].
  { eapply PREV in LT; eauto. }
  { subst k. edestruct (NOOTHER (S i + j)); try lia. 
    { by rewrite lookup_drop in JTH. }
    all: lia. }  
  destruct (Nat.lt_trichotomy k (S i + j)) as [LT' | [-> | LT']].
  { apply Nat.le_exists_sub in LT as [d [-> _]]. 
    edestruct (PREV' d); eauto; [| lia].
    rewrite lookup_drop. by rewrite Nat.add_comm. }
  { edestruct (NOOTHER i); eauto; lia. }
  edestruct (NOOTHER (S i + j)); eauto. 
  { by rewrite lookup_drop in JTH. }
  all: lia. 
Qed. 
  
Lemma unlocked_next st (UNL: state_unlocked st):
  {i | exists v, st !! i = Some v /\ v >= 2 /\
            forall j v' (PREV: j < i) (JTH: st !! j = Some v'), v' < 2} +
  {Forall (eq 0) st}.
Proof.
  edestruct (list_find (fun x => 2 <= x) st) eqn:IN.
  { left. destruct p as [i v]. exists i.
    apply list_find_Some in IN as (? & ? & ?). eexists. repeat split; eauto.
    intros. specialize (H1 _ _ JTH). lia. }
  right. 
  apply Forall_lookup_2. intros. 
  red in UNL. specialize (UNL _ _ H). destruct UNL; auto.
  apply list_find_None in IN. eapply Forall_lookup_1 in H; [| apply IN].
  by simpl in H. 
Qed. 

Lemma get_model_status (st: spinlock_model):
  state_unlocked st * 
  ({i | exists v, st !! i = Some v /\ v >= 2 /\
              forall j v' (PREV: j < i) (JTH: st !! j = Some v'), v' < 2} + 
    {Forall (eq 0) st}) + 
  {i: nat | state_locked_by st i} +
  {~ state_unlocked st /\ ~ (exists i, state_locked_by st i)}.
  (* } + *)
  (* {True}. *)
Proof.  
  destruct (unlocked_dec st). 
  - repeat left. split; auto.
    destruct (unlocked_next st s) as [[]| ?]; [left | right]; eauto.
  - destruct (locked_dec st) as [[]| ?]; eauto.
Qed.


Lemma unlocked_locked_incompat (s: spinlock_model)
      (UNLOCKED : state_unlocked s) (LOCKED: ∃ j, state_locked_by s j):
  False.
Proof.
  destruct LOCKED as [i [LOCKi]]. specialize (UNLOCKED _ _ LOCKi). lia.
Qed.

Lemma live_roles_alt (s: spinlock_model) i v
        (ITH: s !! i = Some v)
        (V: v ≥ 1):
  i ∈ live_roles spinlock_model s.
Proof.
  simpl. unfold spinlock_lr. apply elem_of_list_to_set, elem_of_list_In.  
  apply filter_In. split. 
  * apply in_seq. apply lookup_lt_Some in ITH. lia.
  * rewrite ITH. simpl. apply Nat.ltb_lt. lia.
Qed. 

Lemma state_locked_by_det (st: spinlock_model) (i j: nat)
      (LOCKi: state_locked_by st i) (LOCKj: state_locked_by st j):
  i = j.
Proof.
  destruct LOCKi as [I1 NOJ]. destruct LOCKj as [J1 NOI].
  destruct (dec_eq_nat i j) as [? | NEQ]; auto.
  specialize (NOJ _ _ J1). lia.
Qed.

Lemma state_locked_by_simpl (st: spinlock_model) (i j: nat)
      (DOMi: i < length st)
      (LOCK: state_locked_by (<[i:=1]> st) j):
  i = j.
Proof.
  destruct LOCK as [I1 NOJ].
  destruct (dec_eq_nat i j) as [? | NEQ]; auto.
  edestruct (NOJ i); eauto.
  { by eapply list_lookup_insert. }
  all: lia.
Qed. 

Lemma sm_step_le (s s': spinlock_state) (oρ: option nat)
      (STEP: spinlock_model_step s oρ s'):
  sm_order s' s.
Proof. 
  inversion STEP; subst.
  - eapply sm_order_insert; eauto. lia.
  - destruct LOCKi. eapply sm_order_insert; eauto.
  - red. apply Reflexive_instance_0. red. lia.
Qed. 

  
Program Instance spinlock_model_terminates: FairTerminatingModelSimple spinlock_model :=
  {|
  ftms_leq := sm_order;
  |}.
Next Obligation.
  eapply wf_projected with (f := rem_actions).
  2: { apply lt_wf. }
  unfold sm_order, rem_actions. intros x y [LE NGE].
  edestruct @not_Forall2 as (i & a & b & [? [?]]); [| eauto |..].
  { symmetry. by eapply Forall2_length. }
  { apply nat_le_dec. }
  rewrite <- (take_drop_middle x i b), <- (take_drop_middle y i a); auto.
  repeat (rewrite list_sum_app; simpl).
  apply PeanoNat.Nat.add_le_lt_mono.
  { apply sm_order_sum_le. by apply Forall2_take. }
  apply PeanoNat.Nat.add_lt_le_mono; [lia| ].
  apply sm_order_sum_le. by apply Forall2_drop. 
Qed.
Next Obligation.
  intros. red.
  destruct (get_model_status s) as [[[UNL [[i READY] | ALL0]] | [i LOCK]] | [NO1 NO2]].
  - left. destruct READY, H. red. exists (Some i).
    eexists. econstructor; eauto. lia.
  - right. intros ACT. red in ACT. destruct ACT, H. inversion H; subst.
    1,3: eapply Forall_lookup_1 in READYi; eauto; lia.
    destruct LOCKi. eapply Forall_lookup_1 in H0; eauto. lia.
  - left. destruct LOCK. exists (Some i).
    eexists. eapply sm_unlock. red. eauto.
  - right. intros ACT. red in ACT. destruct ACT, H.
    inversion H; subst; try tauto. 
    edestruct NO2; eauto. 
Qed.
Next Obligation.
  (* TODO: refactor *)
  intros. red in ACTIVE. destruct ACTIVE, H.
  destruct x as [ρ | ].
  2: { inversion H. }
  inversion H; subst. 
  1, 2: (exists ρ; split; [by eapply fm_live_spec; eauto| subst; intros]).
  - inversion STEPρ; subst.
    2, 3: edestruct unlocked_locked_incompat; eauto.
    eapply strict_sm_order_insert; eauto.
  - inversion STEPρ; subst.
    { edestruct unlocked_locked_incompat; eauto. }
    { red in LOCKi. destruct LOCKi. eapply strict_sm_order_insert; eauto. }
    destruct LOCKED. 
    pose proof (state_locked_by_det _ _ _ LOCKi H0) as <-; eauto.
    destruct H0. rewrite H0 in READYi. inversion READYi. lia.
  - destruct LOCKED as [j LOCKED]. exists j. split.
    { eapply fm_live_spec. eapply sm_unlock; eauto. }
    intros. 
    inversion STEPρ; subst.
    { edestruct unlocked_locked_incompat; eauto. }
    { red in LOCKi. destruct LOCKi. eapply strict_sm_order_insert; eauto. }
    destruct LOCKED0. 
    pose proof (state_locked_by_det _ _ _ H0 LOCKED) as <-; eauto.
    destruct H0. rewrite H0 in READYi0. inversion READYi0. lia.
Qed.
Next Obligation.
  intros. by eapply sm_step_le. 
Qed.

Instance proof_irrel_trans s x:
  ProofIrrel ((let '(s', ℓ) := x in spinlock_model_step s ℓ s'): Prop).
Proof. apply make_proof_irrel. Qed.

Lemma le_states_list (s: spinlock_model):
  {l: list spinlock_state | forall s' (LE: sm_order s' s), In s' l }. 
Proof.
  induction s as [| a s [l IHl]].
  { exists [[]]. intros. inversion LE. subst. simpl. tauto. }
  exists (flat_map (fun (i: nat) => map (fun s_ => i :: s_) l) (seq 0 (S a))).
  intros. inversion LE. subst. 
  apply in_flat_map.
  exists x. split.
  { apply in_seq. lia. }
  apply in_map_iff. eexists. split; eauto.
Qed.

Lemma sm_step_role_bound (s s': spinlock_state) (oρ: option nat)
      (STEP: spinlock_model_step s oρ s'):
  exists ρ, oρ = Some ρ /\ ρ < length s.
Proof.
  inversion STEP; eexists; split; eauto; apply lookup_lt_is_Some; subst; eauto.
  destruct LOCKi. eauto.
Qed. 
  
  
Lemma model_finitary (s: spinlock_model):
  Finite { '(s', ℓ) | spinlock_model_step s ℓ s'}.
Proof.
  destruct (le_states_list s) as [ls INls].
  set (l := flat_map (fun (i: nat) => map (fun s_ => (s_, Some i)) ls)
                     (seq 0 (length s))).
  eapply in_list_finite with (l0 := l). intros. destruct x. 
  apply elem_of_list_In. subst l. apply in_flat_map.
  pose proof (sm_step_role_bound s s0 o H) as [ρ [-> LT]].
  exists ρ. split.
  { apply in_seq. lia. }
  apply in_map_iff. eexists. split; eauto.
  apply INls. by eapply sm_step_le.
Qed.

(* TODO: adapted from lifting.v, unify? *)
Theorem simple_simulation_adequacy_terminate_ftm Σ `{FairTerminatingModelSimple Mdl} `{!heapGpreS Σ Mdl} (s: stuckness)
        e1 (s1: Mdl)
        (extr : extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  valid_state_evolution_finitary (aux_fair_state Mdl) (λ ex aux, live_tids (trace_last ex) (trace_last aux))→
  live_roles Mdl s1 ≠ ∅ ->
  (∀ `{!heapGS Σ Mdl},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         has_fuels (Σ := Σ) 0%nat (Mdl.(live_roles) s1) (gset_to_gmap (fuel_limit s1) (Mdl.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  eapply simulation_adequacy_terminate =>//.
  apply simple_fair_terminating_traces_terminate.
Qed.


(* TODO: how to correctly pass P premise to proof? 
   So far we only substitute True for P.
   It's better to parametrize the theorem with "P is available" premise *)
  
Theorem spinlock_terminates
        (* (N : nat) *)
        (* (HN: N > 0) *)
        (extr : extrace)
        (Hvex : extrace_valid extr)
  (*       (P: iProp spinlockΣ) *)
  (*       (getP: heap_lang.expr) *)
  (*       (ALLOC_P: *)
  (* ∀ (tid : locale heap_lang) (Φ : heap_lang.val → iPropI spinlockΣ) `{Wp heap_lang (iPropI spinlockΣ) stuckness}, *)
  (*   (⌜True⌝ -∗ ▷ (P -∗ Φ #()) -∗ WP getP @tid {{ v, Φ v }})) *)
        (Hexfirst : (trfirst extr).1 = [program]):
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  assert (heapGpreS spinlockΣ spinlock_model) as HPreG.
  { apply _. }
  eapply (simple_simulation_adequacy_terminate_ftm (Mdl := spinlock_model)
                                            spinlockΣ NotStuck _ [2; 2])
  =>//.
  - eapply valid_state_evolution_finitary_fairness.
    intros ?. simpl. apply (model_finitary s1).
  - intros ?. iStartProof. iIntros "!> Hm Hf !>". simpl.
    iApply (program_spec _ True _ with "[Hm Hf]"); eauto.
    iFrame. iSplitL ""; [done| ].    
    rewrite /spinlock_lr. simpl.
    iApply has_fuels_equiv_args; last by iFrame.
    { set_solver. }
    simpl. rewrite !gset_to_gmap_union_singleton gset_to_gmap_empty.
    done. 
Qed.
