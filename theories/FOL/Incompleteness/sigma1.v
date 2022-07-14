From Undecidability.FOL.Incompleteness Require Import utils fol qdec.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax Friedman.
From Undecidability.FOL Require Import PA.

From Equations Require Import Equations.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.


Require Import Setoid.

Require Import Undecidability.Shared.Libs.DLW.Vec.vec.

Require Import String.
Open Scope string_scope.

(** ** Sigma1 completeness *)

Section Sigma1.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {p : peirce}.



  (** # <a id="Sigma1" /> #*)
  Inductive Σ1 : form -> Prop :=
  | Sigma_exists : forall α, Σ1 α -> Σ1 (∃ α)
  | Sigma_Delta : forall α, Qdec α -> Σ1 α.
  Inductive Π1 : form -> Prop :=
  | Pi_forall : forall α, Π1 α -> Π1 (∀ α)
  | Pi_Delta : forall α, Qdec α -> Π1 α.

  Lemma Σ1_subst φ ρ : Σ1 φ -> Σ1 φ[ρ].
  Proof.
    induction 1 as [α H IH | α H] in ρ |-*.
    - cbn. constructor. apply IH.
    - constructor. apply Qdec_subst, H.
  Qed.

  Lemma Π1_subst φ ρ : Π1 φ -> Π1 φ[ρ].
  Proof.
    induction 1 as [α H IH | α H] in ρ |-*.
    - cbn. constructor. apply IH.
    - constructor. apply Qdec_subst, H.
  Qed.

  Lemma exist_times_Σ1 n φ :
    Σ1 φ -> Σ1 (exist_times n φ).
  Proof.
    intros H. induction n.
    - easy.
    - now constructor.
  Qed.


  Lemma exists_compression_2 φ n : Qdec φ -> bounded (S (S n)) φ -> exists ψ, Qdec ψ /\ bounded (S n) ψ /\ Qeq ⊢I (∃∃φ) <~> (∃ψ).
  Proof.
    intros HQ Hb.
    exists (∃ ($0 ⧀= $1) ∧ ∃ ($0 ⧀=comm $2) ∧ φ[up (up (S >> var))]).
    repeat split.
    { apply (@Qdec_bounded_exists $0), (@Qdec_bounded_exists_comm $1).
      apply Qdec_subst, HQ. }
    { constructor. constructor.
      { rewrite pless_eq. 
        eapply (@bounded_up _ _ _ _ 2); last lia.
        repeat solve_bounds. }
      constructor. constructor.
      { eapply (@bounded_up _ _ _ _ 3); last lia.
        rewrite pless_swap_eq.
        constructor. repeat solve_bounds. }
      eapply subst_bound; last eassumption.
      intros n' H'.
      destruct n' as [|[|n']]; cbn; unfold "↑"; cbn; constructor; lia. }
    apply CI.
    - apply II.
      eapply ExE.
      { apply Ctx; now left. }
      cbn -[Qeq]. unfold "↑". fold ↑.
      change (List.map (subst_form ↑) Qeq) with Qeq.
      eapply ExE.
      { apply Ctx; now left. }
      cbn -[Qeq]. unfold "↑". fold ↑.
      change (List.map (subst_form ↑) Qeq) with Qeq.
      apply Weak with (A := (φ :: Qeq)%list).
      2: { intros ϕ [<-|H].
           - now left.
           - now do 3 right. }
      apply ExI with (t := $1 ⊕ $0).
      cbn -[Qeq]. unfold "↑". fold ↑.
      apply ExI with (t := $1).
      cbn -[Qeq]. unfold "↑". fold ↑.
      apply CI.
      { apply ExI with (t := $0). cbn -[Qeq].
        eapply AllE with (t := $1 ⊕ $0) (phi := $0 == $0).
        apply Ctx. right. now left. }
      apply ExI with (t := $0).
      cbn -[Qeq]. unfold "↑". fold ↑.
      apply CI.
      { apply ExI with (t := $1). cbn -[Qeq].
        eapply AllE with (t := $1 ⊕ $0) (phi := $0 == $0).
        apply Ctx. right. now left. }
      rewrite !subst_comp. erewrite subst_ext; first instantiate (1 := var).
      + rewrite subst_var. now apply Ctx.
      + now intros [|[|[|k]]]; cbn.
    - apply II.
      eapply ExE.
      { apply Ctx; now left. }
      cbn -[Qeq]. unfold "↑". fold ↑.
      change (List.map (subst_form ↑) Qeq) with Qeq.
      eapply ExE.
      { apply Ctx; now left. }
      cbn -[Qeq]. unfold "↑". fold ↑.
      change (List.map (subst_form ↑) Qeq) with Qeq.
      eapply ExE.
      { eapply CE2, Ctx. now left. }
      cbn -[Qeq]. unfold "↑". fold ↑.
      change (List.map (subst_form ↑) Qeq) with Qeq.
      eapply ExI with (t := $1). cbn -[Qeq].
      eapply ExI with (t := $0). cbn -[Qeq].
      eapply IE.
      2: { eapply CE2, Ctx. now left. }
      eapply Weak with (A := Qeq).
      2: { intros f H. now do 4 right. }
      apply II. rewrite !subst_comp.
      apply Ctx. left.
      apply subst_ext. now intros [|[|[|k]]].
  Qed.

  Lemma exists_equiv φ ψ : Qeq ⊢I φ ~> ψ -> (∃φ :: Qeq) ⊢I (∃ψ).
  Proof.
    intros H. eapply ExE.
    { apply Ctx. now left. }
    cbn -[Qeq]. fexists $0. (* Including proofmode broke ExI *)
    replace (ψ[_][_]) with (ψ[var]); first last.
    { rewrite subst_comp. apply subst_ext. now intros [|k]. }
    rewrite subst_var. eapply IE.
    { eapply Weak; first apply H. now do 2 right. }
    now apply Ctx.
  Qed.

  Lemma exists_compression φ k n : bounded (n + k) φ -> Qdec φ ->
    exists ψ, Qdec ψ /\ bounded (S k) ψ /\ Qeq ⊢I exist_times n φ <~> ∃ ψ.
  Proof.
    intros Hb HQ. revert Hb. induction n as [|n IH] in k |-*.
    2: destruct n. all: cbn.
    all: intros Hb.
    - exists φ[↑]. repeat split.
      { now apply Qdec_subst. }
      { eapply subst_bound; last apply Hb. intros n H. constructor. lia. }
      apply CI.
      + apply II. fexists $0. apply Ctx. now left.
      + apply II. eapply ExE; first (apply Ctx; now left).
        apply Ctx. now left.
    - exists φ. repeat split.
      + assumption.
      + cbn. replace (k - 0) with k by lia. assumption.
      + fsplit; fintros; ctx.
    - destruct (IH (S k)) as (ψ & HQ' & Hb' & H). 
      { now replace (S n + S k) with (S (S n) + k) by lia. }
      edestruct (@exists_compression_2 ψ) as (ψ' & HΔψ & Hbψ' & Hψ).
      1-2: eassumption.
      exists ψ'. repeat split; try easy.  cbn in H.
      apply CI.
      + apply II. eapply IE.
        { eapply CE1, Weak; first apply Hψ. now right. }
        eapply exists_equiv, CE1. eassumption.
      + apply II. eapply IE with (phi := ∃∃ψ); first last.
        { eapply IE.
          - eapply CE2, Weak; first apply Hψ. now right.
          - now apply Ctx. }
        eapply Weak with (A := Qeq); last now right.
        apply II. apply exists_equiv. eapply CE2. eassumption.
  Qed.

  Lemma Σ1_exist_times φ : Σ1 φ -> exists n ψ, Qdec ψ /\ φ = exist_times n ψ.
  Proof.
    induction 1 as [φ H (n & ψ & HΔ & Hψ)|φ H].
    - exists (S n), ψ. now rewrite Hψ.
    - now exists 0, φ.
  Qed.

  Lemma bounded_exist_times φ n k : bounded (n + k) φ <-> bounded k (exist_times n φ).
  Proof.
    induction n in k |-*; split.
    - easy.
    - easy.
    - cbn. intros H. constructor. apply IHn. replace (n + S k) with (S n + k) by lia. apply H.
    - cbn. invert_bounds. replace (S (n + k)) with (n + (S k)) by lia. now apply IHn. 
  Qed.

  (** # <a id="Sigma1_compression" /> #*)
  Lemma Σ1_compression φ n : bounded n φ -> Σ1 φ -> exists ψ, Qdec ψ /\ bounded (S n) ψ /\ Qeq ⊢I φ <~> ∃ψ.
  Proof.
    intros Hb (k & ψ & HΔ & ->)%Σ1_exist_times.
    destruct (@exists_compression ψ n k) as (ψ' & HΔ' & Hb' & H').
    all: firstorder using bounded_exist_times.
  Qed.
End Sigma1.



Section Sigma1completeness.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Existing Instance intu.

  (** # <a id="Sigma1_completeness" /> #*)
  Theorem Σ1_completeness_intu φ : Σ1 φ -> bounded 0 φ -> interp_nat ⊨= φ -> Qeq ⊢ φ.
  Proof.
    enough (forall ρ, Σ1 φ -> bounded 0 φ[ρ] -> interp_nat ⊨= φ[ρ] -> Qeq ⊢ φ[ρ]).
    { intros HΣ Hb Hsat. rewrite <-subst_var. apply H.
      - easy.
      - now rewrite subst_var.
      - intros ρ'. rewrite subst_var. apply Hsat. }
    intros ρ. induction 1 as [φ H IH|φ H] in ρ |-*.
    - cbn. invert_bounds.
      intros Hnat. destruct (Hnat (fun _ => 0)) as [d Hd].
      remember intu as Hintu. (* for proof mode *)
      fexists (num d). rewrite subst_comp. apply IH.
      + rewrite <-subst_comp. eapply subst_bound; last apply H4.
        intros [|n] Hn; last lia. apply num_bound.
      + intros ρ'. rewrite <-subst_comp.
        rewrite sat_single_nat in Hd.
        eapply sat_closed; last apply Hd.
        eapply subst_bound; last apply H4. 
        intros [|n] Hn; last lia. apply num_bound.
    - intros Hb Hnat.
      assert (Qdec φ[ρ]) as H'.
      { apply Qdec_subst, H. }
      destruct (H' intu (fun _ => zero)) as [H1|H1].
      { intros _. solve_bounds. }
      + rewrite bounded_0_subst in H1; assumption.
      + (* note: actually only requires consistency, can also be shown for classical *)
        eapply soundness in H1. cbn in H1. unfold valid_ctx in H1. 
        specialize (H1 _ interp_nat (fun _ => 0) (nat_is_Q_model _)).
        cbn in H1. destruct H1. rewrite bounded_0_subst; auto.
  Qed.


  (*(** # <a id="Sigma1_witness" /> #*)*)
  (*Theorem Σ1_witness_intu φ : Σ1 φ -> bounded 1 φ -> Qeq ⊢ ∃φ -> exists x, Qeq ⊢ φ[(num x)..].*)
  (*Proof.*)
  (*  intros Hb HΣ Hφ. eapply Σ1_soundness with (rho := fun _ => 0) in Hφ as [x Hx].*)
  (*  exists x. eapply Σ1_completeness with (ρ := fun _ => 0).*)
  (*  - now apply Σ1_subst.*)
  (*  - eapply subst_bound; last eassumption.*)
  (*    intros [|n] H; last lia. apply num_bound.*)
  (*  - eapply sat_closed; first last.*)
  (*    + rewrite <-sat_single_nat. apply Hx.*)
  (*    + eapply subst_bound; last eassumption.*)
  (*      intros [|n] H; last lia. apply num_bound.*)
  (*Qed.*)

End Sigma1completeness.

Section conservativity.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Lemma Σ1_conservativity ϕ :
    Σ1 ϕ -> bounded 0 ϕ -> Qeq ⊢C ϕ -> Qeq ⊢I ϕ.
  Proof. 
    intros S1 Hcl Htc.
    destruct (Σ1_compression Hcl S1) as [α (dec_α & b1_α & Hα)].
    assert (bounded 0 (∃ α)) as b0_α by (now solve_bounds).
    eapply IE with (∃ α).
    1: eapply CE2; apply Hα.
    apply Σ1_completeness_intu; auto.
    1: do 2 constructor; auto.
    assert (Qeq ⊢C ∃ α) as H.
    { eapply IE with ϕ; auto.
      apply prv_intu_class. 
      eapply CE1. apply Hα. }
    apply Fr_cl_to_min, soundness in H.
    refine (let H' := H nat (extend_interp interp_nat _) (fun _ => 0) _ in _).
    cbn in H'; apply H'. clear H H'.
    intros [n Hn].
    destruct (dec_α intu (fun _ => num n)) as [H|H].
    - intro. apply num_bound.
    - exists n. apply soundness in H.
      eapply sat_single_nat. 
      erewrite bounded_subst.
      + apply H, nat_is_Q_model.
      + eauto.
      + intros []; [reflexivity|lia].
    - apply prv_intu_class with (p:=class) in H.
      apply Fr_cl_to_min, soundness in H.
      refine (let H' := H nat (extend_interp interp_nat _) (fun _ => 0) _ in _).
      cbn in H'. apply H'; clear H H'.
      rewrite <-subst_Fr. apply sat_comp.
      eapply FullTarski_facts.bound_ext with (N:=1).
      3 : apply Hn.
      { now apply bounded_Fr. }
      intros []; [intros _;cbn|lia].
      apply nat_eval_num.
      Unshelve. all: apply nat_sat_Fr_Q.
  Qed.

  Context {pei : peirce}.

  Lemma Σ1_soundness ϕ :
    Σ1 ϕ -> bounded 0 ϕ -> Qeq ⊢ ϕ -> interp_nat ⊨= ϕ.
  Proof.
    Set Printing Implicit.
    intros HΣ Hb Hϕ. intros ρ. 
    destruct pei eqn:H; eapply soundness. 
    - apply Σ1_conservativity.
      * congruence.
      * assumption.
      * assumption.
    - apply nat_is_Q_model.
    - apply Hϕ.
    - apply nat_is_Q_model.
  Qed.

End conservativity.

Section Sigma1completeness.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context `{pei : peirce}.

  (** # <a id="Sigma1_completeness" /> #*)
  Theorem Σ1_completeness φ : Σ1 φ -> bounded 0 φ -> interp_nat ⊨= φ -> Qeq ⊢ φ.
  Proof.
    destruct pei; last apply Σ1_completeness_intu.
    enough (forall ρ, Σ1 φ -> bounded 0 φ[ρ] -> interp_nat ⊨= φ[ρ] -> Qeq ⊢C φ[ρ]).
    { intros HΣ Hb Hsat. rewrite <-subst_var. apply H.
      - easy.
      - now rewrite subst_var.
      - intros ρ'. rewrite subst_var. apply Hsat. }
    intros ρ. induction 1 as [φ H IH|φ H] in ρ |-*.
    - cbn. invert_bounds.
      intros Hnat. destruct (Hnat (fun _ => 0)) as [d Hd].
      remember intu as Hintu. (* for proof mode *)
      fexists (num d). rewrite subst_comp. apply IH.
      + rewrite <-subst_comp. eapply subst_bound; last apply H4.
        intros [|n] Hn; last lia. apply num_bound.
      + intros ρ'. rewrite <-subst_comp.
        rewrite sat_single_nat in Hd.
        eapply sat_closed; last apply Hd.
        eapply subst_bound; last apply H4. 
        intros [|n] Hn; last lia. apply num_bound.
    - intros Hb Hnat.
      assert (@Qdec φ[ρ]) as H'.
      { apply Qdec_subst, H. }
      destruct (H' class (fun _ => zero)) as [H1|H1].
      { intros _. solve_bounds. }
      all: rewrite bounded_0_subst in H1; try eassumption.
      contradict Hnat.
      apply Σ1_soundness with (rho := fun _ => 0) in H1.
      + cbn in H1. contradict H1. apply H1.
      + constructor. apply Qdec_impl.
        * assumption.
        * apply Qdec_bot.
      + now solve_bounds.
  Qed.


  (** # <a id="Sigma1_witness" /> #*)
  Theorem Σ1_witness φ : Σ1 φ -> bounded 1 φ -> Qeq ⊢ ∃φ -> exists x, Qeq ⊢ φ[(num x)..].
  Proof.
    intros Hb HΣ Hφ. eapply Σ1_soundness with (rho := fun _ => 0) in Hφ as [x Hx].
    exists x. eapply Σ1_completeness.
    - now apply Σ1_subst.
    - eapply subst_bound; last eassumption.
      intros [|n] H; last lia. apply num_bound.
    - intros ρ. rewrite sat_single_nat in Hx. 
      eapply sat_closed; last eassumption.
      eapply subst_bound; last eassumption.
      intros [|n] H; lia + apply num_bound.
    - now constructor.
    - now constructor.
  Qed.

End Sigma1completeness.
