From Undecidability.FOL.Util Require Import Syntax sig_bin.
From Undecidability.FOL.Util Require  Tarski Deduction Kripke.
From Undecidability.DiophantineConstraints Require Import H10UPC H10UPC_undec.
From Undecidability.FOL.Reductions Require H10UPC_to_FOL_minimal H10UPC_to_FSAT.
From Undecidability.Synthetic Require Import Definitions Undecidability.

Definition minimalForm (ff:falsity_flag) := @form sig_empty sig_binary FragmentSyntax.frag_operators ff.


Section general.
  Import H10UPC_to_FOL_minimal Tarski Deduction Kripke.

  Lemma minValidityUndec : undecidable (fun k : minimalForm falsity_off => valid k).
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact validReduction.
  Qed.

  Lemma minKripkeValidityUndec : undecidable (fun k : minimalForm falsity_off => kvalid k).
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact kripkeValidReduction.
  Qed.

  Definition int_provable (phi : minimalForm falsity_off) : Prop := nil ⊢M phi.
  Definition class_provable (phi : minimalForm falsity_off) : Prop := nil ⊢C phi.

  Lemma minProvabilityUndec : undecidable int_provable.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact proveReduction.
  Qed.

  Lemma minClassicalProvabilityUndec (LEM : forall P:Prop, P \/ ~P) : undecidable class_provable.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    apply classicalProveReduction, LEM.
  Qed.

  Lemma minSatisfiabilityReduc : (complement H10UPC_SAT) ⪯  (fun k : minimalForm falsity_on => satis k).
  Proof.
    apply satisReduction.
  Qed.

  Lemma minKripkeSatisfiabilityReduc : (complement H10UPC_SAT) ⪯  (fun k : minimalForm falsity_on => ksatis k).
  Proof.
    apply kripkeSatisReduction.
  Qed.
  
End general.


Section finite.
  Import H10UPC_to_FSAT.
  (** Reduction into fragment syntax. Step 1: define FSAT for fragment syntax *)
  Definition FSAT_frag (phi : minimalForm falsity_on) :=
  exists D (I : Tarski.interp D) rho, FSAT.listable D /\ decidable (fun v => Tarski.i_atom (P:=tt) v) /\ @Tarski.sat _ _ D I _ rho phi.

  (** Also define FVAL for fragment syntax *)
  Definition FVAL_frag (phi : minimalForm falsity_on) :=
  forall D (I : Tarski.interp D) rho, FSAT.listable D /\ decidable (fun v => Tarski.i_atom (P:=tt) v) -> @Tarski.sat _ _ D I _ rho phi.

  (** Also define FVAL for negation-free fragment *)
  Definition FVAL_frag_no_negation (phi : minimalForm falsity_off) :=
  forall D (I : Tarski.interp D) rho, FSAT.listable D /\ decidable (fun v => Tarski.i_atom (P:=tt) v) -> @Tarski.sat _ _ D I _ rho phi.

  Lemma minFiniteSatisfiabilityUndec : undecidable FSAT_frag.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    eapply reduces_transitive.
    * eexists. apply fsat_reduction.
    * eexists. apply frag_reduction_fsat.
  Qed.

  Lemma minFiniteValidityReduction : (Definitions.complement H10UPC_SAT) ⪯ FVAL_frag.
  Proof.
    eapply reduces_transitive.
    * eexists. apply fval_reduction.
    * eexists. apply frag_reduction_fval.
  Qed.

  (** This is a conjecture *)
  Lemma minFiniteValidityConjecture : (Definitions.complement H10UPC_SAT) ⪯ FVAL_frag_no_negation.
  Abort.

End finite.

