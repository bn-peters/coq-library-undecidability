(* TODO deduplicate imports *)
From Undecidability.FOL.Incompleteness Require Import utils.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.

From Equations Require Import Equations.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
From Undecidability.FOL.Incompleteness Require Import fol qdec sigma1.


Require Import Setoid.

Require Import Undecidability.Shared.Libs.DLW.Vec.vec.

Require Import String.
Open Scope string_scope.

Section bin_qdec.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.

  Existing Instance intu.

  Lemma bin_bounded_forall_iff t φ : bounded_t 0 t -> 
    Qeq ⊢ (∀∀ ($1 ⊕ $0 ⧀= t) ~> φ) <~>
          (∀ ($0 ⧀= t) ~> ∀ ($0 ⧀= $1) ~> ∀ ($0 ⧀= $2) ~> ($1 ⊕ $0 ⧀= t) ~> φ[up (up ↑)]).
  Proof.
    intros Hb. destruct (closed_term_is_num Hb) as [t' Ht'].
    rewrite !pless_eq. cbn. unfold "↑". 
    fstart. fsplit.
    - fintros "H" z "[z' Hz']". cbn.
      fintros x "[x' Hx']".
      fintros y "[y' Hy']" "[xy' Hxy']".
      fspecialize ("H" x y).
      replace (φ[_][_][_][_]) with (φ[up x..][y..]).
      2: { rewrite !subst_comp. apply subst_ext.
        intros [|[|n]]; reflexivity. }
      fapply "H". fexists xy'. rewrite !(bounded_t_0_subst _ Hb). fapply "Hxy'".
    - fintros "H" x y. fintros "[z Hz]".
      fspecialize ("H" t).
      fdestruct "H".
      { rewrite !(bounded_t_0_subst _ Hb).
        fassert (t == num t') by fapply Ht'. frewrite "H".
        fexists zero. admit. }
      fdestruct ("H" x).
      { fexists (y ⊕ z). admit. }
      fdestruct ("H" y).
      { fexists (x ⊕ z). admit. }
      { fexists z. rewrite !(bounded_t_0_subst _ Hb). fapply "Hz". }
      replace (φ[_][_][_][_]) with (φ[up x..][y..]).
      2: { rewrite !subst_comp. apply subst_ext.
        now intros [|[|n]]. }
      ctx.
  Admitted.

  Lemma qdec_bin_bounded_forall t φ :
    Qdec φ -> Qdec (∀∀ $1 ⊕ $0 ⧀= t`[↑]`[↑] ~> φ).
  Proof.
    intros Hφ. 
    eapply (@Qdec_iff' _ (∀ ($0 ⧀= t`[↑]) ~> ∀ ($0 ⧀= $1) ~> ∀ ($0 ⧀= $2) ~> ($1 ⊕ $0 ⧀= t`[↑]`[↑]`[↑]) ~> φ[up (up ↑)])).
    - intros ρ Hb.
      cbn. rewrite !pless_subst. cbn. rewrite !up_term.
      unfold "↑".
      assert (bounded_t 0 t`[ρ]) as Ht.
      { destruct (find_bounded_t t) as [k Hk].
        eapply subst_bound_t; last eassumption. auto. }
      pose proof (@bin_bounded_forall_iff t`[ρ] φ Ht).
      pose proof (subst_Weak ρ H) as H'. change (List.map _ _) with Qeq in H'.
      apply frewrite_equiv_switch. 
      cbn in H'. rewrite !pless_subst in H'.
      rewrite !(bounded_t_0_subst _ Ht). rewrite !(bounded_t_0_subst _ Ht) in H'.
      apply H'.
    - apply Qdec_bounded_forall.
      apply Qdec_bounded_forall with (t0 := $0).
      apply Qdec_bounded_forall with (t0 := $1).
      apply Qdec_impl.
      + apply Qdec_le.
      + apply Qdec_subst, Hφ.
  Qed.


End bin_qdec.
