(* TODO deduplicate imports *)
From Undecidability.FOL.Incompleteness Require Import utils.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.

Require Import Undecidability.Shared.Libs.DLW.Vec.vec.

From Equations Require Import Equations.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
Require Import String List.
Open Scope string_scope.

(** * First-order logic *)

(* Notation for satisfying list theories *)
Notation "I ⊨=L T" := (forall psi, List.In psi T -> I ⊨= psi) (at level 20).
(* Notation for explicitely giving model *)
Notation "I ; rho '⊨' phi" := (@sat _ _ _ I _ rho phi) (at level 20, rho at next level).


(* Utilities for first-order logic *)
Section lemmas.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.

  Context `{pei : peirce}.

  Lemma num_subst x ρ : (num x)`[ρ] = num x.
  Proof.
    induction x; cbn; congruence.
  Qed.

  Lemma num_bound n k : bounded_t k (num n).
  Proof.
    induction n; cbn; constructor.
    - intros t []%Vectors.In_nil.
    - intros t ->%vec_singleton.
      assumption.
  Qed.

  Lemma subst_bound_t {ff : falsity_flag} n m t sigma : 
    (forall i, i < n -> bounded_t m (sigma i)) -> bounded_t n t -> bounded_t m (t`[sigma]).
  Proof.
    intros Hi. induction 1 as [|? ? ? IH].
    - cbn. apply Hi. lia.
    - cbn. econstructor. intros t [x [<- Hx]]%Vectors.vect_in_map_iff.
      now apply IH.
  Qed.

  Lemma subst_bounded_up_t {ff : falsity_flag} i m sigma : 
    (forall i', i' < i -> bounded_t m (sigma i')) -> bounded_t (S m) (up sigma i).
  Proof.
    intros Hb. unfold up,funcomp,scons. destruct i.
    - econstructor. lia.
    - eapply subst_bound_t. 2: apply Hb. 2:lia.
      intros ii Hii. econstructor. lia.
  Qed.

  Lemma subst_bound {ff : falsity_flag} n m phi sigma : 
    (forall i, i < n -> bounded_t m (sigma i)) -> bounded n phi -> bounded m (phi[sigma]).
  Proof. intros Hi.
    induction 1 as [ff n P v H| bo ff n phi psi H1 IH1 H2 IH2| qo ff n phi H1 IH1| n] in Hi,sigma,m|-*; cbn; econstructor.
    - intros t [x [<- Hx]]%Vectors.vect_in_map_iff. eapply subst_bound_t. 1: exact Hi. now apply H.
    - apply IH1. easy.
    - apply IH2. easy.
    - apply IH1. intros l Hl.
      apply subst_bounded_up_t. intros i' Hi'. apply Hi. lia.
  Qed.

  Lemma up_invert_bound_t n t :
    bounded_t (S n) t`[↑] -> bounded_t n t.
  Proof. 
    induction t.
    - unfold "↑". cbn. inversion 1. constructor. lia.
    - cbn. inversion 1.
      constructor. intros t Ht.
      apply IH; first assumption.
      apply H1.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; try decide equality. subst.
      now apply Vectors.vect_in_map.
  Qed.


  Lemma prv_intu_class T φ p : @prv _ _ _ intu T φ -> @prv _ _ _ p T φ.
  Proof.
    remember intu as p' eqn:H.
    induction 1.
    15: discriminate. 
    1,3,4,7-9,12,13: auto.
    - eapply IE; eauto.
    - eapply ExI; eauto.
    - eapply ExE; eauto.
    - eapply CE1; eauto.
    - eapply CE2; eauto.
    - eapply DE; eauto.
  Qed.

  Lemma iμ_eval_num M (I : interp M) k ρ : iμ k = eval ρ (num k).
  Proof.
    induction k; cbn; congruence.
  Qed.

  Lemma iμ_standard (k : nat) : iμ k = k.
  Proof.
    induction k; cbn; congruence.
  Qed.

  Lemma sat_single_PA M (I : interp M) φ ρ k : (iμ k .: ρ) ⊨ φ <-> ρ ⊨ φ[(num k)..].
  Proof.
    erewrite iμ_eval_num. apply sat_single.
  Qed.

  Lemma sat_single_nat φ ρ k : interp_nat; (k .: ρ) ⊨ φ <-> interp_nat; ρ ⊨ φ[(num k)..].
  Proof.
    erewrite <-iμ_standard at 1.
    now rewrite sat_single_PA.
  Qed.


  Lemma eval_up ρ s t :
    eval (s .: ρ) t`[↑] = eval ρ t.
  Proof.
    rewrite eval_comp. now apply eval_ext.
  Qed.


  Lemma subst_cons_comp2 φ x y :
    φ[num x .: (num y) ..] = φ[(num x)..][(num y)..].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [|[|n]]; cbn; now rewrite ?num_subst.
  Qed.
  Lemma subst_cons_comp3 φ x y z :
    φ[num x .: num y .: (num z) ..] = φ[num x .: (num y)..][(num z)..].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [|[|[|n]]]; cbn; now rewrite ?num_subst.
  Qed.


  Lemma AllE_Ctx A χ ψ t :
    In (∀ψ) A -> (ψ[t..] :: A) ⊢ χ -> A ⊢ χ.
  Proof.
    intros H1 H2. eapply IE.
    - apply II, H2.
    - apply AllE, Ctx, H1.
  Qed.
  Lemma AllI_named (A : list form) (phi : form) :
    (forall t, A ⊢ phi[t..]) -> A ⊢ ∀phi.
  Proof.
    intros H. apply AllI. 
    destruct (nameless_equiv_all A phi) as [t Ht].
    apply Ht, H.
  Qed.
  Lemma ExE_named A χ ψ :
    A ⊢ ∃ χ -> (forall t, (χ[t..]::A) ⊢ ψ) -> A ⊢ ψ.
  Proof.
    intros H1 H2. destruct (nameless_equiv_ex A χ ψ) as [t Ht].
    eapply ExE.
    - eassumption.
    - apply Ht, H2.
  Qed.

End lemmas.


Lemma enumerable_PA_funcs : enumerable__T PA_funcs.
Proof.
  cbn. exists (fun k => match k with
    | 0 => Some Zero
    | 1 => Some Succ
    | 2 => Some Plus
    | _ => Some Mult
    end).
  intros [].
  + now exists 0.
  + now exists 1.
  + now exists 2.
  + now exists 3.
Qed.
Lemma enumerable_PA_preds : enumerable__T PA_preds.
Proof.
  exists (fun _ => Some Eq). intros []. now exists 0.
Qed.
Lemma list_theory_enumerable {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} A : 
  enumerable (list_theory A).
Proof.
  exists (List.nth_error A).
  intros x. split.
  - apply List.In_nth_error.
  - intros [k Hk]. eapply List.nth_error_In, Hk.
Qed.




(* Definitions of comparisions *)
Section syntax.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  (* Notation for satisfying list theories *)
  Notation "I ⊨=L T" := (forall psi, List.In psi T -> I ⊨= psi) (at level 20).
  (* Notation for explicitely giving model *)
  (* TODO possibility: use I ⊨ rho phi, similar to Coq *)
  Notation "I ; rho '⊨' phi" := (@sat _ _ _ I _ rho phi) (at level 20, rho at next level).

  Definition pless x y := ∃ y`[↑] == (x`[↑] ⊕ $0).
  Definition pless_swap x y := ∃ y`[↑] == ($0 ⊕ x`[↑]).
  (* NOTE this definition requires extensionality of the model *)
  Definition mless {M} {I : interp M} x y := exists k, y = x i⊕ k.

  Lemma pless_eq x y : pless x y = ∃ y`[↑] == (x`[↑] ⊕ $0).
  Proof. reflexivity. Qed.

  Lemma pless_subst x y ρ : (pless x y)[ρ] = pless (x`[ρ]) (y`[ρ]).
  Proof.
    rewrite !pless_eq. cbn. do 3 f_equal.
    - rewrite !subst_term_comp. reflexivity. 
    - do 3 f_equal. rewrite !subst_term_comp. reflexivity. 
  Qed.

  Lemma pless_invert_bound n x y : bounded n (pless x y) -> bounded_t n x /\ bounded_t n y.
  Proof.
    unfold pless. intros Hb.
    inversion Hb. subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H3; try decide equality. subst.
    inversion H2. subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H4; try decide equality. subst.
    split.
    - assert (bounded_t (S n) (x`[↑] ⊕ $0)) as H by (apply H3; right; left).
      inversion H. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H4; try decide equality. subst.
      apply up_invert_bound_t. apply H1. left.
    - apply up_invert_bound_t. apply H3. left.
  Qed.


  Lemma pless_swap_eq x y : pless_swap x y = ∃ y`[↑] == ($0 ⊕ x`[↑]).
  Proof. reflexivity. Qed.

  Lemma pless_swap_subst x y ρ : (pless_swap x y)[ρ] = pless_swap (x`[ρ]) (y`[ρ]).
  Proof.
    rewrite !pless_swap_eq. cbn. do 3 f_equal.
    - rewrite !subst_term_comp. reflexivity. 
    - do 3 f_equal. rewrite !subst_term_comp. reflexivity. 
  Qed.

  Lemma pless_swap_invert_bound n x y : bounded n (pless_swap x y) -> bounded_t n x /\ bounded_t n y.
  Proof.
    unfold pless_swap. intros Hb.
    inversion Hb. subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H3; try decide equality. subst.
    inversion H2. subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H4; try decide equality. subst.
    split.
    - assert (bounded_t (S n) ($0 ⊕ x`[↑])) as H by (apply H3; right; left).
      inversion H. subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H4; try decide equality. subst.
      apply up_invert_bound_t. apply H1. right. left.
    - apply up_invert_bound_t. apply H3. left.
  Qed.

  Lemma bounded_t_0_subst t ρ : bounded_t 0 t -> t`[ρ] = t.
  Proof.
    intros H. setoid_rewrite <-subst_term_var at 3. 
    eapply bounded_subst_t; last eassumption. lia.
  Qed.
  Lemma bounded_0_subst φ ρ : bounded 0 φ -> φ[ρ] = φ.
  Proof.
    intros H. setoid_rewrite <-subst_var at 3. eapply bounded_subst; first eassumption. lia.
  Qed.




  (* The definitions are opaque to avoid automatic unfolding when simplifying substitutions *)
  Global Opaque pless.
  Global Opaque pless_swap.
End syntax.
(* Notations for le *)
Notation "x '⧀=' y"  := (pless x y) (at level 42) : PA_Notation.
Notation "x '⧀=comm' y"  := (pless_swap x y) (at level 42) : PA_Notation.
Notation "x 'i⧀=' y"  := (mless x y) (at level 42) : PA_Notation.

(* Make Qeq opaque to avoid simplifying under normal circumstances *)
(* The definition does not actually become completely opaque and many goals are
 * still solvable *)
Definition Qeq := PA.Qeq.
Global Opaque Qeq.
Lemma Qeq_def : Qeq = PA.Qeq.
Proof. reflexivity. Qed.

(* setup proofmode *)
Section PM.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Global Program Instance PA_Leibniz : Leibniz PA_funcs_signature PA_preds_signature falsity_on.
  Next Obligation. exact Eq. Defined.
  Next Obligation. exact Qeq. Defined.
  Next Obligation. fintros. fapply ax_refl. Qed.
  Next Obligation. fintros. fapply ax_sym. ctx. Qed.
  Next Obligation.
    unfold PA_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
    destruct F; repeat dependent elimination t0; repeat dependent elimination t.
    - fapply ax_refl.
    - fapply ax_succ_congr. apply H1.
    - fapply ax_add_congr; apply H1.
    - fapply ax_mult_congr; apply H1.
  Qed.
  Next Obligation.
    unfold PA_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
    destruct P; repeat dependent elimination t0; repeat dependent elimination t.
    - cbn in H1. split.
      + intros H2. feapply ax_trans. feapply ax_sym. apply H1. feapply ax_trans.
        apply H2. apply H1.
      + intros H2. feapply ax_trans. apply H1. feapply ax_trans. apply H2.
        fapply ax_sym. apply H1.
  Qed.


End PM.
Global Ltac custom_simpl ::= cbn; rewrite ?pless_subst; cbn; rewrite ?num_subst; cbn.
Global Notation "'σh' x" := (bFunc Succ (Vector.cons bterm x 0 (Vector.nil bterm))) (at level 32) : hoas_scope.
Global Notation "x '⊕h' y" := (bFunc Plus (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 39) : hoas_scope.
Global Notation "x '⊗h' y" := (bFunc Mult (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 38) : hoas_scope. 
Global Notation "x '==h' y" := (bAtom Eq (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 40) : hoas_scope.


(* Tactic for boundedness inversions *)
Global Ltac invert_bounds :=
  inversion 1; subst;
  repeat match goal with
           H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep_dec.inj_pair2_eq_dec in H; try decide equality
         end; subst.

(* Closed terms are numerabls *)
Section n.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Context `{pei : peirce}.

  Lemma closed_term_is_num s : bounded_t 0 s -> { n & Qeq ⊢ s == num n }.
  Proof.
    intros H. 
    induction s using term_rect. 2: destruct F.
    - exfalso. inversion H. lia.
    - rewrite (vec_0_nil v). exists 0.
      fapply ax_refl.
    - destruct (vec_1_inv v) as [t ->]. destruct (X t) as [n Hn].
      + left.
      + revert H. invert_bounds. apply H1. left.
      + exists (S n). fapply ax_succ_congr. apply Hn.
    - destruct (vec_2_inv v) as (t1 & t2 & ->). 
      destruct (X t1, X t2) as [[n1 Hn1] [n2 Hn2]].
      + left.
      + revert H. invert_bounds. apply H1. left.
      + right. left.
      + revert H. invert_bounds. apply H1. right. left.
      + exists (n1 + n2).
        pose proof num_add_homomorphism as H'.
        refine ((fun H'' => _) (H' _ Qeq _ n1 n2)).
        2: { firstorder. }
        frewrite <-H''.
        fapply ax_add_congr; assumption.
    - destruct (vec_2_inv v) as (t1 & t2 & ->). 
      destruct (X t1, X t2) as [[n1 Hn1] [n2 Hn2]].
      + left.
      + revert H. invert_bounds. apply H1. left.
      + right. left.
      + revert H. invert_bounds. apply H1. right. left.
      + exists (n1 * n2).
        pose proof num_mult_homomorphism as H'.
        refine ((fun H'' => _) (H' _ Qeq _ n1 n2)).
        2: { firstorder. }
        frewrite <-H''.
        fapply ax_mult_congr; assumption.
  Qed.

End n.
