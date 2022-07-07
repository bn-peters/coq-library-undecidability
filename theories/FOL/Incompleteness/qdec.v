(* TODO deduplicate imports *)
From Undecidability.FOL.Incompleteness Require Import utils.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.

From Equations Require Import Equations.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
From Undecidability.FOL.Incompleteness Require Import fol.


Require Import Setoid.

Require Import Undecidability.Shared.Libs.DLW.Vec.vec.

Require Import String.
Open Scope string_scope.

(** ** Q-decidability *)
Section Qdec.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {p : peirce}.

  Definition Qdec φ := forall ρ, (forall k, bounded_t 0 (ρ k)) -> Qeq ⊢ φ[ρ] \/ Qeq ⊢ ¬φ[ρ].

  Lemma subst_t_closed t ρ : (forall k, bounded_t 0 (ρ k)) -> bounded_t 0 t`[ρ].
  Proof.
    intros H. destruct (find_bounded_t t) as [n Hn].
    eapply subst_bound_t; last eassumption.
    intros l _. apply H.
  Qed.
  Lemma subst_closed φ ρ : (forall k, bounded_t 0 (ρ k)) -> bounded 0 φ[ρ].
  Proof.
    intros H. destruct (find_bounded φ) as [n Hn].
    eapply subst_bound; last eassumption.
    intros l _. apply H.
  Qed.

  Lemma Qdec_subst φ ρ : Qdec φ -> Qdec φ[ρ].
  Proof.
    intros H ρ' Hb. rewrite subst_comp. apply H.
    intros k. apply subst_t_closed, Hb.
  Qed.

  Lemma Qdec_iff φ ψ : Qeq ⊢ φ <~> ψ -> Qdec φ -> Qdec ψ.
  Proof.
    intros H Hφ ρ Hρ. 
    pose proof (subst_Weak ρ H) as Hiff. cbn in Hiff. change (List.map _ _) with Qeq in Hiff.
    destruct (Hφ ρ Hρ) as [H1|H1].
    - left. fapply Hiff. fapply H1.
    - right. fintros. fapply H1. fapply Hiff. ctx.
  Qed.
  (* TODO use this lemma for qdec proofs below! *)
  Lemma Qdec_iff' φ ψ : 
    (forall ρ, (forall k, bounded_t 0 (ρ k)) -> Qeq ⊢ φ[ρ] <~> ψ[ρ]) -> 
    Qdec φ -> Qdec ψ.
  Proof.
    intros H Hφ ρ Hρ.
    specialize (H _ Hρ). destruct (Hφ _ Hρ) as [H1|H1].
    - left. fapply H. fapply H1.
    - right. fintros. fapply H1. fapply H. ctx.
  Qed.

  Lemma Qdec_bot : Qdec ⊥.
  Proof.
    intros ρ Hb. right. fintros. ctx.
  Qed.

  Lemma Qdec_and φ ψ : Qdec φ -> Qdec ψ -> Qdec (φ ∧ ψ).
  Proof. 
    intros Hφ Hψ ρ Hb. cbn.
    destruct (Hφ _ Hb) as [H1|H1], (Hψ _ Hb) as [H2|H2].
    2-4: right; fintros; fdestruct 0.
    - left. now fsplit.
    - fapply H2. ctx.
    - fapply H1. ctx.
    - fapply H1. ctx.
  Qed.

  Lemma Qdec_or φ ψ : Qdec φ -> Qdec ψ -> Qdec (φ ∨ ψ).
  Proof. 
    intros Hφ Hψ ρ Hb. cbn.
    destruct (Hφ _ Hb) as [H1|H1], (Hψ _ Hb) as [H2|H2].
    1-3: left; now (fleft + fright).
    right. fintros "[H|H]".
    - fapply H1. ctx.
    - fapply H2. ctx.
  Qed.

  Lemma Qdec_impl φ ψ : Qdec φ -> Qdec ψ -> Qdec (φ ~> ψ). 
  Proof.
    intros Hφ Hψ ρ Hb. cbn.
    destruct (Hφ _ Hb) as [H1|H1], (Hψ _ Hb) as [H2|H2].
    - left. fintros. fapply H2.
    - right. fintros. fapply H2. fapply 0. fapply H1.
    - left. fintros. fapply H2.
    - left. fintros. fexfalso. fapply H1. ctx.
  Qed.
  
  Lemma Qdec_eq t s : Qdec (t == s).
  Proof.
    intros ρ Hb. cbn. 
    destruct (@closed_term_is_num _ t`[ρ]) as [k1 Hk1].
    { apply subst_t_closed, Hb. }
    destruct (@closed_term_is_num _ s`[ρ]) as [k2 Hk2].
    { apply subst_t_closed, Hb. }
    assert (k1 = k2 \/ k1 <> k2) as [->|Hk] by lia; [left|right].
    all: frewrite Hk1; frewrite Hk2.
    - fapply ax_refl.
    - clear Hk1. clear Hk2. revert Hk. induction k1 in k2 |-*; intros Hk.
      + destruct k2; first congruence. cbn.
        fapply ax_zero_succ.
      + cbn. destruct k2.
        * fintros. fapply (ax_zero_succ (num k1)). fapply ax_sym. ctx.
        * cbn. fintros. assert (H' : k1 <> k2) by congruence.
          specialize (IHk1 k2 H'). fapply IHk1.
          fapply ax_succ_inj. ctx.
  Qed.
  Lemma Qdec_le t s : Qdec (t ⧀= s).
  Proof.
    intros ρ Hb.
    destruct (@closed_term_is_num _ t`[ρ]) as [k1 Hk1].
    { apply subst_t_closed, Hb. }
    destruct (@closed_term_is_num _ s`[ρ]) as [k2 Hk2].
    { apply subst_t_closed, Hb. }
    assert (k1 <= k2 \/ ~k1 <= k2) as [Hk|Hk] by lia.
    - left. rewrite pless_eq. cbn. fexists (num (k2 - k1)).
      frewrite Hk1. frewrite Hk2.
      clear Hk2 Hk1. induction k2 as [|k2 IH].
      + assert (k1 = 0) as -> by lia. cbn.
        frewrite (ax_add_zero zero). fapply ax_refl.
      + assert (k1 = S k2 \/ k1 <= k2) as [->|H] by lia.
        * replace (S k2 - S k2) with 0 by lia.
          cbn. admit.
        * cbn. admit.
    - admit.
  Admitted.

  Lemma Q_eqdec t x : Qeq ⊢ x == (num t) ∨ ¬(x == num t).
  Proof. 
    induction t in x |-*; fstart; fintros.
    - fassert (ax_cases); first ctx.
      fdestruct ("H" x).
      + fleft. frewrite "H".
        fapply ax_refl.
      + fright. fdestruct "H". frewrite "H".
        fintros. fapply (ax_zero_succ x0).
        fapply ax_sym. ctx.
    - fassert (ax_cases); first ctx.
      fdestruct ("H" x).
      + fright. frewrite "H".
        fapply ax_zero_succ.
      + fdestruct "H". frewrite "H".
        specialize (IHt x0). 
        fdestruct IHt.
        * fleft. fapply ax_succ_congr. fapply "H0".
        * fright. fintros. fapply "H0".
          fapply ax_succ_inj. fapply "H1".
  Qed.

  Lemma pless_zero_eq x : Qeq ⊢ x ⧀= zero ~> x == zero.
  Proof.
    rewrite !pless_eq.
    fstart. fintros. fdestruct "H".
    fassert ax_cases.
    { ctx. }
    unfold ax_cases.
    fdestruct ("H0" x).
    - fapply "H0".
    - fdestruct "H0".
      fexfalso. fapply (ax_zero_succ (x1 ⊕ x0)).
      frewrite <- (ax_add_rec x0 x1). frewrite <- "H0".
      fapply "H".
  Qed.
  Lemma pless_swap_zero_eq x : Qeq ⊢ (x ⧀=comm zero) ~> x == zero.
  Proof.
    rewrite !pless_swap_eq. 
    fstart. fintros. fdestruct "H".
    fassert ax_cases as "C"; first ctx.
    fdestruct ("C" x0) as "[Hx'|[x' Hx']]".
    - frewrite <-(ax_add_zero x). frewrite <-"Hx'".
      frewrite <-"H". frewrite "Hx'". fapply ax_refl.
    - fexfalso. fapply (ax_zero_succ (x' ⊕ x)).
      frewrite <-(ax_add_rec x x'). frewrite <-"Hx'".
      fapply "H".
  Qed.

  Lemma add_zero_swap t x :
    Qeq ⊢ x ⊕ zero == num t ~> x == num t.
  Proof.
    fstart. induction t in x |-*; fintros.
    - fassert (ax_cases); first ctx.
      fdestruct ("H0" x).
      + ctx.
      + fdestruct "H0".
        fexfalso. fapply (ax_zero_succ (x0 ⊕ zero)).
        frewrite <- (ax_add_rec zero x0). 
        frewrite <-"H0". fapply ax_sym. ctx.
    - fassert (ax_cases); first ctx.
      fdestruct ("H0" x).
      + fexfalso. fapply (ax_zero_succ (num t)).
        frewrite <-"H". frewrite "H0".
        frewrite (ax_add_zero zero).
        fapply ax_refl.
      + fdestruct "H0".
        frewrite "H0". fapply ax_succ_congr.
        specialize (IHt x0). 
        fapply IHt. fapply ax_succ_inj.
        frewrite <-(ax_add_rec zero x0).
        frewrite <- "H0". fapply "H".
  Qed.

  Lemma add_rec_swap t x y:
    Qeq ⊢ x ⊕ σ y == σ num t ~> x ⊕ y == num t.
  Proof. 
    induction t in x |-*; fstart; fintros "H".
    - fassert ax_cases as "C"; first ctx.
      fdestruct ("C" x) as "[Hx|[x' Hx']]".
      + frewrite "Hx". frewrite (ax_add_zero y).
        fapply ax_succ_inj. frewrite <-(ax_add_zero (σ y)).
        frewrite <-"H". frewrite "Hx". fapply ax_refl.
      + frewrite "Hx'". fassert ax_cases as "C"; first ctx.
        fdestruct ("C" x') as "[Hx''|[x'' Hx'']]".
        * fexfalso. fapply (ax_zero_succ y). 
          fapply ax_succ_inj. frewrite <-"H".
          frewrite "Hx'". frewrite "Hx''".
          frewrite (ax_add_rec (σ y) zero). frewrite (ax_add_zero (σ y)).
          fapply ax_refl.
        * fexfalso. fapply (ax_zero_succ (x'' ⊕ σ y)). 
          fapply ax_succ_inj. frewrite <-"H".
          frewrite "Hx'". frewrite "Hx''".
          frewrite (ax_add_rec (σ y) (σ x'')).
          frewrite (ax_add_rec (σ y) x''). fapply ax_refl.
    - fassert ax_cases as "C"; first ctx.
      fdestruct ("C" x) as "[Hx'|[x' Hx']]".
      + fapply ax_succ_inj. frewrite <-"H".
        frewrite "Hx'". frewrite (ax_add_zero y).
        frewrite (ax_add_zero (σ y)). fapply ax_refl.
      + frewrite "Hx'". frewrite (ax_add_rec y x').
        fapply ax_succ_congr. 
        specialize (IHt x'). fapply IHt.
        fapply ax_succ_inj. frewrite <-(ax_add_rec (σ y) x').
        frewrite <-"Hx'". ctx.
  Qed.

  Lemma pless_sigma_neq t x : Qeq ⊢ (x ⧀= σ(num t)) ~> ¬(x == σ(num t)) ~> x ⧀= num t.
  Proof. 
    rewrite !pless_eq. 
    fstart. fintros. fdestruct "H". custom_simpl.
    fassert (ax_cases); first ctx.
    fdestruct ("H1" x0).
    - fexfalso. fapply "H0". 
      pose proof (add_zero_swap (S t) x). cbn in H.
      fapply H. frewrite <- "H1". fapply ax_sym.
      ctx.
    - fdestruct "H1". fexists x1. custom_simpl.
      fapply ax_sym. fapply add_rec_swap.
      frewrite <-"H1". fapply ax_sym. fapply "H".
  Qed. 
  Lemma pless_swap_sigma_neq t x : Qeq ⊢ (x ⧀=comm σ(num t)) ~> ¬(x == σ(num t)) ~> x ⧀=comm num t.
  Proof. 
    fstart. fintros. 
    rewrite !pless_swap_eq. rewrite !num_subst.
    fdestruct "H" as "[z Hz]".
    fassert ax_cases as "C"; first ctx.
    fdestruct ("C" z) as "[Hz'|[z' Hz']]".
    - fexfalso. fapply "H0". frewrite "Hz". frewrite "Hz'".
      fapply ax_sym. fapply ax_add_zero.
    - fexists z'. fapply ax_succ_inj.
      frewrite <-(ax_add_rec x z').
      frewrite <-"Hz'". ctx.
  Qed. 

  Lemma add_rec_swap2 t x y :
    Qeq ⊢ x ⊕ y == num t ~> x ⊕ (σ y) == num (S t).
  Proof.
    induction t in x |-*; fstart; fintros "H".
    - fassert ax_cases as "C"; first ctx. 
      fdestruct ("C" x) as "[Hx'|[x' Hx']]".
      + frewrite <-"H". frewrite "Hx'". 
        frewrite (ax_add_zero (σ y)). frewrite (ax_add_zero y).
        fapply ax_refl.
      + fexfalso. fapply (ax_zero_succ (x' ⊕ y)). frewrite <-"H".
        frewrite "Hx'". frewrite (ax_add_rec y x'). fapply ax_refl.
    - fassert ax_cases as "C"; first ctx. 
      fdestruct ("C" x) as "[Hx'|[x' Hx']]".
      + frewrite <-"H". frewrite "Hx'".
        frewrite (ax_add_zero (σ y)). frewrite (ax_add_zero y).
        fapply ax_refl.
      + frewrite "Hx'". frewrite (ax_add_rec (σ y) x').
        fapply ax_succ_congr.
        fapply IHt. fapply ax_succ_inj.
        frewrite <-(ax_add_rec y x'). frewrite <-"Hx'".
        fapply "H".
  Qed.

  Lemma pless_succ t x : Qeq ⊢ (x ⧀= num t) ~> (x ⧀= σ (num t)).
  Proof. 
    rewrite !pless_eq, !num_subst.
    fstart. fintros "[z Hz]". fexists (σ z).
    fapply ax_sym. fapply add_rec_swap2. fapply ax_sym. fapply "Hz".
  Qed.
  Lemma pless_swap_succ t x : Qeq ⊢ (x ⧀=comm num t) ~> (x ⧀=comm σ (num t)).
  Proof. 
    rewrite !pless_swap_eq, !num_subst.
    fstart. fintros "[z Hz]". fexists (σ z).
    frewrite (ax_add_rec x z). fapply ax_succ_congr. ctx.
  Qed.

  Lemma add_zero_num t :
    Qeq ⊢ num t ⊕ zero == num t.
  Proof.
    induction t.
    - cbn. frewrite (ax_add_zero zero). fapply ax_refl.
    - cbn. frewrite (ax_add_rec zero (num t)).
      fapply ax_succ_congr. apply IHt.
  Qed.
  Lemma pless_num_eq t x :
    Qeq ⊢ x == num t ~> x ⧀= num t.
  Proof.
    rewrite pless_eq. rewrite num_subst.
    fstart. fintros "H". fexists zero.
    frewrite "H". fapply ax_sym. fapply add_zero_num.
  Qed.
  Lemma pless_swap_num_eq t x :
    Qeq ⊢ x == num t ~> x ⧀=comm num t.
  Proof.
    rewrite pless_swap_eq. rewrite num_subst.
    fstart. fintros "H". fexists zero.
    frewrite (ax_add_zero x). fapply ax_sym. fapply "H".
  Qed.

  Fixpoint fin_disj n φ := match n with
                           | 0 => φ[(num 0) ..]
                           | S n => (fin_disj n φ) ∨ φ[(num (S n)) ..]
                           end.
  Fixpoint fin_conj n φ := match n with
                           | 0 => φ[(num 0) ..]
                           | S n => (fin_conj n φ) ∧ φ[(num (S n)) ..]
                           end.



  Lemma le_fin_disj t x :
    Qeq ⊢ x ⧀= num t <~> fin_disj t (x`[↑] == $0).
  Proof.
    induction t; cbn; rewrite subst_term_shift; fstart; fsplit.
    - fapply pless_zero_eq.
    - rewrite pless_eq. fintros "H".
      frewrite "H". fexists zero.
      frewrite (ax_add_zero zero). fapply ax_refl.
    - fintros "H". fassert (x == σ num t ∨ (¬ x == σ num t)) as "H1".
      { pose proof (Q_eqdec (S t) x). cbn in H. fapply H. }
      fdestruct "H1" as "[H1|H1]".
      + fright. ctx.
      + fleft. fapply IHt. 
        fapply pless_sigma_neq; ctx.
    - fintros "H". fdestruct "H" as "[H|H]".
      + fapply pless_succ. fapply IHt. fapply "H".
      + pose proof (pless_num_eq (S t) x). cbn in H.
        fapply H. fapply "H".
  Qed.
  Lemma le_swap_fin_disj t x :
    Qeq ⊢ x ⧀=comm num t <~> fin_disj t (x`[↑] == $0).
  Proof.
    induction t; cbn; rewrite subst_term_shift; fstart; fsplit.
    - fapply pless_swap_zero_eq.
    - rewrite pless_swap_eq.  fintros "H". frewrite "H".
      fexists zero. frewrite (ax_add_zero zero). fapply ax_refl.
    - fintros "H". fassert (x == σ num t ∨ (¬ x == σ num t)) as "H1".
      { pose proof (Q_eqdec (S t) x). cbn in H. fapply H. }
      fdestruct "H1" as "[H1|H1]".
      + fright. ctx.
      + fleft. fapply IHt. 
        fapply pless_swap_sigma_neq; ctx.
    - fintros "H". fdestruct "H" as "[H|H]".
      + fapply pless_swap_succ. fapply IHt. fapply "H".
      + pose proof (pless_swap_num_eq (S t) x). cbn in H.
        fapply H. fapply "H".
  Qed.

  Lemma Q_leibniz_t a x y : Qeq ⊢ x == y ~> a`[x..] == a`[y..].
  Proof.
    induction a.
    - destruct x0; cbn.
      + fintros. ctx.
      + fintros. fapply ax_refl.
    - destruct F.
      + cbn in v. rewrite (vec_0_nil v).
        fintros. fapply ax_refl.
      + cbn in v. 
        destruct (vec_1_inv v) as [z ->]. cbn.
        fintros. fapply (ax_succ_congr z`[y..] z`[x..]).
        frevert 0. fapply IH. apply Vector.In_cons_hd.
      + destruct (vec_2_inv v) as (a & b & ->).
        cbn. fintros. fapply ax_add_congr.
        all: frevert 0; fapply IH.
        * apply Vector.In_cons_hd.
        * apply Vector.In_cons_tl, Vector.In_cons_hd.
      + destruct (vec_2_inv v) as (a & b & ->).
        cbn. fintros. fapply ax_mult_congr.
        all: frevert 0; fapply IH.
        * apply Vector.In_cons_hd.
        * apply Vector.In_cons_tl, Vector.In_cons_hd.
  Qed.

  Lemma subst_up φ t1 t2 :
    φ[up t1..][t2..] = φ[t2`[↑]..][t1..].
  Proof.
    rewrite !subst_comp. apply subst_ext. intros [|[|n]]; cbn.
    + now rewrite subst_term_shift.
    + now rewrite subst_term_shift.
    + reflexivity.
  Qed.

  Lemma Q_leibniz φ x y : 
    Qeq ⊢ x == y ~> φ[x..] ~> φ[y..].
  Proof. 
    enough (Qeq ⊢ x == y ~> φ[x..] <~> φ[y..]).
    { fintros. fapply H; ctx. }
    induction φ using form_ind_subst.
    - cbn. fintros. fsplit; fintros; ctx. 
    - destruct P0. cbn in t. 
      destruct (vec_2_inv t) as (a & b & ->).
      cbn. fstart. fintros.
      fassert (a`[x..] == a`[y..]).
      { pose proof (Q_leibniz_t a x y).
        fapply H. fapply "H". }
      fassert (b`[x..] == b`[y..]).
      { pose proof (Q_leibniz_t b x y).
        fapply H. fapply "H". }
      frewrite "H0". frewrite "H1".
      fsplit; fintros; ctx.
    - fstart; fintros.
      fassert (φ1[x..] <~> φ1[y..]) by (fapply IHφ1; fapply "H").
      fassert (φ2[x..] <~> φ2[y..]) by (fapply IHφ2; fapply "H").
      destruct b0; fsplit; cbn.
      + fintros "[H2 H3]". fsplit.
        * fapply "H0". ctx.
        * fapply "H1". ctx.
      + fintros "[H2 H3]". fsplit.
        * fapply "H0". ctx.
        * fapply "H1". ctx.
      + fintros "[H2|H3]".
        * fleft. fapply "H0". ctx.
        * fright. fapply "H1". ctx.
      + fintros "[H2|H3]".
        * fleft. fapply "H0". ctx.
        * fright. fapply "H1". ctx.
      + fintros "H2" "H3". 
        fapply "H1". fapply "H2". fapply "H0". ctx.
      + fintros "H2" "H3". 
        fapply "H1". fapply "H2". fapply "H0". ctx.
    - fstart. fintros. fsplit; destruct q; cbn; fintros.
      + specialize (H (x0`[↑]..)). rewrite subst_up. fapply H.
        * ctx.
        * fspecialize ("H0" x0). rewrite subst_up. ctx.
      + fdestruct "H0". fexists x0. rewrite !subst_up.
        specialize (H (x0`[↑]..)). fapply H; ctx.
      + specialize (H (x0`[↑]..)). rewrite subst_up. fapply H.
        * ctx.
        * fspecialize ("H0" x0). rewrite subst_up. ctx.
      + fdestruct "H0". fexists x0. rewrite !subst_up.
        specialize (H (x0`[↑]..)). fapply H; ctx.
  Qed.

  (* Could probably be generalised to arbitrary finite disjunctions *)
  Lemma forall_fin_disj_conj φ t :
    Qeq ⊢ (∀ (fin_disj t ($1 == $0)) ~> φ) <~> fin_conj t φ.
  Proof.
    induction t as [|t IH]; cbn; fstart; fsplit.
    - fintros "H". fapply "H". fapply ax_refl.
    - fintros "H" x "H1". 
      feapply Q_leibniz.
      + feapply ax_sym. fapply "H1".
      + ctx.
    - fintros "H". fsplit.
      + fapply IH. fintros x "H1". fapply "H". fleft. fapply "H1".
      + fapply "H". fright. rewrite num_subst. fapply ax_refl.
    - fintros "[H1 H2]" x "[H3|H3]".
      + fdestruct IH as "[H4 H5]".
        fapply "H5"; ctx.
      + feapply Q_leibniz.
        * feapply ax_sym. fapply "H3".
        * fapply "H2".
  Qed.

  Lemma exists_fin_disj φ t :
    Qeq ⊢ (∃ (fin_disj t ($1 == $0)) ∧ φ) <~> fin_disj t φ.
  Proof.
    induction t as [|t IH]; cbn; fstart; fsplit.
    - fintros "[x [H1 H2]]". feapply Q_leibniz.
      + fapply "H1".
      + ctx.
    - fintros "H". fexists zero. fsplit.
      + fapply ax_refl.
      + ctx.
    - fintros "[x [[H1|H1] H2]]".
      + fleft. fapply IH. fexists x. fsplit.
        * fapply "H1".
        * fapply "H2".
      + fright. feapply Q_leibniz.
        * fapply "H1".
        * ctx.
    - fintros "[H1|H1]".
      + fapply IH in "H1". fdestruct "H1" as "[x [H1 H2]]".
        fexists x. fsplit.
        * fleft. ctx.
        * ctx.
      + fexists (σ num t). fsplit.
        * fright. fapply ax_refl.
        * ctx.
  Qed.


  Lemma Qdec_fin_conj φ t :
    Qdec φ -> Qdec (fin_conj t φ).
  Proof.
    intros Hφ. induction t; cbn.
    - apply Qdec_subst, Hφ.
    - apply Qdec_and.
      + assumption.
      + apply Qdec_subst, Hφ.
  Qed.

  Lemma Qdec_fin_disj φ t :
    Qdec φ -> Qdec (fin_disj t φ).
  Proof.
    intros Hφ. induction t; cbn.
    - apply Qdec_subst, Hφ.
    - apply Qdec_or.
      + assumption.
      + apply Qdec_subst, Hφ.
  Qed.

  Lemma forall_bound_iff φ ψ χ:
    Qeq ⊢ φ <~> ψ -> Qeq ⊢ (∀ φ ~> χ) <~> (∀ ψ ~> χ).
  Proof.
    intros H. fstart. fsplit.
    - fintros "H1" x "H2". fapply "H1". 
      apply (subst_Weak x..) in H. change (List.map _ _) with Qeq in H. 
      cbn in H. fapply H. fapply "H2".
    - fintros "H1" x "H2". fapply "H1". 
      apply (subst_Weak x..) in H. change (List.map _ _) with Qeq in H. 
      cbn in H. fapply H. fapply "H2".
  Qed.


  Lemma bounded_t_0 t ρ :
    bounded_t 0 t -> t`[ρ] = t.
  Proof.
    intros Hb. rewrite <-subst_term_var.
    eapply bounded_subst_t; last eassumption.
    lia.
  Qed.
  Lemma subst_up2 φ t ρ : bounded_t 0 t -> φ[t..][ρ] = φ[up ρ][t..].
  Proof.
    intros Hb. rewrite !subst_comp. apply subst_ext.
    intros [|n]; cbn; unfold "↑";cbn.
    - now apply bounded_t_0. 
    - rewrite !subst_term_comp. rewrite <-subst_term_var at 1.
      apply subst_term_ext. intros [|n']; reflexivity.
  Qed.

  Lemma fin_disj_subst n φ ρ :
    (fin_disj n φ)[ρ] = fin_disj n φ[up ρ].
  Proof.
    induction n; cbn.
    - apply subst_up2. solve_bounds.
    - cbn. f_equal; first assumption.
      apply subst_up2. solve_bounds. apply num_bound.
  Qed.


  Lemma AllI_named (A : list form) (phi : form) :
    (forall t, A ⊢ phi[t..]) ->
    A ⊢ ∀phi.
  Proof.
    intros H. apply AllI. 
    destruct (nameless_equiv_all A phi) as [t Ht].
    apply Ht, H.
  Qed.
  (* NOTE: this lemma could be strengthened to allow arbitrary terms t`[↑] in
   * place of $(S t). Unfortunately this broke the proofmode for some reason. *)
  Theorem Qdec_bounded_forall t φ :
    Qdec φ -> Qdec (∀ $0 ⧀= t`[↑] ~> φ).
  Proof.
    intros H ρ Hρ.
    destruct (@closed_term_is_num _ t`[ρ]) as [x Hx].
    { destruct (find_bounded_t t) as [k Hk].
      eapply subst_bound_t; last eassumption. auto. }
    enough (Qeq ⊢ (∀ (fin_disj x ($1 == $0))  ~> φ)[ρ] \/ Qeq ⊢ ¬ (∀ (fin_disj x ($1 == $0)) ~> φ)[ρ]) as H'.
    { cbn. rewrite pless_subst. cbn.
      cbn in H'. rewrite fin_disj_subst in H'. 
      cbn in H'. unfold "↑" in H'.
      destruct H' as [H1|H1].
      - left. fstart. fintros. fapply H1. 
        rewrite fin_disj_subst. cbn.
        fapply le_fin_disj. rewrite !pless_eq. 
        fdestruct "H" as "[z H]". fexists z.
        fassert (t`[ρ] == num x); first fapply Hx.
        frewrite <-"H0". fapply "H".
      - right.  fstart. fintros. fapply H1. fstop.
        fintros. fstart.
        fapply "H".
        rewrite fin_disj_subst. cbn.
        rewrite pless_subst. cbn.
        fassert (x0 ⧀= num x).
        { fapply le_fin_disj. fapply "H0". }
        rewrite !pless_eq. fdestruct "H1" as "[z Hz]".
        fexists z. 
        fassert (t`[ρ] == num x); first fapply Hx.
        frewrite "H1". fapply "Hz". }
    eapply Qdec_iff.
    - apply frewrite_equiv_switch. apply forall_fin_disj_conj.
    - apply Qdec_fin_conj, H.
    - apply Hρ.
  Qed.
  Theorem Qdec_bounded_exists t φ :
    Qdec φ -> Qdec (∃ ($0 ⧀= t`[↑]) ∧ φ).
  Proof.
    intros H ρ Hρ.
    destruct (@closed_term_is_num _ t`[ρ]) as [x Hx].
    { destruct (find_bounded_t t) as [k Hk].
      eapply subst_bound_t; last eassumption. auto. }
    enough (Qeq ⊢ (∃ (fin_disj x ($1 == $0)) ∧ φ)[ρ] \/ Qeq ⊢ ¬ (∃ (fin_disj x ($1 == $0)) ∧ φ)[ρ]) as H'.
    { cbn. rewrite pless_subst. cbn.
      cbn in H'. rewrite fin_disj_subst in H'. 
      cbn in H'. unfold "↑" in H'.
      destruct H' as [H1|H1].
      - left. fstart. 
        fassert (∃ fin_disj x ($1 == $0) ∧ φ[up ρ]).
        { fapply H1. }
        fdestruct "H" as "[z [H1 H2]]".
        rewrite fin_disj_subst. cbn.
        fexists z. fsplit; last ctx.
        fassert (z ⧀= num x).
        { fapply le_fin_disj. fapply "H1". }
        rewrite !pless_eq. fdestruct "H". fexists x0.
        frewrite Hx. fapply "H".
      - right.  fstart. fintros. fapply H1.
        fdestruct "H" as "[z [H1 H2]]". fexists z. 
        (* why does the proofmode stop here? *)
        fstart. fsplit; last ctx.
        rewrite fin_disj_subst. cbn. fapply le_fin_disj.
        rewrite !pless_eq. fdestruct "H". fexists x0.
        fassert (t`[ρ] == num x) by fapply Hx.
        frewrite <-"H1". fapply "H". }
    eapply Qdec_iff.
    - apply frewrite_equiv_switch. apply exists_fin_disj.
    - apply Qdec_fin_disj, H.
    - apply Hρ.
  Qed.
  Theorem Qdec_bounded_exists_comm t φ :
    Qdec φ -> Qdec (∃ ($0 ⧀=comm t`[↑]) ∧ φ).
  Proof.
    intros H ρ Hρ.
    destruct (@closed_term_is_num _ t`[ρ]) as [x Hx].
    { destruct (find_bounded_t t) as [k Hk].
      eapply subst_bound_t; last eassumption. auto. }
    enough (Qeq ⊢ (∃ (fin_disj x ($1 == $0)) ∧ φ)[ρ] \/ Qeq ⊢ ¬ (∃ (fin_disj x ($1 == $0)) ∧ φ)[ρ]) as H'.
    { cbn. rewrite pless_swap_subst. cbn.
      cbn in H'. rewrite fin_disj_subst in H'. 
      cbn in H'. unfold "↑" in H'.
      destruct H' as [H1|H1].
      - left. fstart. 
        fassert (∃ fin_disj x ($1 == $0) ∧ φ[up ρ]) by apply H1.
        fdestruct "H" as "[z [H1 H2]]".
        rewrite fin_disj_subst. cbn.
        fexists z. fsplit; last ctx.
        fassert (z ⧀=comm num x).
        { fapply le_swap_fin_disj. fapply "H1". }
        rewrite !pless_swap_eq. fdestruct "H". fexists x0.
        frewrite Hx. fapply "H".
      - right.  fstart. fintros. fapply H1.
        fdestruct "H" as "[z [H1 H2]]". fexists z. 
        (* why does the proofmode stop here? *)
        fsplit; last ctx.
        rewrite fin_disj_subst. cbn. fapply le_swap_fin_disj.
        rewrite !pless_swap_eq. cbn. fdestruct "H1". fexists x0.
        fassert (t`[ρ] == num x) by fapply Hx.
        frewrite <-"H0". fapply "H". }
    eapply Qdec_iff.
    - apply frewrite_equiv_switch. apply exists_fin_disj.
    - apply Qdec_fin_disj, H.
    - apply Hρ.
  Qed.
End Qdec.
