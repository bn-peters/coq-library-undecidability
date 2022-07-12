From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.

From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts Axiomatisations FA_facts Syntax.
From Undecidability.FOL Require Import PA.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode Hoas.
From Undecidability.FOL.Incompleteness Require Import formal_systems abstract_incompleteness fol qdec sigma1 weak_strong bin_qdec utils epf epf_mu fol_incompleteness.

From Undecidability.H10 Require Import DPRM dio_single.

Require Import String List.
Import ListNotations.

Section ctq.
  Context {p : peirce}.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.
  (* TODO More general formulation *)
  (* TODO deduce more general formulation from the weaker one? *)
  Definition CTQ := 
    forall (f : nat -\ nat), exists φ, bounded 2 φ /\ Σ1 φ /\ (forall x y, f x ▷ y <-> Qeq ⊢ ∀ φ[num x .: $0 ..] <~> $0 == num y).

  Definition CTQ_total := 
    forall (f : nat -> nat), exists φ, bounded 2 φ /\ Σ1 φ /\ forall x, Qeq ⊢ ∀ φ[num x .: $0..] <~> $0 == num (f x).

  Lemma ctq_ctq_total : CTQ -> CTQ_total.
  Proof.
    intros ctq f. destruct (ctq (partialise f)) as (φ & Hb & HΣ & Hφ).
    exists φ. do 2 (split; first assumption). 
    intros x. apply Hφ. exists 0. reflexivity.
  Qed.
End ctq.


Section ctq_epf.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.
  Existing Instance intu.

  Search (enumerable__T PA_preds).

  Lemma Q_num_inj x y : Qeq ⊢ num x == num y -> x = y.
  Proof. 
    intros H%soundness.
    specialize (H _ interp_nat (fun _ => 0) (nat_is_Q_model _)). cbn in H.
    (* TODO refactor/deduplicate *)
    assert (forall x, iμ x = x) as Hi. { induction x0; cbn; congruence. }
    now rewrite !eval_num, !Hi in H.
  Qed.

  Lemma prv_enumerable (T : list form) (p' : peirce) :
    enumerable (fun phi => T ⊢ phi).
  Proof.
    edestruct (@tprv_enumerable PA_funcs_signature PA_preds_signature) with (T := list_theory T) as [f Hf].
    - apply enumerable_PA_funcs.
    - exact _.
    - apply enumerable_PA_preds.
    - exact _.
    - apply list_theory_enumerable.
    - exists f. intros phi. unfold enumerator in Hf.
      rewrite <-Hf. split.
      + intros H. exists T. eauto.
      + intros [T' HT']. apply Weak with (A := T'); firstorder.
  Qed.

  Lemma ctq_epfn : CTQ -> EPF_N.
  Proof.
    unshelve edestruct (@form_enumerable PA_funcs_signature PA_preds_signature enumerable_PA_funcs enumerable_PA_preds) as [f_form Hform].
    assert (semi_decidable (fun ψ => Qeq ⊢I ψ)) as [f_prv Hprv].
    { apply enumerable_semi_decidable.
      - apply form_discrete.
      - apply prv_enumerable. }

    intros ctq.
    unshelve eexists.
    { intros c. 
      intros x. unshelve eexists.
      { intros k. 
        destruct (f_form c) as [φ|]. 2: exact None.
        destruct (unembed k) as [l y].
        destruct (f_prv (∀ φ[num x .: $0 ..] <~> $0 == num y) l).
        - exact (Some y).
        - exact None. }
      intros y1 y2 k1 k2. destruct (f_form c) as [φ|] eqn:Hc; cbn.
      2: congruence. 
      destruct (unembed k1) as [l1 y'1].
      destruct (unembed k2) as [l2 y'2].
      destruct (f_prv _ l1) eqn:H1, (f_prv _ l2) eqn:H2.  2-4: congruence. intros [= <-] [= <-].
      assert (Qeq ⊢I ∀ φ[num x .: $0..] <~> $0 == num y'1) as H1'. 
      { apply Hprv. eauto. }
      assert (Qeq ⊢I ∀ φ[num x .: $0..] <~> $0 == num y'2) as H2'. 
      { apply Hprv. eauto. }
      enough (Qeq ⊢I num y'1 == num y'2).
      { apply Q_num_inj, H. }
      fspecialize (H2' (num y'1)). rewrite num_subst in H2'.
      fapply H2'.
      fspecialize (H1' (num y'1)). rewrite num_subst in H1'.
      fapply H1'. fapply ax_refl. }
    intros f. destruct (ctq f) as (φ & H1 & H2 & Hφ).
    destruct (Hform φ) as [c Hc]. exists c.
    intros x y. setoid_rewrite Hφ. cbn. split.
    - intros H. apply Hprv in H as [l Hl].
      exists (embed (l, y)). cbn.
      rewrite Hc. rewrite embedP. rewrite Hl.
      reflexivity.
    - intros [k H3]. cbn in H3.
      rewrite Hc in H3. destruct (unembed k) as [l y'].
      destruct f_prv eqn:H.
      + apply Hprv. exists l. now injection H3 as ->.
      + congruence.
  Qed.

End ctq_epf.

Section ctq_repr.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.

  (* Context {p : peirce}. *) 
  Existing Instance intu.

  (* TODO global formulation for weak repr in fol *)
  (* TODO precedence of .. *)
  Lemma ctq_weak_repr (ctq : CTQ_total) (P : nat -> Prop) :
    enumerable P -> exists φ,
    bounded 1 φ /\ Σ1 φ /\ forall x, P x <-> Qeq ⊢ φ[(num x)..].
  Proof.
    intros [f Hf].
    pose (f' := fun x => match f x with Some y => S y | None => 0 end).
    destruct (ctq f') as (φ & Hb & HΣ & Hφ).
    exists (∃(φ[$0 .: (σ $1) ..])).
    repeat apply conj.
    { constructor. eapply subst_bound; last eassumption.
      intros [|[|n]] ?; repeat solve_bounds. }
    { constructor. apply Σ1_subst, HΣ. }
    intros x. unfold enumerator in Hf. setoid_rewrite Hf.
    split.
    - intros [k Hk]. cbn. 
      fexists (num k). 
      specialize (Hφ k). fspecialize (Hφ (num (f' k))).
      rewrite num_subst in Hφ.
      replace (φ[_][_][_]) with (φ[num k .: $0 ..][(num (f' k))..]).
      { fapply Hφ. fapply ax_refl. }
      rewrite !subst_comp. eapply bounded_subst; first eassumption.
      intros [|[|n]] ?; cbn; rewrite ?num_subst.
      + reflexivity.
      + unfold f'. rewrite Hk. reflexivity.
      + lia.
    - cbn. intros [k Hk]%Σ1_witness. 
      2: { apply Σ1_subst, Σ1_subst, HΣ. }
      2: { rewrite subst_comp. eapply subst_bound; last eassumption.
        intros [|[|n]] ?; cbn.
        - constructor. lia.
        - repeat (solve_bounds; rewrite ?num_subst); apply num_bound. 
        - lia. }
      exists k.
      enough (f' k = S x) as H.
      { unfold f' in H. now destruct (f k). }
      apply Q_num_inj. 
      specialize (Hφ k). fspecialize (Hφ (num (S x))). 
      rewrite num_subst in Hφ. 
      fapply ax_sym. fapply Hφ.
      replace (φ[_][_][_]) with (φ[num k .: $0 ..][(σ num x)..]) in Hk; first easy.
      rewrite !subst_comp. eapply bounded_subst; first eassumption.
      intros [|[|n]] ?; cbn; rewrite ?num_subst; easy + lia.
  Qed.

  (* TODO really discuss semi decidability, enumerability with Dominik *)
  Lemma ctq_strong_sepr (ctq : CTQ) (P Q : nat -> Prop) :
    (forall x, P x -> Q x -> False) ->
    semi_decidable P -> semi_decidable Q ->
    exists φ, bounded 1 φ /\ Σ1 φ /\ 
      (forall x, P x -> Qeq ⊢ φ[(num x)..]) /\ 
      (forall x, Q x -> Qeq ⊢ ¬φ[(num x)..]).
  Proof.
    intros Hdisj HP HQ.
    destruct (enumerable_separable Hdisj HP HQ) as [f Hf].
    destruct (ctq (fun x => comp_part_total (fun b : bool => if b then 1 else 0) (f x))) as (φ & Hb & HΣ & Hφ).
    exists (φ[$0 .: (num 1) ..]). repeat split.
    { eapply subst_bound; last eassumption.
      intros [|[|n]] ?; cbn; repeat solve_bounds. }
    { apply Σ1_subst, HΣ. }
    - intros x Hx%Hf. 
      assert (comp_part_total (fun b : bool => if b then 1 else 0) (f x) ▷ 1) as H%Hφ.
      { destruct Hx as [k Hk]. exists k. cbn. now rewrite Hk. }
      fspecialize (H (num 1)).
      replace (φ[_][_]) with (φ[num x .: $0..][(num 1)..]).
      { fapply H. fapply ax_refl. }
      rewrite !subst_comp. eapply bounded_subst; first eassumption.
      intros [|[|n]]?; cbn; rewrite ?num_subst; easy + lia.
    - intros x Hx%Hf. 
      assert (comp_part_total (fun b : bool => if b then 1 else 0) (f x) ▷ 0) as H%Hφ.
      { destruct Hx as [k Hk]. exists k. cbn. now rewrite Hk. }
      fspecialize (H (num 1)).
      replace (φ[_][_]) with (φ[num x .: $0..][(num 1)..]).
      { fstart. fintros "H". fapply H in "H". 
        (* For some reason, these assumption cause fapply to take a long time *)
        clear H Hx x Hφ HΣ Hb φ Hf f HQ HP Hdisj P Q ctq.
        fapply (ax_zero_succ zero). fapply ax_sym.
        ctx. }
      rewrite !subst_comp. eapply bounded_subst; first eassumption.
      intros [|[|n]]?; cbn; rewrite ?num_subst; easy + lia.
  Qed.

End ctq_repr.

Section ctq.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.

  Existing Instance intu.

  Print EPF_N.
  Variable theta : nat -> nat -\ nat.
  Variable theta_universal : is_universal theta.

  Variable (φ : nat -> form).
  Hypothesis φ1_qdec : forall c, Qdec (φ c).
  Hypothesis φ1_bounded : forall c, bounded 3 (φ c).
  Hypothesis wrepr : forall c x y, theta c x ▷ y <-> Qeq ⊢ ∃ (φ c)[$0 .: num x .: (num y)..].

  Local Definition ψ : nat -> form := fun c =>
    ∃ (φ c)[$0.:$1.:$2..] ∧ ∀∀ ($1 ⊕ $0 ⧀= $4 ⊕ $2) ~> (φ c)[$0.:$3.:$1..] ~> $1 == $4.

  Lemma ψ_bounded c : bounded 2 (ψ c).
  Proof.
    repeat solve_bounds.
    - eapply subst_bound; last auto.
      intros [|[|[|k]]]; solve_bounds.
    - rewrite pless_eq. cbn. unfold "↑". repeat solve_bounds.
    - eapply subst_bound; last auto.
      intros [|[|[|k]]]; solve_bounds.
  Qed.
  Lemma ψ_Σ1 c : Σ1 (ψ c).
  Proof.
    constructor. constructor.
    apply Qdec_and.
    - now apply Qdec_subst.
    - apply (Qdec_bin_bounded_forall ($2 ⊕ $0)).
      apply Qdec_impl.
      + now apply Qdec_subst. 
      + apply Qdec_eq.
  Qed.
  Lemma sdjfkl c x y : (ψ c)[x.:y..] = 
    ∃ (φ c)[$0 .: x`[↑] .: y`[↑]..] ∧ ∀∀ ($1 ⊕ $0 ⧀= y`[↑]`[↑]`[↑] ⊕ $2) ~> (φ c)[$0 .: x`[↑]`[↑]`[↑] .: $1..] ~> $1 == y`[↑]`[↑]`[↑].
  Proof.
    cbn. do 2 f_equal.
    { rewrite subst_comp. 
      eapply bounded_subst; first auto.
      intros [|[|[|n]]]; cbn; solve_bounds. }
    do 4 f_equal.
    rewrite subst_comp. 
    eapply bounded_subst; first auto.
    intros [|[|[|n]]]; cbn; solve_bounds.
  Qed.


  Check nameless_equiv_ex.
  Lemma ExE_named A χ ψ :
    A ⊢ ∃ χ -> (forall t, (χ[t..]::A) ⊢ ψ) -> A ⊢ ψ.
  Proof.
    intros H1 H2. destruct (nameless_equiv_ex A χ ψ) as [t Ht].
    eapply ExE.
    - eassumption.
    - apply Ht, H2.
  Qed.

  Lemma epf_n_ctq : CTQ.
  Proof.
    intros f. destruct (theta_universal f) as [c Hc]. exists (ψ c).
    split; first apply ψ_bounded.
    split; first apply ψ_Σ1.
    intros x y. rewrite sdjfkl.
    split; first (intros Hf; apply AllI_named; intros y'; cbn; apply CI).
    - fstart. fintros "[k [H1 H2]]". 
      clear wrepr. cbn.
      fspecialize ("H2" y').
      the interesting case
      admit. (* Proofmode fucky *)
    - assert (exists k, Qeq ⊢ (φ c)[num k .: num x .: (num y) ..]).
      { Check Σ1_witness.
      admit.
    - intros H. apply Hc, wrepr.
      fspecialize (H (num y)). fdestruct H.

      intros [k Hk]%Hc%wrepr%Σ1_witness. 
      2: { apply Σ1_subst. now constructor. }
      2: { admit. (* boundedness *) }
      cbn. rewrite pless_subst. cbn. unfold "↑". 
      fstart. fintros y'. fsplit.
      + fintros "[k' [H1 H2]]".
        admit. (* the only interesting case *)
      + fintros "H". fexists (num k). fsplit.
        * fstop.
          replace φ[_][_][_][_] with φ[num k .: (num x) .: $0 ..][y'..].
          2: { rewrite !subst_comp. eapply bounded_subst; first eassumption.
            intros [|[|[|l]]] H; cbn; now rewrite ?num_subst, ?subst_term_shift + lia. }
          feapply Q_leibniz.
          -- clear Hk Hφ wrepr. feapply ax_sym. ctx.
          -- admit. (* just replace substitutions *)
        * fassert (∀∀ $1 ⊕ $0 ⧀= num y ⊕ num k ~> φ[$0.:num x.:$1 ..] ~> $1 == num y); first last.
          { fintros y'' k' "H1". fintros "H2". clear Hk Hφ wrepr.
            (* Proof outline:
               - rewrite "H"
               - apply "H0" y'' k' H2. *) 
            admit. (* TODO: fight with proofmode *) }
          fstop. eapply (Weak Qeq); last easy.
          eapply Σ1_completeness.
          { admit. (* Sigma1 *) }
          { admit. (* boundedness *)}
          rewrite pless_eq. cbn.
          intros y'' k' _ H.
          rewrite nat_eval_num in *.
          eapply part_functional with (p := f x); apply Hc; apply Hφ.
          -- eapply Σ1_completeness.
             { admit. (* Sigma1 *)}
             { admit. (* boundedness *) }
             exists k'. 
             admit. (* Easy up to lemmas on satisfiability *)
          -- fexists (num k). assumption.
    - intros H. apply Hc, Hφ. cbn in H.
      fstart.
      fspecialize (H (num y)). rewrite !num_subst in H.
      (* easy, since H contains the assumption when instantiating with num y == num y *)
      admit.
  Admitted.
End ctq.
