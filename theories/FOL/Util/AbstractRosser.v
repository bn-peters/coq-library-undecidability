(** * Abstract Incompleteness using Rosser's Trick *)

From Undecidability.Synthetic Require Import Definitions Undecidability.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Synthetic Require Import ListEnumerabilityFacts MoreEnumerabilityFacts.
From Undecidability.Shared Require Import Dec embed_nat.
From Equations Require Import Equations.
Require Import ConstructiveEpsilon.
Require Import List.
Import ListNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.



Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition pi1 {A : Type} {P : A -> Type} (e : Sigma x, P x): A := let (x, _) := e in x.

Definition tenumerable X := exists (f : nat -> X), forall x, exists k, f k = x.
Definition senumerator {X} (f : nat -> X) P := forall x, P x <-> exists n, f n = x.
Definition senumerable {X} (P : X -> Prop) := exists f, senumerator f P.

Lemma senumerable_enumerable X (P : X -> Prop) : senumerable P -> enumerable P.
Proof.
  intros [f Hf]. exists (fun x => Some (f x)).
  intros x. split.
  - intros Hpx. apply Hf in Hpx.
    destruct Hpx as [n Hn]. exists n. congruence.
  - intros [k Hk].
    destruct (Hf x) as [H1 H2].
    apply H2. exists k. congruence.
Qed.
Lemma enumerable_senumerable X (P : X -> Prop) : (exists x, P x) -> enumerable P -> senumerable P.
Proof.
  intros [a Ha] [f Hf].
  exists (fix g n := match n with 0 => a | S n => match f n with None => g n | Some x => x end end).
  intros x. split.
  - intros Hpx. destruct (Hf x) as [H1 _].
    destruct (H1 Hpx) as [n Hn]. exists (S n). now rewrite Hn.
  - intros [n Hn]. induction n.
    + congruence.
    + destruct (f n) eqn:H.
      * apply Hf. exists n. congruence.
      * apply IHn, Hn.
Qed.


Definition mu (p : nat -> Prop) :
  (forall x, dec (p x)) -> ex p -> sig p.
Proof.
  apply constructive_indefinite_ground_description_nat_Acc.
Qed.

Definition ldecidable {X} (p : X -> Prop) :=
  forall x, p x \/ ~ p x.

Theorem weakPost X (p : X -> Prop) :
  discrete X -> ldecidable p -> enumerable p -> enumerable (fun x => ~ p x) -> decidable p.
Proof.
  intros [E] % discrete_iff Hl [f Hf] [g Hg].
  eapply decidable_iff. econstructor. intros x.
  assert (exists n, f n = Some x \/ g n = Some x) by (destruct (Hl x); firstorder).
  destruct (@mu (fun n => f n = Some x \/ g n = Some x)) as [n HN]; trivial.
  - intros n. exact _.
  - decide (f n = Some x); decide (g n = Some x); firstorder.
Qed.
Theorem sWeakPost X (p : X -> Prop) :
  discrete X -> ldecidable p -> senumerable p -> senumerable (fun x => ~ p x) -> decidable p.
Proof.
  intros Xdis Hl Henum Hnenum.
  apply weakPost; auto using senumerable_enumerable.
Qed.

Definition Post X (p : X -> Prop) := senumerable p -> senumerable (fun x => ~p x) -> decidable p.

Section s.
  Variable (T R : Type).
  Definition function := Sigma (f : T -> nat -> option R), forall x k k' y y',
        f x k = Some y -> f x k' = Some y' -> y = y'.

  Variable (f : function).

  Definition returns (x : T) (y : R) : Prop := exists k, pi1 f x k = Some y.
  Definition diverges (x : T) : Prop := forall k, pi1 f x k = None.
  Definition halts (x : T) : Prop := exists y, returns x y.

  Lemma returns_functional (x : T) (y1 y2 : R) : returns x y1 -> returns x y2 -> y1 = y2.
  Proof.
    intros (k & Hk) (k' & Hk').
    destruct f as [f' Hf].
    exact (Hf x k k' y1 y2 Hk Hk').
  Qed.
End s.

Arguments returns {T R}.
Arguments diverges {T R}.
Arguments halts {T R}.

Inductive out : Type := ACC | REJ.
Section s.
  Variable (T : Type) (f : function T out).

  Definition accepts (x : T) : Prop := returns f x ACC.
  Definition rejects (x : T) : Prop := returns f x REJ.

  Lemma accepts_rejects (x : T) : accepts x -> rejects x -> False.
  Proof.
    intros Ha Hr. enough (ACC = REJ) by discriminate. eapply returns_functional; eassumption.
  Qed.
End s.

Arguments accepts {T}.
Arguments rejects {T}.


Section Abstract.
  Variable sentences : Type.
  Variable neg : sentences -> sentences.
  Hypothesis sentences_discrete : forall (s1 s2 : sentences), (s1 = s2) + (s1 <> s2).
  Hypothesis sentences_enumerable : tenumerable sentences.


  (* Replacing this with an enumerable predicate makes things difficult
     because the enumerator must be computational (not under an exists) *)
  Variable (provable_enumerator : nat -> sentences).
  Definition provable s := exists k, provable_enumerator k = s.

  Hypothesis consistent : forall s, provable s -> provable (neg s) -> False.
  Arguments consistent s : clear implicits.
  Definition completeness := forall s, provable s \/ provable (neg s).

  Lemma neg_no_fixpoint : forall s, provable s -> s <> neg s.
  Proof.
    intros s Hs Heq. apply (consistent s); congruence.
  Qed.
  Lemma neg_no_fixpoint2 : forall s, provable (neg s) -> s <> neg s.
  Proof.
    intros s Hs Heq. apply (consistent s); congruence.
  Qed.

  Lemma undeepen_provability s : completeness -> ~provable s -> provable (neg s).
  Proof.
    intros complete Hnprov. now destruct (complete s).
  Qed.
  Lemma deepen_provability s : provable (neg s) -> ~provable s.
  Proof.
    intros Hprovn Hnprov. apply (consistent s); eassumption.
  Qed.

  Lemma ldecidable_provable : completeness -> ldecidable provable.
  Proof.
    intros complete s. destruct (complete s); intuition.
  Qed.


  Lemma provable_enumerable : senumerable provable.
  Proof.
    now exists provable_enumerator.
  Qed.
  Lemma provable_coenumerable : completeness -> senumerable (fun s => ~provable s).
  Proof.
    intros complete.
    destruct sentences_enumerable as [sentences_enumerator Hsent].
    apply enumerable_senumerable.
    { destruct (complete (sentences_enumerator 0)).
      - exists (neg (sentences_enumerator 0)). intros H1.
        now destruct (@consistent (sentences_enumerator 0)).
      - exists (sentences_enumerator 0). intros H1.
        now destruct (@consistent (sentences_enumerator 0)).
    }
    unshelve eexists.
    { intros [k1 k2] % unembed.
      destruct (sentences_discrete (provable_enumerator k1) (neg (sentences_enumerator k2))).
      - exact (Some (sentences_enumerator k2)).
      - exact None. }
    intros s. split.
    - intros [k1 Hk1] % undeepen_provability. 2: exact complete.
      destruct (Hsent s) as [k2 Hk2].
      exists (embed (k1, k2)). rewrite embedP. cbn.
      rewrite Hk1, Hk2. now destruct sentences_discrete.
    - intros [k Hk].
      destruct (unembed k) as [k1 k2]. cbn in Hk.
      destruct sentences_discrete as [Heq|?]. 2: discriminate.
      injection Hk as <-.
      apply deepen_provability. now exists k1.
  Defined.
  Lemma decidable_provable : completeness -> decidable provable.
  Proof.
    intros complete.
    apply sWeakPost.
    - unfold discrete, decidable, decider, reflects.
      exists (fun '(s1, s2) => if sentences_discrete s1 s2 then true else false).
      intros [s1 s2]. split; destruct sentences_discrete; auto.
    - apply ldecidable_provable, complete.
    - apply provable_enumerable.
    - apply provable_coenumerable, complete.
  Qed.

  Section representability_prop.
    Variable T : Type.
    Variable P : T -> Prop.

    Definition weakly_representable :=
      Sigma f, forall t, P t <-> provable (f t).
    Definition strongly_representable :=
      Sigma f, forall t, (P t -> provable (f t)) /\ (~provable (neg (f t)) -> P t).
    Definition strongly_representable_classic :=
      Sigma f, forall t, (P t -> provable (f t)) /\ (~P t -> provable (neg (f t))).

    Lemma strongly_weakly_representable : strongly_representable -> weakly_representable.
    Proof.
      intros [f Hf].
      exists f. intros t. split.
      - apply Hf.
      - intros Hprov. apply Hf.
        intros Hnprov. eapply consistent.
        + exact Hprov.
        + exact Hnprov.
    Qed.
    Lemma weakly_strongly_representable :
      completeness -> weakly_representable -> strongly_representable.
    Proof.
      intros complete [f Hf].
      exists f. intros t. split.
      - apply Hf.
      - intros Hnprov. apply Hf.
        destruct (complete (f t)).
        + assumption.
        + contradiction.
    Qed.
    Lemma weakly_strongly_representable_classic :
      completeness -> weakly_representable -> strongly_representable_classic.
    Proof.
      intros complete [f Hf]. exists f.
      intros t. split.
      - apply Hf.
      - intros Hnpt. destruct (complete (f t)).
        + firstorder.
        + assumption.
    Qed.


    Goal ldecidable provable -> strongly_representable -> strongly_representable_classic.
    Proof.
      intros ldec [f Hf]. exists f.
      intros t. split.
      - apply Hf.
      - intros Hnpt. destruct (ldec (neg (f t))).
        + assumption.
        + firstorder.
    Qed.
    Goal ldecidable P -> strongly_representable_classic -> strongly_representable.
    Proof.
      intros ldec [f Hf]. exists f.
      intros t. split.
      - apply Hf.
      - intros Hnprov. destruct (ldec t); firstorder.
    Qed.
  End representability_prop.
  Arguments weakly_representable {T}.
  Arguments strongly_representable {T}.
  Arguments strongly_representable_classic {T}.

  Section decidability_predicate.
    Variable (T : Type) (Tdis : forall (t1 t2 : T), (t1 = t2) + (t1 <> t2)) (Tenumerable : Sigma (f : nat -> T), forall t, exists n, f n = t).
    Variable (P : T -> Prop).
    Variable srepr : strongly_representable_classic P.

    (* TODO work on an abstract machine model using Church's Thesis *)
    (* TODO this as a Coq function using Posts Theorem *)
    Lemma srepr_fn : function T out.
    Proof.
      destruct srepr as [psent Hpsent].
      unshelve eexists.
      - intros t k.
        destruct (sentences_discrete (provable_enumerator k) (psent t)).
        + exact (Some ACC).
        + destruct (sentences_discrete (provable_enumerator k) (neg (psent t))).
          * exact (Some REJ).
          * exact None.
      - intros x k1 k2 y1 y2. cbn.
        repeat destruct sentences_discrete; try congruence.
        all: edestruct consistent.
        + exists k1. eassumption.
        + exists k2. congruence.
        + exists k2. eassumption.
        + exists k1. congruence.
    Defined.

    (* This has a flavour of strong representability *)
    Lemma srepr_fn_correct t : (P t -> accepts srepr_fn t) /\ (~P t -> rejects srepr_fn t).
    Proof.
      destruct srepr as [psent Hpsent] eqn:Hsrepr.
      split.
      - intros pt. unfold accepts, returns.
        assert (provable (psent t)) as [k Hk] by intuition.
        exists k. cbv. rewrite Hsrepr, Hk.
        destruct sentences_discrete; easy.
      - intros Hnpt. unfold rejects, returns.
        assert (provable (neg (psent t))) as [k Hk] by intuition.
        exists k. cbv. rewrite Hsrepr, Hk.
        destruct sentences_discrete as [Heq | ?].
        { destruct (@neg_no_fixpoint (psent t)).
          - exists k. congruence. 
          - easy. }
        destruct sentences_discrete; easy.
    Qed.

    Lemma srepr_fn_correct_iff (ldec : ldecidable P) t
      : (P t <-> accepts srepr_fn t) /\ (~P t <-> rejects srepr_fn t).
    Proof.
      split; split. 1, 3: now apply srepr_fn_correct.
      - destruct (ldec t) as [H|H]. 1: easy.
        apply srepr_fn_correct in H.
        intros H'.
        edestruct accepts_rejects; eassumption.
      - destruct (ldec t) as [H|H]. 2: easy.
        apply srepr_fn_correct in H.
        intros H'.
        edestruct accepts_rejects; eassumption.
    Qed.

    Lemma srepr_enumerable : (ldecidable P) -> enumerable P.
    Proof.
      intros Pldec.
      destruct srepr as [repr Hrepr], Tenumerable as [Tenum HTenum].
      unshelve eexists.
      { intros k. destruct (unembed k) as [k1 k2].
        destruct (sentences_discrete (repr (Tenum k1)) (provable_enumerator k2)).
        - exact (Some (Tenum k1)).
        - exact None. }
      intros t. split.
      - intros Hpt. apply Hrepr in Hpt.
        destruct (HTenum t) as [k1 Hk1].
        destruct (Hpt) as [k2 Hk2].
        exists (embed (k1, k2)). rewrite embedP. cbn.
        rewrite Hk1, Hk2. now destruct sentences_discrete.
      - intros [k Hk].
        destruct (unembed k) as [k1 k2]. cbn in Hk.
        destruct sentences_discrete as [Heq|Heq]. 2: discriminate.
        destruct (Pldec t) as [H|H]. 1: assumption.
        edestruct consistent.
        + exists k2. symmetry. exact Heq.
        + apply Hrepr. congruence.
    Qed.
    (* TODO it is possible to remove the completeness requirement here
        essentially by inlining the coenumerability proof only for the sentences
        that strongly represent *)
    Lemma srepr_coenumerable : completeness -> (ldecidable P) -> enumerable (fun t => ~P t).
    Proof.
      intros complete Pldec.
      destruct provable_coenumerable as [provable_coenumerator Hprov_coenum]. 1: assumption.
      destruct srepr as [repr Hrepr], Tenumerable as [Tenum HTenum].
      unshelve eexists.
      { intros k. destruct (unembed k) as [k1 k2].
        destruct (sentences_discrete (repr (Tenum k1)) (provable_coenumerator k2)).
        - exact (Some (Tenum k1)).
        - exact None.
      }
      intros t. split.
      - intros Hnpt. apply Hrepr in Hnpt.
        destruct (HTenum t) as [k1 Hk1].
        unfold enumerator in Hprov_coenum.
        destruct (Hprov_coenum (repr t)) as [[k2 Hk2] _].
        1: now apply deepen_provability.
        exists (embed (k1, k2)). rewrite embedP. cbn.
        rewrite Hk1, Hk2. now destruct sentences_discrete.
      - intros [k Hk].
        destruct (unembed k) as [k1 k2]. cbn in Hk.
        destruct sentences_discrete as [Heq|Heq]. 2: discriminate.
        destruct (Pldec t) as [H|H]. 2: assumption.
        destruct (@consistent (repr t)).
        + now apply Hrepr.
        + apply undeepen_provability. 1: assumption.
          apply Hprov_coenum.
          exists k2. congruence.
    Qed.



    (* TODO it feels like i can replace decidability with markovs principle here *)
    Lemma srepr_decidable : completeness -> (ldecidable P) -> decidable P.
    Proof.
      intros complete Pldec.
      apply weakPost.
      - unfold discrete, decidable, decider, reflects.
        exists (fun '(t1, t2) => if Tdis t1 t2 then true else false).
        intros [t1 t2]. split; destruct Tdis; intuition.
      - assumption.
      - now apply srepr_enumerable.
      - now apply srepr_coenumerable.
    Qed.
  End decidability_predicate.

  Section cg.
    Variable (T : Type) (t : T).
    (* NOTE: This is not consistent guessing anymore, the acceptance problem *)
    Definition cg_pred (g : function T out) : Prop := (accepts g t).
    (* TODO (why) does implication suffice here? In our old formulation it did as well*)
    (* NOTE This is some kind of representability on a meta-level? *)
    Hypothesis no_cg : ~exists f, forall g, (cg_pred g -> returns f g ACC) /\ (~cg_pred g -> returns f g REJ).

    Lemma cg_false : completeness -> weakly_representable cg_pred -> False.
    Proof.
      intros complete cg_repr % (weakly_strongly_representable_classic complete).
      apply no_cg.
      exists (srepr_fn cg_repr). apply srepr_fn_correct.
    Qed.
  End cg.

End Abstract.

Check srepr_fn_correct.
