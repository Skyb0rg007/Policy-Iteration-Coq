Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Unicode.Utf8.

Generalizable All Variables.

Reserved Notation "x ⊔ y" (at level 36, left associativity).
Reserved Notation "x ⊓ y" (at level 40, left associativity).
Reserved Notation "⊥" (at level 0).
Reserved Notation "⊤" (at level 0).

Definition equiv `{Equivalence A} := Equivalence.equiv.

Local Open Scope equiv_scope.

Class Lattice (A : Type) `{Equivalence A} : Type := {
  meet : A → A → A where "x ⊓ y" := (meet x y);
  join : A → A → A where "x ⊔ y" := (join x y);
  top : A;
  bot : A;

  (* These exact axioms are taken from the nlab page on lattices *)
  meet_commutative : ∀ a b, a ⊓ b === b ⊓ a;
  meet_idempotent : ∀ a, a ⊓ a === a;
  meet_associative : ∀ a b c, a ⊓ (b ⊓ c) === (a ⊓ b) ⊓ c;

  join_commutative : ∀ a b, a ⊔ b === b ⊔ a;
  join_idempotent : ∀ a, a ⊔ a === a;
  join_associative : ∀ a b c, a ⊔ (b ⊔ c) === (a ⊔ b) ⊔ c;

  join_meet_absorptive : ∀ a b, a ⊔ (a ⊓ b) === a;
  meet_join_absorptive : ∀ a b, a ⊓ (a ⊔ b) === a;

  meet_id : ∀ a, a ⊓ top === a;
  join_id : ∀ a, a ⊔ bot === a;

  (* Welcome to "Setoid-Hell" *)
  meet_respectful :> Proper (equiv ==> equiv ==> equiv) meet;
  join_respectful :> Proper (equiv ==> equiv ==> equiv) join;
}.

Notation "x ⊓ y" := (meet x y).
Notation "x ⊔ y" := (join x y).
Notation "⊤" := top.
Notation "⊥" := bot.

Module Lattice.
Section Lattice.

  Context {A : Type} {equ : A → A → Prop}.
  Context {E : Equivalence equ}.
  Context {L : Lattice A}.

  Definition le_meet a b := a ⊓ b === a.

  Instance Reflexive_le_meet : Reflexive le_meet := meet_idempotent.

  Instance Transitive_le_meet : Transitive le_meet.
  Proof.
    intros x y z P Q.
    unfold le_meet in *.
    rewrite <- P.
    rewrite <- Q.
    rewrite meet_associative.
    rewrite <- meet_associative.
    rewrite meet_idempotent.
    reflexivity.
  Qed.

  Instance PreOrder_le_meet : PreOrder le_meet := {|
    PreOrder_Reflexive := Reflexive_le_meet;
    PreOrder_Transitive := Transitive_le_meet;
  |}.

  Instance PartialOrder_le_meet : PartialOrder equ le_meet.
  Proof.
    intros x y.
    split; intros H.
    - split.
      + unfold le_meet.
        rewrite <- (meet_respectful x x (reflexivity x) x y H).
        apply meet_idempotent.
      + unfold le_meet, Basics.flip.
        rewrite (meet_respectful y y (reflexivity y) x y H).
        apply meet_idempotent.
    - destruct H as [H1 H2].
      unfold le_meet, Basics.flip in *.
      rewrite <- H1 in *.
      rewrite (meet_commutative x y) in H2.
      rewrite meet_associative in H2.
      rewrite meet_idempotent in H2.
      rewrite meet_commutative in H2.
      apply H2.
  Qed.

  Definition le_join a b := a ⊔ b === b.

  Lemma le_meet_join : ∀ a b, le_meet a b ↔ le_join a b.
  Proof.
    intros a b.
    unfold le_meet, le_join in *.
    split.
    - intros H.
      rewrite <- H.
      rewrite meet_commutative.
      rewrite join_commutative.
      apply join_meet_absorptive.
    - intros H.
      rewrite <- H.
      apply meet_join_absorptive.
  Qed.

  Instance Reflexive_le_join : Reflexive le_join := join_idempotent.
  Instance Transitive_le_join : Transitive le_join.
  Proof.
    intros x y z.
    do 3 rewrite <- le_meet_join.
    apply Transitive_le_meet.
  Qed.
  Instance PreOrder_le_join : PreOrder le_join := {|
    PreOrder_Reflexive := Reflexive_le_join;
    PreOrder_Transitive := Transitive_le_join;
  |}.
  Instance PartialOrder_le_join : PartialOrder equ le_join.
  Proof.
    intros x y.
    unfold pointwise_lifting, relation_conjunction, Basics.flip, predicate_intersection, pointwise_extension.
    do 2 rewrite <- le_meet_join.
    apply PartialOrder_le_meet.
  Qed.

End Lattice.
End Lattice.

