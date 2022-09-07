Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qminmax.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Unicode.Utf8.
Require Import Iteration.Lattice.

(* Rationals with ±+∞ *)

Reserved Notation "+∞" (at level 0).
Reserved Notation "-∞" (at level 0).

Declare Scope QInf_scope.
Delimit Scope QInf_scope with QInf.

Module QInf.

  Local Open Scope Q_scope.
  Local Open Scope QInf_scope.

  Inductive t :=
    NegInf : t 
  | PosInf : t 
  | Fin : Q → t.

  Coercion Fin : Q >-> t.

  Notation "+∞" := PosInf : QInf_scope.
  Notation "-∞" := NegInf : QInf_scope.

  Definition eqb n m :=
    match n, m with
    | +∞, +∞ => true
    | -∞, -∞ => true
    | Fin n, Fin m => Qeq_bool n m
    | _, _ => false
    end.

  Definition eq n m := eqb n m = true.

  Infix "==" := eq : QInf_scope.
  
  Hint Unfold eq eqb : core.

  Lemma eq_refl : Reflexive eq.
  Proof.
    intros x.
    destruct x; try reflexivity.
    apply Qeq_bool_refl.
  Qed.

  Lemma eq_sym : Symmetric eq.
  Proof.
    intros x y H.
    destruct x; destruct y; inversion H; try reflexivity.
    apply Qeq_bool_sym.
    assumption.
  Qed.

  Lemma eq_trans : Transitive eq.
  Proof.
    intros x y z P Q.
    destruct x; destruct y; destruct z; inversion P; inversion Q; try reflexivity.
    apply (Qeq_bool_trans _ _ _ P Q).
  Qed.

  Lemma eq_Qeq : ∀ x y, (x == y)%Q → (x == y)%QInf.
  Proof.
    intros x y.
    apply Qeq_bool_iff.
  Qed.

  Global Instance Equivalence_eq : Equivalence eq := {|
    Equivalence_Reflexive := eq_refl;
    Equivalence_Symmetric := eq_sym;
    Equivalence_Transitive := eq_trans;
  |}.

  Add Relation t eq
    reflexivity proved by eq_refl
    symmetry proved by eq_sym
    transitivity proved by eq_trans
    as eq_qinf_rel.

  Definition leb n m :=
    match n, m with
    | +∞, +∞ => true
    | +∞, _ => false
    | _, +∞ => true
    | -∞, _ => true
    | _, -∞ => false
    | Fin n, Fin m => Qle_bool n m
    end.

  Definition le n m := leb n m = true.

  Infix "<=" := le : QInf_scope.
  Infix "≤" := le : QInf_scope.

  Hint Unfold le leb : core.

  Lemma le_refl : Reflexive le.
  Proof.
    intros x.
    destruct x; try reflexivity.
    unfold le, leb.
    rewrite Qle_bool_iff.
    apply Qle_refl.
  Qed.

  Lemma le_trans : Transitive le.
  Proof.
    intros x y z P Q.
    destruct x; destruct y; destruct z; inversion P; inversion Q; try reflexivity.
    unfold le, leb in *.
    rewrite Qle_bool_iff in *.
    apply (Qle_trans _ _ _ P Q).
  Qed.

  Global Instance PreOrder_le : PreOrder le := {|
    PreOrder_Reflexive := le_refl;
    PreOrder_Transitive := le_trans;
  |}.

  Global Instance PartialOrder_eq_le : PartialOrder eq le.
  Proof.
    intros x y.
    split.
    - intros H.
      split;
        destruct x; destruct y; inversion H; try reflexivity;
        apply Qle_bool_iff;
        apply Qeq_bool_eq in H1;
        rewrite H1;
        apply Qle_refl.
    - intros H.
      destruct H as [P Q].
      destruct x; destruct y; inversion P; inversion Q; try reflexivity.
      apply Qeq_eq_bool.
      apply Qle_bool_iff in H0.
      apply Qle_bool_iff in H1.
      apply (Qle_antisym _ _ H0 H1).
  Qed.

  Add Morphism le with
    signature eq ==> eq ==> iff as le_mor.
  Proof.
    intros x y P z w Q.
    split.
    - intros H.
      destruct x; destruct y; destruct z; destruct w;
      inversion P; inversion Q; inversion H; try reflexivity.
      apply Qle_bool_iff.
      apply Qeq_bool_eq in H1.
      apply Qeq_bool_eq in H2.
      apply Qle_bool_iff in H3.
      rewrite H2 in H3.
      rewrite H1 in H3.
      assumption.
    - intros H.
      destruct x; destruct y; destruct z; destruct w;
      inversion P; inversion Q; inversion H; unfold le, leb; try reflexivity.
      apply Qle_bool_iff.
      apply Qeq_bool_eq in H1.
      apply Qeq_bool_eq in H2.
      apply Qle_bool_iff in H3.
      rewrite <- H2 in H3.
      rewrite <- H1 in H3.
      assumption.
  Qed.

  Definition add n m :=
    match n with
    | -∞ => -∞
    | +∞ => +∞
    | Fin n => n + m
    end.

  Infix "+" := add : QInf_scope.

  Add Morphism add with
    signature eq ==> Qeq ==> eq as add_mor.
  Proof.
    intros x y P z w Q.
    destruct x; destruct y; destruct z; destruct w;
    inversion P; inversion Q; try reflexivity.
    clear H1.
    remember (Qnum # Qden) as x.
    remember (Qnum0 # Qden0) as y.
    unfold add, eq, eqb in *.
    apply Qeq_bool_iff.
    apply Qeq_bool_iff in P.
    rewrite P.
    rewrite Q.
    reflexivity.
  Qed.

  Definition sub n m :=
    match n with
    | -∞ => -∞
    | +∞ => +∞
    | Fin n => n - m
    end.

  Infix "-" := sub : QInf_scope.

  Add Morphism sub with
    signature eq ==> Qeq ==> eq as sub_mor.
  Proof.
    intros x y P z w Q.
    destruct x; destruct y; destruct z; destruct w;
    inversion P; inversion Q; try reflexivity.
    clear H1.
    remember (Qnum # Qden) as x.
    remember (Qnum0 # Qden0) as y.
    unfold sub, eq, eqb in *.
    apply Qeq_bool_iff.
    apply Qeq_bool_iff in P.
    rewrite P.
    rewrite Q.
    reflexivity.
  Qed.

  Definition min n m :=
    match n, m with
    | -∞, _ => -∞
    | _, -∞ => -∞
    | +∞, m => m
    | n, +∞ => n
    | Fin n, Fin m => Qmin n m
    end.

  Lemma min_comm : ∀ n m, (min n m == min m n)%QInf.
  Proof.
    intros n m.
    destruct n; destruct m; try reflexivity.
    apply Qeq_bool_iff.
    apply Q.min_comm.
  Qed.

  Lemma min_id : ∀ n, (min n n == n)%QInf.
  Proof.
    intros n.
    destruct n; try reflexivity.
    apply Qeq_bool_iff.
    apply Q.min_id.
  Qed.

  Lemma min_posinf : ∀ n, (min n +∞ == n)%QInf.
  Proof.
    intros n. destruct n; reflexivity.
  Qed.

  Lemma min_assoc : ∀ m n p, (min m (min n p) == min (min m n) p)%QInf.
  Proof.
    intros m n p.
    destruct m; destruct n; destruct p; try reflexivity.
    apply Qeq_bool_iff.
    apply Q.min_assoc.
  Qed.

  Add Morphism min with
    signature eq ==> eq ==> eq as min_mor.
  Proof.
    intros x y P z w Q.
    destruct x; destruct y; destruct z; destruct w;
    inversion P; inversion Q; try reflexivity;
    unfold eq, eqb in *; simpl;
    apply Qeq_bool_iff.
    apply Qeq_bool_iff in Q.
    assumption.
    apply Qeq_bool_iff in P.
    assumption.
    apply Qeq_bool_iff in Q.
    apply Qeq_bool_iff in P.
    rewrite P.
    rewrite Q.
    reflexivity.
  Qed.

  Definition max n m :=
    match n, m with
    | +∞, _ => +∞
    | _, +∞ => +∞
    | -∞, m => m
    | n, -∞ => n
    | Fin n, Fin m => Qmax n m
    end.

  Lemma max_comm : ∀ n m, (max n m == max m n)%QInf.
  Proof.
    intros n m.
    destruct n; destruct m; try reflexivity.
    apply Qeq_bool_iff.
    apply Q.max_comm.
  Qed.

  Lemma max_id : ∀ n, (max n n == n)%QInf.
  Proof.
    intros n.
    destruct n; try reflexivity.
    apply Qeq_bool_iff.
    apply Q.max_id.
  Qed.

  Lemma max_neginf : ∀ n, (max n -∞ == n)%QInf.
  Proof.
    intros n. destruct n; reflexivity.
  Qed.

  Lemma max_assoc : ∀ m n p, (max m (max n p) == max (max m n) p)%QInf.
  Proof.
    intros m n p.
    destruct m; destruct n; destruct p; try reflexivity.
    apply Qeq_bool_iff.
    apply Q.max_assoc.
  Qed.

  Add Morphism max with
    signature eq ==> eq ==> eq as max_mor.
  Proof.
    intros x y P z w Q.
    destruct x; destruct y; destruct z; destruct w;
    inversion P; inversion Q; try reflexivity;
    unfold eq, eqb in *; simpl;
    apply Qeq_bool_iff.
    apply Qeq_bool_iff in Q.
    assumption.
    apply Qeq_bool_iff in P.
    assumption.
    apply Qeq_bool_iff in Q.
    apply Qeq_bool_iff in P.
    rewrite P.
    rewrite Q.
    reflexivity.
  Qed.

  Lemma min_max_absorption : ∀ n m, (max n (min n m) == n)%QInf.
  Proof.
    intros n m.
    destruct n; destruct m; try reflexivity; apply Qeq_bool_iff.
    - apply Q.max_id.
    - apply Q.min_max_absorption.
  Qed.

  Lemma max_min_absorption : ∀ n m, (min n (max n m) == n)%QInf.
  Proof.
    intros n m.
    destruct n; destruct m; try reflexivity; apply Qeq_bool_iff.
    - apply Q.max_id.
    - apply Q.max_min_absorption.
  Qed.

  Global Instance Lattice_QInf : Lattice t := {|
    meet := min;
    join := max;
    top := +∞;
    bot := -∞;

    meet_commutative := min_comm;
    meet_idempotent := min_id;
    meet_associative := min_assoc;
    meet_id := min_posinf;

    join_commutative := max_comm;
    join_idempotent := max_id;
    join_associative := max_assoc;
    join_id := max_neginf;

    meet_join_absorptive := max_min_absorption;
    join_meet_absorptive := min_max_absorption;

    meet_respectful := min_mor;
    join_respectful := max_mor;
  |}.

End QInf.

Coercion QInf.Fin : Q >-> QInf.t.
Notation "+∞" := QInf.PosInf : QInf_scope.
Notation "-∞" := QInf.NegInf : QInf_scope.
Infix "==" := QInf.eq : QInf_scope.
Infix "<=" := QInf.le : QInf_scope.
Infix "≤" := QInf.le : QInf_scope.
Infix "+" := QInf.add : QInf_scope.
Infix "-" := QInf.sub : QInf_scope.


