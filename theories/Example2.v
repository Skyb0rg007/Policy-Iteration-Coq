Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qminmax.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Unicode.Utf8.
Require Import Iteration.Lattice.
Require Import Iteration.QInf.
Require Import Iteration.Selection.

Generalizable All Variables.

Import ListNotations.
Local Open Scope Q_scope.
Local Open Scope QInf_scope.
Local Open Scope equiv_scope.

Definition g1 x := (x + 2.5) ⊔ -5.
Definition g2 x := (x + 0.5) ⊔ -3.
Definition g3 x := (x - 3) ⊔ 1.
Definition g4 x := (x - 4) ⊔ 1.5.
Definition g5 x := (x - 4.5) ⊔ 2.5.

Definition G := [g1; g2; g3; g4; g5].

Definition f := inf G.

(* We register the g's as morphisms (ie. respect QInf.eq) *)
Ltac g_mor :=
  intros x y H;
  destruct x; destruct y; inversion H as [H1]; try reflexivity;
  apply Qeq_bool_iff in H1;
  unfold QInf.eq, QInf.eqb;
  simpl;
  rewrite H1;
  apply Qeq_bool_iff;
  reflexivity.

Add Morphism g1 with signature QInf.eq ==> QInf.eq as g1_mor.
Proof. g_mor. Qed.

Add Morphism g2 with signature QInf.eq ==> QInf.eq as g2_mor.
Proof. g_mor. Qed.

Add Morphism g3 with signature QInf.eq ==> QInf.eq as g3_mor.
Proof. g_mor. Qed.

Add Morphism g4 with signature QInf.eq ==> QInf.eq as g4_mor.
Proof. g_mor. Qed.

Add Morphism g5 with signature QInf.eq ==> QInf.eq as g5_mor.
Proof. g_mor. Qed.

Add Morphism f with signature QInf.eq ==> QInf.eq as f_mor.
Proof. g_mor. Qed.

(* This is extremely annoying to prove, there has to be a better way
   to show that G admits a lower selection *)
Lemma g1_matches : ∀ x, x ≤ -5.5 → g1 x === f x.
Proof.
  intros x H.
  destruct x; try reflexivity.
  destruct (Qcompare_spec (q + 2.5) (-5)).
  - setoid_replace (-5)%Q with (-7.5 + 2.5)%Q in H0; try reflexivity.
    rewrite Qplus_inj_r in H0.
    unfold Equivalence.equiv, QInf.eq, QInf.eqb.
    simpl.
    apply Qeq_bool_iff.
    rewrite H0.
    reflexivity.
  - unfold QInf.le, QInf.leb in H.
    rewrite Qle_bool_iff in H.
    setoid_replace (-5)%Q with (-7.5 + 2.5)%Q in H0; try reflexivity.
    rewrite Qplus_lt_l in H0.
    unfold Equivalence.equiv, QInf.eq, QInf.eqb.
    simpl.
    apply Qeq_bool_iff.
    assert (Qmax (q + 2.5) (-5) == (-5))%Q.
    { apply Q.max_r.
      setoid_replace (-5)%Q with (-7.5 + 2.5)%Q; try reflexivity.
      apply Qplus_le_l.
      apply Qlt_le_weak.
      assumption. }
    setoid_rewrite H1.
    assert (Qmax (q + 0.5) (-3) == -3)%Q.
    { apply Q.max_r.
      setoid_replace (-3)%Q with (-3.5 + 0.5)%Q; try reflexivity.
      apply Qplus_le_l.
      assert (Qle (-5.5) (-3.5)). { apply Qle_bool_iff. reflexivity. }
      apply (Qle_trans _ _ _ H H2). }
    setoid_rewrite H2.
Admitted.

Section PI.
  (* Algorithm PI example (Example 2) *)

  (* Step 1: Set k = 1 and select g ∈ G *)
  (* We choose g5 *)

  (* Step 2: Find a fixed point for g5 *)
  (* We compute the least fixed point xᵏ of g5 *)

  Definition x1 := 2.5.

  Lemma x1_g5_least_fixed_point : least_fixed_point g5 x1.
  Proof.
    unfold x1.
    split.
    - reflexivity.
    - intros y H.
      unfold fixed_point in H.
      destruct y.
      + inversion H.
      + reflexivity.
      + unfold Lattice.le_meet, meet, Equivalence.equiv, QInf.eq, QInf.eqb in *.
        simpl in *.
        apply Qeq_bool_iff.
        apply Qeq_bool_iff in H.
        apply Q.min_l.
        destruct (Qcompare_spec (2.5) q).
        * rewrite H0. apply Qle_refl.
        * apply Qlt_le_weak in H0. assumption.
        * apply Qlt_not_le in H0.
          unfold Qmax, GenericMinMax.gmax in H.
          destruct (Qcompare_spec (q - 4.5) 2.5).
          -- rewrite (Qeq_trans _ _ _ H H1).
             apply Qle_refl.
          -- rewrite H.
             apply Qle_refl.
          -- rewrite H in H0.
             apply Qlt_le_weak in H1.
             contradiction.
  Qed.

  (* Step 3: Compute f(xₖ) *)
  (* Step 4: If xᵏ = f(xᵏ), return xᵏ *)
  (* This fails in our example *)

  Lemma x1_not_f_fixpoint : ¬ (fixed_point f x1).
  Proof. intros H. inversion H. Qed.

  (* Step 5: Choose g ∈ G st f(xᵏ) = g(xᵏ) *)
  (* We choose g3 *)

  Lemma g3_matches : f x1 == g3 x1.
  Proof. reflexivity. Qed.

  (* Repeat: find fixed point for g3 *)

  Definition x2 := 1.

  Lemma x2_g3_least_fixed_point : least_fixed_point g3 x2.
  Proof.
    split.
    - reflexivity.
    - intros y H.
      unfold x2.
      unfold fixed_point in H.
      destruct y.
      + inversion H.
      + reflexivity.
      + unfold Lattice.le_meet, meet, Equivalence.equiv, QInf.eq, QInf.eqb in *.
        simpl in *.
        apply Qeq_bool_iff.
        apply Qeq_bool_iff in H.
        apply Q.min_l.
        destruct (Qcompare_spec 1 q).
        * rewrite H0. apply Qle_refl.
        * apply Qlt_le_weak in H0. assumption.
        * apply Qlt_not_le in H0.
          unfold Qmax, GenericMinMax.gmax in H.
          destruct (Qcompare_spec (q - 3) 1).
          -- rewrite (Qeq_trans _ _ _ H H1).
             apply Qle_refl.
          -- rewrite H.
             apply Qle_refl.
          -- rewrite H in H0.
             apply Qlt_le_weak in H1.
             contradiction.
  Qed.

  Lemma x2_f_fixed_point : fixed_point f x2.
  Proof. reflexivity. Qed.

End PI.


(* Some monotone definitions *)
Definition monotone `{PreOrder A R} (f : A → A) :=
  Proper (R ==> R) f.

Require Import Coq.QArith.QArith.

Instance PreOrder_Qle : PreOrder Qle := {|
  PreOrder_Reflexive := Qle_refl;
  PreOrder_Transitive := Qle_trans;
|}.

Definition succ (n : Q) := n + 1.

Definition monotone_succ : monotone succ.
Proof.
  intros x y.
  apply Qplus_le_l.
Qed.

Lemma monotone_respectful `{PartialOrder A equ R} (f : A → A) :
  monotone f → Proper (equ ==> equ) f.
Proof.
  intros M x y Eq.
  apply partial_order_equivalence.
  split.
  - apply M.
    apply partial_order_equivalence.
    symmetry.
    assumption.
  - apply M.
    apply partial_order_equivalence.
    assumption.
Qed.

