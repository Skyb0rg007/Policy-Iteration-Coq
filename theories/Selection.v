Require Import Coq.Classes.Equivalence.
Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8.
Require Import Iteration.Lattice.

Generalizable All Variables.

Local Open Scope equiv_scope.

Definition inf {X} `{Lattice A} (G : list (X → A)) (x : X) :=
  List.fold_right (λ g a, a ⊓ g x) top G.

(* We use the paper's equivalent definition since it's simpler to write *)
Definition lower_selection {X} `{Lattice A} (G : list (X → A)) : Prop :=
  ∀ x, Exists (λ g, g x === inf G x) G.

Definition fixed_point `{Equivalence A} (f : A → A) (x : A) : Prop :=
  x === f x.

Definition least_fixed_point `{Lattice A} (f : A → A) (x : A) : Prop :=
  fixed_point f x ∧ ∀ y, fixed_point f y → Lattice.le_meet x y.

