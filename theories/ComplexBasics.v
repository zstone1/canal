Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice div.
From mathcomp Require Import seq fintype bigop order ssralg ssrnum finmap matrix.
From mathcomp Require Import topology normedtype derive all_real_closed reals.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import Num.Theory GRing.Theory GRing.
Open Scope ring_scope.
Open Scope complex_scope.

Reserved Notation "''Dz' f" (at level 0, f at level 0,
  format "''Dz'  f").
Section C_structures.
Set Printing Coercions.
Variable (R : realType).
(* This is R[i], as seen as a 1-R[i] dimension normed vector space*)
Definition C := numFieldType_normedModType [numFieldType of R[i]].

Section Holomorphic.
Variable (V : normedModType C).
Definition Holomorphic (f : C -> V) z := derivable f 1 z.
Notation "''Dz' g" := ('D_1 g) .
Check is_derive_cst.

Definition g := (cst 0 : C -> V) .
Lemma foo : forall q, 
  g ^`() q = 0.
Proof.
  move => q //.
  rewrite /g derive1E. 
  have x (_ : (@is_derive_cst [numFieldType of derive1E]).
  1: have x := (@diff_cst C) .
  Search diff_cts.
simpl.

Definition CHolo (f : C -> V) z := 
    Holomorphic f z /\
    continuous ('Dz f) z .

End Holomorphic. 



