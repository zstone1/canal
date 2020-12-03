Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice div.
From mathcomp Require Import seq fintype bigop order ssralg ssrnum finmap matrix.
From mathcomp Require Import topology normedtype derive all_real_closed.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import Num.Theory GRing.Theory GRing.

Section Holomorphic.
Context {R : rcfType}.
Notation C := R[i].
Ltac as_R2 := 
  match goal with 
  | x : R[i] |- _ => destruct x 
  end.
Definition complex_lmodTypeR := Rcomplex_lmodType R.
Definition r_pseudoMetric := (numFieldType_pseudoMetricType R).
Definition r2_pseudoMetric := [pseudoMetricType R of (r_pseudoMetric * r_pseudoMetric)].

Open Scope ring_scope.
Open Scope complex_scope.
Definition ball_R2 : C -> R -> C -> Prop := fun z eps z' => 
  let: x +i* y := z in
  let: x' +i* y' := z' in 
  ball (R := R) (M := r2_pseudoMetric) 
    (x,y) eps (x',y').

Program Definition complex_PseudoMetric := 
  @PseudoMetricMixin R C (entourage_ ball_R2) ball_R2 _ _ _ _.
Next Obligation.
  case: x; move => ??.
  rewrite /ball_R2 /prod_ball.
  by apply PseudoMetric.ax1.
Qed.
Next Obligation.
  move: H; case: x; case: y => ????.
  apply PseudoMetric.ax2.
Qed.
Next Obligation.
  move: z y x H H0 => [r1 l1][r2 l2][r3 l3].
  apply PseudoMetric.ax3.
Qed.
Program Definition complex_NormedModuleMixin := NormedModMixin (K := R) _.

Program Definition foo := @pseudoMetric_of_normedDomain R [normedZModType R of C] _.

Program Definition complex_pseudoMetricType_mixin := topologyOfBaseMixin (T := C).
  [uniformType of C].

Print matrix_pseudoMetricType_mixin.
Program Definition complex_pseudoMetricType_mixin := 
  @PseudoMetricMixin R C.
Local Open Scope ring_scope.
Search (_ -> pseudoMetricType _).
Definition complex_pseudoMetricType := 
  
Definition complex_pseudoMetricNormedZmodType := 
  numFieldType_pseudoMetricNormedZmodMixin [numFieldType of R] .

Canonical complex_pseudoMetricNormedZmodType.
Definition foo := NormedModMixin (K := R) (V:=complex_pseudoMetricNormedZmodType).
Check foo.
Canonical structure (foo : pseudoMetricNormedZmodType C) := _.
Canonical normedModType C. 

Definition Holomorphic (f : C -> V) F := differentiable f F.