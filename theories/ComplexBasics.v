From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice div .
From mathcomp Require Import seq finset fintype bigop order ssralg ssrnum finmap matrix interval.
From mathcomp Require Import all_real_closed.
From mathcomp Require Import 
  boolp reals nngnum posnum classical_sets topology 
  normedtype prodnormedzmodule derive reals landau forms.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import Order.TTheory GRing.Theory Num.Theory.
Open Scope complex_scope.
Open Scope classical_set_scope.
Open Scope ring_scope.

Section C1.
Context {R:numFieldType} {V : normedModType R}.

Open Scope type_scope.
Definition C_1 (f : R^o -> V^o) := forall (z:R),
  { near (z:R^o), forall x, differentiable f x} /\
  { near (z:R^o), continuous (f^`() : R^o -> _)}.
End C1.

Section SubspaceContinuity.
Variable (X Y : topologicalType).

Definition continuous_on (U : set X) (f: X^o -> Y) := 
  (forall x, f @ (within U [filter of x]) --> f x).

End SubspaceContinuity.
Section C_structures.
Set Printing Coercions.
Variable (R : realType).
(* This is R[i], as seen as a 1-R[i] dimension normed vector space*)
Definition C := R[i].
Definition as_R2 (z:C) := let: x +i* y := z in (x,y).

Section Holomorphic.
Context {V : normedModType C}.

Definition Holomorphic_on U {O:open U} (f : C^o -> V) :=
    {in U, forall z, derivable f 1 z}.
Program Definition CHolo_on U {O:open U} (f : C^o -> V) (z:C^o) := 
  Holomorphic_on (O:=O) f /\
  {in U, continuous (f^`() : C^o -> _) }.
End Holomorphic. 

Section ComplexIntegrals.

Context {V : normedModType R}.

Record CIntegral := {
  path : R^o -> C^o;
  l_end : R^o;
  r_end : R^o;
  f : C^o -> V^o;

  lltr : l_end < r_end;
  cts_f : continuous_on 
    (path @` itv_decompose `[l_end,r_end]) f;
  (* continuously differentiable on the open interval*)
  pathdiff : {in `]l_end,r_end[, C_1 
    (as_R2 \o path : R^o -> R^o * R^o)  };
  (* continuous on the closed interval*)
  pathcts : continuous_on (X:=[topologicalType of R^o])
    (itv_decompose `[l_end, r_end]) path;
}.

Section 





