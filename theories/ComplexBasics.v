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

(** We first need to discuss restricting functions to a region*)
Section DomainRestrictions.
Context {U V : Type}.
Variable (A : set U).
Local Definition explode (f : U -> V) :=
  [set g : U -> V | {in A, f =1 g} ].

Local Definition explode_set (X : set (U -> V)) := 
  \bigcup_(f in X) explode f.

Lemma explode_refl: forall f, explode f f.
Proof.
  rewrite /explode.
  by move => f /=.
Qed.

Lemma explodeE : forall f g, 
  explode f g <-> {in A, f =1 g}.
Proof. done. Qed.


Lemma explode_setT : explode_set setT = setT.
Proof.
  rewrite /explode_set /= eqEsubset; split => f.
  - by move.
  - move => ?.
    econstructor.
    2: apply: explode_refl.
    eauto.
Qed.

Definition restricted (F : set (set (U -> V))) :=
  [set Q | (exists P, F P /\ explode_set P `<=` Q)].

Global Instance restricted_filter F: Filter F -> Filter (restricted F).
Proof.
  move => FF. rewrite /restricted. constructor.
  - rewrite /=; exists setT; split.
    2: rewrite [x in x `<=` _]explode_setT.
    2: done.
    by apply filterE.
  - move => /= P Q [P' [? a]] [Q' [? b]].
    set R := [set f | P' f /\ (exists g, Q' g /\ {in A, f =1 g}) ].
    exists R.
    split.
    + apply: (filter_app _ _ _ (P := Q' `&` P')).
      2: by apply: (filterI).
      apply: filterE.
      move => g [??] /=.
      rewrite /R /=; split; first by [].
      by exists g. 
    + move => f [g [gP [g' [g'Q W]]] /explodeE E].
        split; [apply: a| apply b];
        rewrite /explode_set => /=;
          first by (exists g; eauto).
        exists g'; first by eauto.
        rewrite explodeE => t tA.
        by apply: eq_trans; [symmetry; apply:W |apply:E].
  - move => P Q W /= [P' [W1 W2]].
    exists P'; split; first by [].
    apply: subset_trans. 
    2: apply: W.
    exact W2.
Qed.

Canonical restricted_filter_on (F: filter_on (U -> V)) := 
  FilterType (restricted F) (restricted_filter _) .

Lemma restricted_filter_not_emtpy : forall (F: pfilter_on (U -> V)),
  ~ restricted F set0.
Proof.
  move => [F1 [N ?]] [P [M W]].
  have  Q: (P = set0).
  {
    apply: funext => f.
    apply: propext; split; last by [].
    move: W=> /(_ f) W L; apply: W.
    exists f; first by [].
    apply explode_refl.
  }
  have R: (set0 = xpredp0) by done.
  move: M => /=; rewrite Q R.
  done.
Qed.

Global Instance restricted_prop_filter F : 
  ProperFilter F -> ProperFilter (restricted F).
Proof.
  move => [N ?]; constructor.
  2: apply: restricted_filter.
  move => W. 
  rewrite /restricted in W.
  case: W => B [X W] .
  have: ( B = xpredp0).
  2: congruence.
  apply: funext => f.
  apply: propext; split; last by [].
  move: W=> /(_ f) W L; apply: W.
  exists f; first by [].
  apply explode_refl.
Qed.

Canonical restricted_pfilter_on (F: pfilter_on (U -> V)) := 
  PFilterType (restricted F) (@restricted_filter_not_emtpy _) .

Definition explode_pair ( fg : (U -> V) * (U -> V)) :=
  explode (fg.1) `*` explode (fg.2).

Definition explode_pairs ( X : set ((U -> V) * (U -> V))) :=
  \bigcup_(f in X) explode_pair f.

Definition restrict_ent (E : set(set((U -> V) * (U -> V)))) :=
  [set Q | (exists P, E P /\ explode_pairs P `<=` Q)].

End DomainRestrictions.

Section RestrictionTopology.
Context {U : choiceType} {V : uniformType}.
Variable (A : set U).

Definition restricted_nbhs_filter (p : U -> V) := 
  restricted A [filter of p].

Definition restricted_ent := restrict_ent A (@fct_ent U V).

Lemma restricted_ent_explode : forall i,
  fct_ent i -> restricted_ent (explode_pairs A i).
Proof.
  move => i J.
  pose proof J as J'.
  move: J' => [j E L].
  exists (explode_pairs A i).
  split.
  apply: filterS.
  2: exact J.
  - move => [f g] I.
    rewrite /explode_pairs /explode_pair.
    exists (f,g); first by [].
    move => /=; split; apply: explode_refl.
  - move => [t1 t2] [[x1 x2] [[y1 y2] M]].
    rewrite /explode_pairs /= /explode_pair /setM /=.
    move => [/explodeE E1 /explodeE E2] [/explodeE E3 /explodeE E4].
    exists (y1,y2); first by [].
    rewrite /explode_pair /= /setM /=.
    split; apply/explodeE; move => t T;
      apply: eq_trans.
    + by apply: E1.
    + by apply: E3.
    + by apply: E2.
    + by apply: E4.
Qed.

Definition patch (f g : U -> V) := 
  (fun u => 
     if_expr (asbool (A u)) (g u) (f u)). 
Lemma explode_patch : forall f g,
  explode A g (patch f g).
Proof.
  move => f g. 
  apply/explodeE => u.
  rewrite /patch /in_mem /mem /= /in_set /=.
  move => -> //=.
Qed.

    
Lemma explode_pairs_lhs : forall I (f g: U -> V), 
  fct_ent I -> 
    (explode_pairs A I (f,g) <-> 
      exists g', explode A g g' /\ I (f, g')
    ).
Proof.
  move => I f g eI.
  split.
  - move => [[f' g']] Ifg [ /= e1 e2].
    exists (patch f g').
    split.
    1: by move => ??; rewrite e2.
    case: eI => B eI Q.
    apply Q.

    
  - move => [g' [L R]]; exists (f,g').
    1: done.
    split => /=.
    1: apply explode_refl.
    move => ??; rewrite L; done.

  
  move => t /= [[g1 g2] gI [] /= E1 E2] .
    exists g2 => /=.
    2: done.
    move: fI => [B eB] M.
    apply: M => /=.

    unfold fct_ent, filter_from in fI.
    simpl in *.
  - 

Lemma restricted_ent_eq : forall f,
  restricted_nbhs_filter f = nbhs_ (restricted_ent) f.
Proof.
  move => f.
  rewrite eqEsubset; split.
  - move => P [Q [M N]].
    have : (nbhs f Q) by apply: M.
    rewrite nbhsP /nbhs_ /filter_from /= => /exists2P [i [L1 L2]].
    exists (explode_pairs A i).
    1: by apply restricted_ent_explode.
    apply: subset_trans.
    2: apply: N.
    admit.
  - move => P [rI [I [? S] N]].
    exists [set y | I (f,y)]; split.
    1: by exists I.
    apply: subset_trans.
    2: apply: N.
    move => g [g' /= gI] E.
    apply S.
    exists (f,g').
    1: done.
    split => /=.
    1: apply explode_refl.
    done.
Qed.
    rewrite /explode_pairs /explode_set /= => /exists2P [[g1 g2] [? O]].
    rewrite /explode_r /setM /set1 /= in O.
    exists g2.

    apply: L2 => /=; by apply: entourage_refl.

    
    
Program Definition restricted_uniformMixin := @topologyOfFilterMixin 
  (U -> V)
  restricted_nbhs_filter
  (fun p => 
    @restricted_prop_filter U V A ([filter of p]) _)
  _
  _
  .
Next Obligation.
Proof.
  case: H => P [[ X Y Z ] W].
  apply: W.
  exists p; last by apply: explode_refl.
  apply: Z => /=.
  apply fct_ent_refl; done.
Qed.
Next Obligation.
  case:H => P [X Y].
  have Z : fct_ent_split
  rewrite /restricted_nbhs_filter /restricted /=.
  eexists.
  split.
  2: { move => f.
  2: move => [g gP].
  2: eexists.


End DomainRestrictions.

Section RestrictedTopology.
Context {U : choiceType} {V : uniformType}.
Variable (A : set U).

Definition restricted_topologyType_mixin := 
  topologyOfFilterMixin.



(** We need to define the topology of compact convergence
    before we get started *)
Section CompactCongergence.
Variable (U : topologicalType) ( P : set (set U)) .
Section Topology.
Variable (V : topologicalType).

Definition fct_cnv_on_P_mixin := 
  @topologyOfSubbaseMixin 
    _ (U -> V)
    [set MA  | open MA.2 /\  P MA.1 ]
    (fun MA => 
      [set g | {in (MA.1 : set U), forall t, (MA.2 (g t))}]
    )
.

Definition compact_cnv_topologicalType := Topological.Pack (
  (@Topological.Class _ 
      (Filtered.Class (Pointed.class _) _)
    fct_cnv_on_P_mixin)).

Local Notation TCC := compact_cnv_topologicalType.
Local Definition nbhs_TCC := @nbhs (U -> V) [filteredType TCC of TCC].

Lemma nbhs_TCC_alt : forall (F : set (set TCC)) (f:TCC),
  F --> f <-> forall K, P K -> 
     . 
    
End Topology.

Section Uniform.
Variable (V : uniformType).

Context (nonemptyP : nonempty P).
Context (intersectP : forall i j, P i /\ P j -> P (i `&` j)).
Print nonempty.
Definition cvg_on_P_ent := 
  @filter_from (set U * set (V * V)) ((U -> V) * (U -> V))
  [set AB | P AB.1 /\ entourage AB.2]
  (fun AB => 
    [set fg | {in AB.1, forall t, AB.2 (fg.1 t, fg.2 t)}]
  )
  .

Lemma compact_entourage_nbhs: nbhs_TCC (V:=V) = nbhs_ cvg_on_P_ent.
Proof.
  apply: funext => p. 
  rewrite  nbhs_E /filter_from.
  rewrite /nbhs_TCC /nbhs /=. 
  rewrite eqEsubset; split.
    rewrite nbhsP.
    apply (in_filter_from ((U -> V) * (U -> V)) _ cvg_on_P_ent). 
  
  rewrite /nbhs_TCC /nbhs /=.
  Search "`<=`".

  

Program Definition compact_cvg_ent_mixin :=
  @Uniform.Mixin (U -> V) (@nbhs_TCC V) cvg_on_P_ent _ _ _ _ _.
Next Obligation.
Proof.
  apply: filter_from_filter.
  {  move: nonemptyP => [?]?.
     eexists (_,_); rewrite //=; split;
    [eauto | apply: entourageT].
  }
  move => [i1 i2] [j1 j2] /= [??] [??].
  exists ((i1 `&` j1), (i2 `&` j2)).
  split => /=.
  1: by apply: intersectP.
  1: by apply: filterI.
  rewrite /=.


Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Proof.

Lemma compact_cnv_limits : forall F (f: U -> V),
  F `=>` nbhs_TCC f <-> 
  true.
    

Definition locally_compact_cnv := 

Section Integrals.


Variable (R : realType) (V : normedModType R).


Definition C_1 {R:numFieldType} {V : normedModType R} 
  (f : R^o -> V^o) := forall (z:R),
  { near (z:R^o), forall x, differentiable f x} /\
  { near (z:R^o), continuous (f^`() : R^o -> _)}.

Structure ContourIntegral := {
  integrate : R -> R -> (R^o -> V) -> V;

  linear : forall l r, linear (integrate l r);
  ftc : forall (l r :R) (f : R^o -> V), 
    {in `]l,r[, C_1 f } ->
    integrate l r (f^`()) = f r - f l
  
}.

Section C1.
Open Scope type_scope.

Definition continuous_on 
  {X Y : topologicalType} (U : set X) (f: X^o -> Y) := 
  (forall x, f @ (within U [filter of x]) --> f x).

Definition continuous_on_itv 
  {R:rcfType} {V : topologicalType} (i : interval R) 
  (f : R^o -> V^o) :=
  @continuous_on ([topologicalType of R^o]) _
    (itv_decompose i) f.


Inductive Piecewise_C_1 {R : realType} {V : normedModType R} 
  (l r:R) (f : R^o -> V) : Prop :=
| OnePiece : 
    {in `]l,r[, C_1 f } -> 
    continuous_on_itv `[l,r] f ->
    Piecewise_C_1 l r f
| Combined : forall (c : R), 
    Piecewise_C_1 l c f -> 
    Piecewise_C_1 c r f -> 
    Piecewise_C_1 l r f
.


    forall (i : interval R,  C_1  -> Piecewise P f.

End C1.

Section SubspaceContinuity.
Variable .

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





