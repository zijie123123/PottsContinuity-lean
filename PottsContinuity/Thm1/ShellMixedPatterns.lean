module

public import PottsContinuity.Thm1.ShellMixedConstraints

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.PD.CorrLength

noncomputable section

attribute [local instance] configurationMeasurableSpace

/-- An exact finite pair pattern together with prescribed membership in the
finite wired shell class. -/
def pottsESLatticeMixedPairPatternEvent (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) : Set LatticeConfiguration :=
  pottsESLatticeMixedConstraintEvent V Positive GhostSites \
    (⋃ p ∈ Negative,
      pottsESLatticeMixedConstraintEvent V (Positive ∪ {p}) GhostSites)

/-- The corresponding exact pair pattern and infinite-cluster memberships. -/
def pottsESConnectionInfinitePairPatternEvent
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) : Set LatticeConfiguration :=
  pottsESConnectionInfiniteConstraintEvent Positive GhostSites \
    (⋃ p ∈ Negative,
      pottsESConnectionInfiniteConstraintEvent (Positive ∪ {p}) GhostSites)

/-- The exact physical pair pattern intersected with specified shell exits. -/
def pottsESLatticePairGhostPatternEvent (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) : Set LatticeConfiguration :=
  pottsESLatticePairPatternEvent V Positive Negative ∩
    ⋂ x ∈ GhostSites, pottsESLatticeExitEventFrom V x

/-- The exact physical pair pattern intersected with specified infinite-cluster
memberships. -/
def pottsESConnectionInfinitePairGhostPatternEvent
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) : Set LatticeConfiguration :=
  pottsESConnectionPairPatternEvent Positive Negative ∩
    ⋂ x ∈ GhostSites, infiniteAt x

private theorem inter_diff_biUnion_inter {α β : Type*}
    (A C : Set α) (S : Set β) (B : β → Set α) :
    (A ∩ C) \ (⋃ p ∈ S, B p ∩ C) = (A \ ⋃ p ∈ S, B p) ∩ C := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨hA, hC⟩, hNo⟩
    refine ⟨⟨hA, ?_⟩, hC⟩
    rintro ⟨p, hp, hB⟩
    exact hNo ⟨p, hp, hB, hC⟩
  · rintro ⟨⟨hA, hNo⟩, hC⟩
    refine ⟨⟨hA, hC⟩, ?_⟩
    rintro ⟨p, hp, hB⟩
    exact hNo ⟨p, hp, hB.1⟩

private theorem pottsESLatticeMixedPairPattern_eq_pairGhostPattern
    (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    pottsESLatticeMixedPairPatternEvent V Positive Negative GhostSites =
      pottsESLatticePairGhostPatternEvent V Positive Negative GhostSites := by
  unfold pottsESLatticeMixedPairPatternEvent
    pottsESLatticePairGhostPatternEvent pottsESLatticePairPatternEvent
    pottsESLatticeMixedConstraintEvent
  exact inter_diff_biUnion_inter
    (pottsESLatticePairIntersectionEvent V Positive)
    (⋂ x ∈ GhostSites, pottsESLatticeExitEventFrom V x)
    Negative (fun p => pottsESLatticePairIntersectionEvent V (Positive ∪ {p}))

private theorem pottsESConnectionMixedPairPattern_eq_pairGhostPattern
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    pottsESConnectionInfinitePairPatternEvent Positive Negative GhostSites =
      pottsESConnectionInfinitePairGhostPatternEvent
        Positive Negative GhostSites := by
  unfold pottsESConnectionInfinitePairPatternEvent
    pottsESConnectionInfinitePairGhostPatternEvent
    pottsESConnectionPairPatternEvent
    pottsESConnectionInfiniteConstraintEvent
  exact inter_diff_biUnion_inter
    (pottsESConnectionIntersectionEvent Positive)
    (⋂ x ∈ GhostSites, infiniteAt x)
    Negative (fun p => pottsESConnectionIntersectionEvent (Positive ∪ {p}))

private theorem pottsESMixedPairIntersection_biInter_insert_union
    (V : Finset (ℤ × ℤ))
    (Positive P : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) (hP : P.Nonempty) :
    (⋂ p ∈ P,
      pottsESLatticeMixedConstraintEvent V (Positive ∪ {p}) GhostSites) =
      pottsESLatticeMixedConstraintEvent V (Positive ∪ P) GhostSites := by
  ext ω
  simp only [pottsESLatticeMixedConstraintEvent, Set.mem_inter_iff,
    pottsESLatticePairIntersectionEvent, Set.mem_iInter]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro q hq
      rcases Finset.mem_union.mp hq with hqPos | hqP
      · obtain ⟨p, hp⟩ := hP
        exact (h p hp).1 q (Finset.mem_union_left _ hqPos)
      · exact (h q hqP).1 q
          (Finset.mem_union_right _ (Finset.mem_singleton_self q))
    · obtain ⟨p, hp⟩ := hP
      exact (h p hp).2
  · rintro ⟨hPairs, hGhost⟩ p hp
    refine ⟨?_, hGhost⟩
    intro q hq
    rcases Finset.mem_union.mp hq with hqPos | hqp
    · exact hPairs q (Finset.mem_union_left _ hqPos)
    · have hqp' : q = p := Finset.mem_singleton.mp hqp
      subst q
      exact hPairs p (Finset.mem_union_right _ hp)

private theorem pottsESMixedConnectionIntersection_biInter_insert_union
    (Positive P : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) (hP : P.Nonempty) :
    (⋂ p ∈ P,
      pottsESConnectionInfiniteConstraintEvent (Positive ∪ {p}) GhostSites) =
      pottsESConnectionInfiniteConstraintEvent (Positive ∪ P) GhostSites := by
  ext ω
  simp only [pottsESConnectionInfiniteConstraintEvent, Set.mem_inter_iff,
    pottsESConnectionIntersectionEvent, Set.mem_iInter]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro q hq
      rcases Finset.mem_union.mp hq with hqPos | hqP
      · obtain ⟨p, hp⟩ := hP
        exact (h p hp).1 q (Finset.mem_union_left _ hqPos)
      · exact (h q hqP).1 q
          (Finset.mem_union_right _ (Finset.mem_singleton_self q))
    · obtain ⟨p, hp⟩ := hP
      exact (h p hp).2
  · rintro ⟨hPairs, hGhost⟩ p hp
    refine ⟨?_, hGhost⟩
    intro q hq
    rcases Finset.mem_union.mp hq with hqPos | hqp
    · exact hPairs q (Finset.mem_union_left _ hqPos)
    · have hqp' : q = p := Finset.mem_singleton.mp hqp
      subst q
      exact hPairs p (Finset.mem_union_right _ hp)

private theorem pottsESMixedExit_measurable
    (V : Finset (ℤ × ℤ)) (x : ℤ × ℤ) :
    MeasurableSet (pottsESLatticeExitEventFrom V x) := by
  have hEq : pottsESLatticeExitEventFrom V x =
      ⋃ y : {y : ℤ × ℤ // y ∉ V},
        {ω | (PD.rcInfiniteOpenGraph ω).Reachable x y.val} := by
    ext ω
    simp only [pottsESLatticeExitEventFrom, Set.mem_ofPred_eq,
      Set.mem_iUnion, Subtype.exists, exists_prop]
  rw [hEq]
  exact MeasurableSet.iUnion fun y => measurableSet_open_reachable x y.val

private theorem pottsESMixedPair_measurable
    (V : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) :
    MeasurableSet (pottsESLatticePairRelationEvent V x y) := by
  rw [pottsESLatticePairRelationEvent]
  exact (measurableSet_open_reachable x y).union
    ((pottsESMixedExit_measurable V x).inter
      (pottsESMixedExit_measurable V y))

private theorem pottsESMixedPairIntersection_measurable
    (V : Finset (ℤ × ℤ))
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    MeasurableSet (pottsESLatticePairIntersectionEvent V Pairs) := by
  change MeasurableSet (⋂ p ∈ Pairs,
    pottsESLatticePairRelationEvent V p.1 p.2)
  exact Pairs.measurableSet_biInter fun p hp =>
    pottsESMixedPair_measurable V p.1 p.2

private theorem pottsESMixedConstraint_measurable
    (V : Finset (ℤ × ℤ))
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    MeasurableSet (pottsESLatticeMixedConstraintEvent V Pairs GhostSites) := by
  rw [pottsESLatticeMixedConstraintEvent]
  exact (pottsESMixedPairIntersection_measurable V Pairs).inter
    (GhostSites.measurableSet_biInter fun x hx =>
      pottsESMixedExit_measurable V x)

private theorem pottsESMixedConnection_measurable
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    MeasurableSet (pottsESConnectionInfiniteConstraintEvent Pairs GhostSites) := by
  rw [pottsESConnectionInfiniteConstraintEvent]
  exact (Pairs.measurableSet_biInter fun p hp =>
      connectionEvent_isMeasurableSet p.1 p.2).inter
    (GhostSites.measurableSet_biInter fun x hx =>
      (measurableSet_infiniteAt x))

/-- Exact finite pair statuses with any fixed finite collection of shell-class
memberships converge jointly to the corresponding infinite-cluster events. -/
theorem pottsESShellMixedPairPattern_probability_tendsto
    (θ : Parameters) (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    Tendsto
      (fun n => (pottsESShellBondProbabilityMeasure θ (V n) :
        Measure LatticeConfiguration).real
          (pottsESLatticeMixedPairPatternEvent
            (V n) Positive Negative GhostSites))
      atTop (𝓝 (μ.real
        (pottsESConnectionInfinitePairPatternEvent
          Positive Negative GhostSites))) := by
  classical
  let : IsProbabilityMeasure μ := hμ.1
  let νn : ℕ → ProbabilityMeasure LatticeConfiguration :=
    fun n => pottsESShellBondProbabilityMeasure θ (V n)
  let B : ℕ → ((ℤ × ℤ) × (ℤ × ℤ)) → Set LatticeConfiguration :=
    fun n p => pottsESLatticeMixedConstraintEvent (V n) (Positive ∪ {p}) GhostSites
  let BInf : ((ℤ × ℤ) × (ℤ × ℤ)) → Set LatticeConfiguration :=
    fun p => pottsESConnectionInfiniteConstraintEvent (Positive ∪ {p}) GhostSites
  have hBmeas (n : ℕ) (p : (ℤ × ℤ) × (ℤ × ℤ)) : MeasurableSet (B n p) := by
    exact pottsESMixedConstraint_measurable (V n) (Positive ∪ {p}) GhostSites
  have hBInfMeas (p : (ℤ × ℤ) × (ℤ × ℤ)) : MeasurableSet (BInf p) := by
    exact pottsESMixedConnection_measurable (Positive ∪ {p}) GhostSites
  have hUnionMeas (n : ℕ) : MeasurableSet (⋃ p ∈ Negative, B n p) := by
    apply MeasurableSet.iUnion
    intro p
    apply MeasurableSet.iUnion
    intro hp
    exact hBmeas n p
  have hUnionInfMeas : MeasurableSet (⋃ p ∈ Negative, BInf p) := by
    apply MeasurableSet.iUnion
    intro p
    apply MeasurableSet.iUnion
    intro hp
    exact hBInfMeas p
  have hBsubset (n : ℕ) : (⋃ p ∈ Negative, B n p) ⊆
      pottsESLatticeMixedConstraintEvent (V n) Positive GhostSites := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω
    rcases hω with ⟨p, hp, hpω⟩
    simp only [B, pottsESLatticeMixedConstraintEvent,
      pottsESLatticePairIntersectionEvent, Set.mem_inter_iff,
      Set.mem_iInter] at hpω ⊢
    exact ⟨fun q hq => hpω.1 q (Finset.mem_union_left _ hq), hpω.2⟩
  have hBInfSubset : (⋃ p ∈ Negative, BInf p) ⊆
      pottsESConnectionInfiniteConstraintEvent Positive GhostSites := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω
    rcases hω with ⟨p, hp, hpω⟩
    simp only [BInf, pottsESConnectionInfiniteConstraintEvent,
      pottsESConnectionIntersectionEvent, Set.mem_inter_iff,
      Set.mem_iInter] at hpω ⊢
    exact ⟨fun q hq => hpω.1 q (Finset.mem_union_left _ hq), hpω.2⟩
  have hPositive := pottsESShellMixedConstraint_probability_tendsto
    θ V hNest hExhaust μ hμ Positive GhostSites
  have hNegativeUnionSum : Tendsto
      (fun n => ∑ u ∈ Negative.powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          (νn n : Measure LatticeConfiguration).real (⋂ p ∈ u, B n p))
      atTop
      (𝓝 (∑ u ∈ Negative.powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) * μ.real (⋂ p ∈ u, BInf p))) := by
    refine tendsto_finsetSum _ (fun u hu => ?_)
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    have hShellEq (n : ℕ) :
        (⋂ p ∈ u, pottsESLatticeMixedConstraintEvent
          (V n) (Positive ∪ {p}) GhostSites) =
          pottsESLatticeMixedConstraintEvent (V n) (Positive ∪ u) GhostSites :=
      pottsESMixedPairIntersection_biInter_insert_union
        (V n) Positive u GhostSites hu.2
    have hInfEq :
        (⋂ p ∈ u, pottsESConnectionInfiniteConstraintEvent
          (Positive ∪ {p}) GhostSites) =
          pottsESConnectionInfiniteConstraintEvent (Positive ∪ u) GhostSites :=
      pottsESMixedConnectionIntersection_biInter_insert_union
        Positive u GhostSites hu.2
    have hJoint := pottsESShellMixedConstraint_probability_tendsto
      θ V hNest hExhaust μ hμ (Positive ∪ u) GhostSites
    have hTerm : Tendsto
        (fun n => (νn n : Measure LatticeConfiguration).real
          (⋂ p ∈ u, B n p)) atTop
        (𝓝 (μ.real (⋂ p ∈ u, BInf p))) := by
      have hSeq : (fun n => (νn n : Measure LatticeConfiguration).real
          (⋂ p ∈ u, B n p)) =ᶠ[atTop]
          fun n => (pottsESShellBondProbabilityMeasure θ (V n) :
              Measure LatticeConfiguration).real
            (pottsESLatticeMixedConstraintEvent
              (V n) (Positive ∪ u) GhostSites) := by
        filter_upwards with n
        rw [hShellEq n]
      have hJoint' := Tendsto.congr' hSeq.symm hJoint
      simpa only [BInf, hInfEq] using hJoint'
    simpa only [mul_comm] using
      (Filter.Tendsto.const_mul ((-1 : ℝ) ^ (u.card + 1)) hTerm)
  have hNegativeUnion : Tendsto
      (fun n => (νn n : Measure LatticeConfiguration).real
        (⋃ p ∈ Negative, B n p)) atTop
      (𝓝 (μ.real (⋃ p ∈ Negative, BInf p))) := by
    have hFormula (n : ℕ) :
        (νn n : Measure LatticeConfiguration).real (⋃ p ∈ Negative, B n p) =
          ∑ u ∈ Negative.powerset with u.Nonempty,
            (-1 : ℝ) ^ (u.card + 1) *
              (νn n : Measure LatticeConfiguration).real (⋂ p ∈ u, B n p) :=
      measureReal_biUnion_eq_sum_powerset
        (fun p hp => hBmeas n p) (by intro p hp; exact measure_ne_top _ _)
    have hFormulaInf : μ.real (⋃ p ∈ Negative, BInf p) =
          ∑ u ∈ Negative.powerset with u.Nonempty,
            (-1 : ℝ) ^ (u.card + 1) * μ.real (⋂ p ∈ u, BInf p) :=
      measureReal_biUnion_eq_sum_powerset
        (fun p hp => hBInfMeas p) (by intro p hp; exact measure_ne_top μ _)
    have hSum := Tendsto.congr' (Filter.Eventually.of_forall fun n =>
      (hFormula n).symm) hNegativeUnionSum
    simpa only [hFormulaInf] using hSum
  have hPatternDiff (n : ℕ) :
      (νn n : Measure LatticeConfiguration).real
        (pottsESLatticeMixedPairPatternEvent
          (V n) Positive Negative GhostSites) =
        (νn n : Measure LatticeConfiguration).real
            (pottsESLatticeMixedConstraintEvent
              (V n) Positive GhostSites) -
          (νn n : Measure LatticeConfiguration).real
            (⋃ p ∈ Negative, B n p) := by
    unfold pottsESLatticeMixedPairPatternEvent
    exact measureReal_sdiff (hBsubset n) (hUnionMeas n)
  have hPatternTargetDiff :
      μ.real (pottsESConnectionInfinitePairPatternEvent
        Positive Negative GhostSites) =
        μ.real (pottsESConnectionInfiniteConstraintEvent
            Positive GhostSites) - μ.real (⋃ p ∈ Negative, BInf p) := by
    unfold pottsESConnectionInfinitePairPatternEvent
    exact measureReal_sdiff hBInfSubset hUnionInfMeas
  have hDifference : Tendsto
      (fun n => (νn n : Measure LatticeConfiguration).real
          (pottsESLatticeMixedConstraintEvent
            (V n) Positive GhostSites) -
        (νn n : Measure LatticeConfiguration).real
          (⋃ p ∈ Negative, B n p))
      atTop
      (𝓝 (μ.real (pottsESConnectionInfiniteConstraintEvent
          Positive GhostSites) - μ.real (⋃ p ∈ Negative, BInf p))) :=
    hPositive.sub hNegativeUnion
  have hPattern : Tendsto
      (fun n => (νn n : Measure LatticeConfiguration).real
        (pottsESLatticeMixedPairPatternEvent
          (V n) Positive Negative GhostSites)) atTop
      (𝓝 (μ.real (pottsESConnectionInfinitePairPatternEvent
        Positive Negative GhostSites))) := by
    have hSeq : (fun n => (νn n : Measure LatticeConfiguration).real
        (pottsESLatticeMixedPairPatternEvent
          (V n) Positive Negative GhostSites)) =ᶠ[atTop]
        fun n => (νn n : Measure LatticeConfiguration).real
            (pottsESLatticeMixedConstraintEvent
              (V n) Positive GhostSites) -
          (νn n : Measure LatticeConfiguration).real
            (⋃ p ∈ Negative, B n p) := by
      filter_upwards with n
      exact hPatternDiff n
    have hDifference' := Tendsto.congr' hSeq.symm hDifference
    simpa only [hPatternTargetDiff] using hDifference'
  simpa only [νn] using hPattern

/-- Exact physical pair statuses jointly with positive wired-shell
memberships converge to the corresponding infinite-volume statuses. -/
theorem pottsESShellPairGhostPattern_probability_tendsto
    (θ : Parameters) (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    Tendsto
      (fun n => (pottsESShellBondProbabilityMeasure θ (V n) :
        Measure LatticeConfiguration).real
          (pottsESLatticePairGhostPatternEvent
            (V n) Positive Negative GhostSites))
      atTop (𝓝 (μ.real
        (pottsESConnectionInfinitePairGhostPatternEvent
          Positive Negative GhostSites))) := by
  have h := pottsESShellMixedPairPattern_probability_tendsto
    θ V hNest hExhaust μ hμ Positive Negative GhostSites
  simpa only [pottsESLatticeMixedPairPattern_eq_pairGhostPattern,
    pottsESConnectionMixedPairPattern_eq_pairGhostPattern] using h

end

end PottsContinuity.Thm1
