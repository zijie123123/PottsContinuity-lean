module

public import PottsContinuity.Thm1.ShellMixedPatterns

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

/-- A complete finite status signature: exact pair statuses and both positive
and negative membership in the shell's wired class. -/
def pottsESLatticeFullSignatureEvent (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostPositive GhostNegative : Finset (ℤ × ℤ)) : Set LatticeConfiguration :=
  pottsESLatticePairGhostPatternEvent V Positive Negative GhostPositive \
    (⋃ x ∈ GhostNegative,
      pottsESLatticePairGhostPatternEvent V Positive Negative
        (GhostPositive ∪ {x}))

/-- The limiting complete signature records infinite-cluster membership and
its complement at the marked sites. -/
def pottsESConnectionInfiniteFullSignatureEvent
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostPositive GhostNegative : Finset (ℤ × ℤ)) : Set LatticeConfiguration :=
  pottsESConnectionInfinitePairGhostPatternEvent
      Positive Negative GhostPositive \
    (⋃ x ∈ GhostNegative,
      pottsESConnectionInfinitePairGhostPatternEvent
        Positive Negative (GhostPositive ∪ {x}))

private theorem pottsESLatticePairGhost_iInter_insert_union
    (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostPositive Ghosts : Finset (ℤ × ℤ)) (hGhosts : Ghosts.Nonempty) :
    (⋂ x ∈ Ghosts,
      pottsESLatticePairGhostPatternEvent V Positive Negative
        (GhostPositive ∪ {x})) =
      pottsESLatticePairGhostPatternEvent V Positive Negative
        (GhostPositive ∪ Ghosts) := by
  ext ω
  simp only [pottsESLatticePairGhostPatternEvent, Set.mem_inter_iff,
    Set.mem_iInter]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := hGhosts
    refine ⟨(h x hx).1, ?_⟩
    intro y hy
    rcases Finset.mem_union.mp hy with hyPos | hyGhost
    · exact (h x hx).2 y (Finset.mem_union_left _ hyPos)
    · exact (h y hyGhost).2 y
        (Finset.mem_union_right _ (Finset.mem_singleton_self y))
  · rintro ⟨hPairs, hGhost⟩ x hx
    refine ⟨hPairs, ?_⟩
    intro y hy
    rcases Finset.mem_union.mp hy with hyPos | hyX
    · exact hGhost y (Finset.mem_union_left _ hyPos)
    · have hyEq : y = x := Finset.mem_singleton.mp hyX
      subst y
      exact hGhost x (Finset.mem_union_right _ hx)

private theorem pottsESConnectionPairGhost_iInter_insert_union
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostPositive Ghosts : Finset (ℤ × ℤ)) (hGhosts : Ghosts.Nonempty) :
    (⋂ x ∈ Ghosts,
      pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
        (GhostPositive ∪ {x})) =
      pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
        (GhostPositive ∪ Ghosts) := by
  ext ω
  simp only [pottsESConnectionInfinitePairGhostPatternEvent,
    Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := hGhosts
    refine ⟨(h x hx).1, ?_⟩
    intro y hy
    rcases Finset.mem_union.mp hy with hyPos | hyGhost
    · exact (h x hx).2 y (Finset.mem_union_left _ hyPos)
    · exact (h y hyGhost).2 y
        (Finset.mem_union_right _ (Finset.mem_singleton_self y))
  · rintro ⟨hPairs, hGhost⟩ x hx
    refine ⟨hPairs, ?_⟩
    intro y hy
    rcases Finset.mem_union.mp hy with hyPos | hyX
    · exact hGhost y (Finset.mem_union_left _ hyPos)
    · have hyEq : y = x := Finset.mem_singleton.mp hyX
      subst y
      exact hGhost x (Finset.mem_union_right _ hx)

private theorem pottsESFullExit_measurable
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

private theorem pottsESFullPair_measurable
    (V : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) :
    MeasurableSet (pottsESLatticePairRelationEvent V x y) := by
  rw [pottsESLatticePairRelationEvent]
  exact (measurableSet_open_reachable x y).union
    ((pottsESFullExit_measurable V x).inter
      (pottsESFullExit_measurable V y))

private theorem pottsESFullPairIntersection_measurable
    (V : Finset (ℤ × ℤ))
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    MeasurableSet (pottsESLatticePairIntersectionEvent V Pairs) := by
  change MeasurableSet (⋂ p ∈ Pairs,
    pottsESLatticePairRelationEvent V p.1 p.2)
  exact Pairs.measurableSet_biInter fun p hp =>
    pottsESFullPair_measurable V p.1 p.2

private theorem pottsESFullPairPattern_measurable
    (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    MeasurableSet (pottsESLatticePairPatternEvent V Positive Negative) := by
  rw [pottsESLatticePairPatternEvent]
  apply (pottsESFullPairIntersection_measurable V Positive).diff
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro hp
  exact pottsESFullPairIntersection_measurable V (Positive ∪ {p})

private theorem pottsESFullPairGhost_measurable
    (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    MeasurableSet
      (pottsESLatticePairGhostPatternEvent V Positive Negative GhostSites) := by
  rw [pottsESLatticePairGhostPatternEvent]
  exact (pottsESFullPairPattern_measurable V Positive Negative).inter
    (GhostSites.measurableSet_biInter fun x hx =>
      pottsESFullExit_measurable V x)

private theorem pottsESFullPairConnection_measurable
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    MeasurableSet (pottsESConnectionIntersectionEvent Pairs) := by
  change MeasurableSet (⋂ p ∈ Pairs, connectionEvent p.1 p.2)
  exact Pairs.measurableSet_biInter fun p hp =>
    connectionEvent_isMeasurableSet p.1 p.2

private theorem pottsESFullConnectionPattern_measurable
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    MeasurableSet (pottsESConnectionPairPatternEvent Positive Negative) := by
  rw [pottsESConnectionPairPatternEvent]
  apply (pottsESFullPairConnection_measurable Positive).diff
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro hp
  exact pottsESFullPairConnection_measurable (Positive ∪ {p})

private theorem pottsESFullPairConnectionGhost_measurable
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    MeasurableSet
      (pottsESConnectionInfinitePairGhostPatternEvent
        Positive Negative GhostSites) := by
  rw [pottsESConnectionInfinitePairGhostPatternEvent]
  exact (pottsESFullConnectionPattern_measurable Positive Negative).inter
    (GhostSites.measurableSet_biInter fun x hx => measurableSet_infiniteAt x)

private theorem pottsESLatticePairGhost_antitone_ghost
    {V : Finset (ℤ × ℤ)} {GhostSmall GhostLarge : Finset (ℤ × ℤ)}
    (hSub : GhostSmall ⊆ GhostLarge)
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    pottsESLatticePairGhostPatternEvent V Positive Negative GhostLarge ⊆
      pottsESLatticePairGhostPatternEvent V Positive Negative GhostSmall := by
  intro ω hω
  simp only [pottsESLatticePairGhostPatternEvent, Set.mem_inter_iff,
    Set.mem_iInter] at hω ⊢
  exact ⟨hω.1, fun x hx => hω.2 x (hSub hx)⟩

private theorem pottsESConnectionPairGhost_antitone_ghost
    {GhostSmall GhostLarge : Finset (ℤ × ℤ)}
    (hSub : GhostSmall ⊆ GhostLarge)
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    pottsESConnectionInfinitePairGhostPatternEvent
        Positive Negative GhostLarge ⊆
      pottsESConnectionInfinitePairGhostPatternEvent
        Positive Negative GhostSmall := by
  intro ω hω
  simp only [pottsESConnectionInfinitePairGhostPatternEvent,
    Set.mem_inter_iff, Set.mem_iInter] at hω ⊢
  exact ⟨hω.1, fun x hx => hω.2 x (hSub hx)⟩

/-- Every exact finite pair-and-ghost signature probability converges along a
nested exhaustive shell sequence to its wired-limit event probability. -/
theorem pottsESShellFullSignature_probability_tendsto
    (θ : Parameters) (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostPositive GhostNegative : Finset (ℤ × ℤ)) :
    Tendsto
      (fun n => (pottsESShellBondProbabilityMeasure θ (V n) :
        Measure LatticeConfiguration).real
          (pottsESLatticeFullSignatureEvent (V n) Positive Negative
            GhostPositive GhostNegative))
      atTop (𝓝 (μ.real
        (pottsESConnectionInfiniteFullSignatureEvent Positive Negative
          GhostPositive GhostNegative))) := by
  classical
  let : IsProbabilityMeasure μ := hμ.1
  let νn : ℕ → ProbabilityMeasure LatticeConfiguration :=
    fun n => pottsESShellBondProbabilityMeasure θ (V n)
  let B : ℕ → (ℤ × ℤ) → Set LatticeConfiguration :=
    fun n x => pottsESLatticePairGhostPatternEvent (V n) Positive Negative
      (GhostPositive ∪ {x})
  have hBmeas (n : ℕ) (x : ℤ × ℤ) : MeasurableSet (B n x) := by
    exact pottsESFullPairGhost_measurable (V n) (Positive) (Negative)
      (GhostPositive ∪ {x})
  have hBInfMeas (x : ℤ × ℤ) : MeasurableSet
      (pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
        (GhostPositive ∪ {x})) :=
    pottsESFullPairConnectionGhost_measurable Positive Negative
      (GhostPositive ∪ {x})
  have hUnionMeas (n : ℕ) : MeasurableSet
      (⋃ x ∈ GhostNegative, B n x) := by
    apply MeasurableSet.iUnion
    intro x
    apply MeasurableSet.iUnion
    intro hx
    exact hBmeas n x
  have hUnionInfMeas : MeasurableSet
      (⋃ x ∈ GhostNegative,
        pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
          (GhostPositive ∪ {x})) := by
    apply MeasurableSet.iUnion
    intro x
    apply MeasurableSet.iUnion
    intro hx
    exact hBInfMeas x
  have hBsubset (n : ℕ) : (⋃ x ∈ GhostNegative, B n x) ⊆
      pottsESLatticePairGhostPatternEvent (V n) Positive Negative GhostPositive := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω
    rcases hω with ⟨x, hx, hxω⟩
    exact pottsESLatticePairGhost_antitone_ghost
      (Finset.subset_union_left) Positive Negative hxω
  have hBInfSubset : (⋃ x ∈ GhostNegative,
      pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
        (GhostPositive ∪ {x})) ⊆
      pottsESConnectionInfinitePairGhostPatternEvent
        Positive Negative GhostPositive := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω
    rcases hω with ⟨x, hx, hxω⟩
    exact pottsESConnectionPairGhost_antitone_ghost
      (Finset.subset_union_left) Positive Negative hxω
  have hPositive := pottsESShellPairGhostPattern_probability_tendsto
    θ V hNest hExhaust μ hμ Positive Negative GhostPositive
  have hUnionSum : Tendsto
      (fun n => ∑ u ∈ GhostNegative.powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          (νn n : Measure LatticeConfiguration).real (⋂ x ∈ u, B n x))
      atTop
      (𝓝 (∑ u ∈ GhostNegative.powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) * μ.real
          (⋂ x ∈ u,
            pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
              (GhostPositive ∪ {x})))) := by
    refine tendsto_finsetSum _ (fun u hu => ?_)
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    have hShellEq (n : ℕ) :
        (⋂ x ∈ u, pottsESLatticePairGhostPatternEvent (V n) Positive Negative
          (GhostPositive ∪ {x})) =
          pottsESLatticePairGhostPatternEvent (V n) Positive Negative
            (GhostPositive ∪ u) :=
      pottsESLatticePairGhost_iInter_insert_union (V n) Positive Negative
        GhostPositive u hu.2
    have hInfEq :
        (⋂ x ∈ u,
          pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
            (GhostPositive ∪ {x})) =
          pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
            (GhostPositive ∪ u) :=
      pottsESConnectionPairGhost_iInter_insert_union Positive Negative
        GhostPositive u hu.2
    have hJoint := pottsESShellPairGhostPattern_probability_tendsto
      θ V hNest hExhaust μ hμ Positive Negative (GhostPositive ∪ u)
    have hTerm : Tendsto
        (fun n => (νn n : Measure LatticeConfiguration).real
          (⋂ x ∈ u, B n x)) atTop
        (𝓝 (μ.real (⋂ x ∈ u,
          pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
            (GhostPositive ∪ {x})))) := by
      have hSeq : (fun n => (νn n : Measure LatticeConfiguration).real
          (⋂ x ∈ u, B n x)) =ᶠ[atTop]
          fun n => (pottsESShellBondProbabilityMeasure θ (V n) :
              Measure LatticeConfiguration).real
            (pottsESLatticePairGhostPatternEvent (V n) Positive Negative
              (GhostPositive ∪ u)) := by
        filter_upwards with n
        rw [hShellEq n]
      have hJoint' := Tendsto.congr' hSeq.symm hJoint
      simpa only [hInfEq] using hJoint'
    simpa only [mul_comm] using
      (Filter.Tendsto.const_mul ((-1 : ℝ) ^ (u.card + 1)) hTerm)
  have hUnion : Tendsto
      (fun n => (νn n : Measure LatticeConfiguration).real
        (⋃ x ∈ GhostNegative, B n x)) atTop
      (𝓝 (μ.real (⋃ x ∈ GhostNegative,
        pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
          (GhostPositive ∪ {x})))) := by
    have hFormula (n : ℕ) :
        (νn n : Measure LatticeConfiguration).real (⋃ x ∈ GhostNegative, B n x) =
          ∑ u ∈ GhostNegative.powerset with u.Nonempty,
            (-1 : ℝ) ^ (u.card + 1) *
              (νn n : Measure LatticeConfiguration).real (⋂ x ∈ u, B n x) :=
      measureReal_biUnion_eq_sum_powerset
        (fun x hx => hBmeas n x) (by intro x hx; exact measure_ne_top _ _)
    have hFormulaInf : μ.real (⋃ x ∈ GhostNegative,
        pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
          (GhostPositive ∪ {x})) =
          ∑ u ∈ GhostNegative.powerset with u.Nonempty,
            (-1 : ℝ) ^ (u.card + 1) * μ.real
              (⋂ x ∈ u,
                pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
                  (GhostPositive ∪ {x})) :=
      measureReal_biUnion_eq_sum_powerset
        (fun x hx => hBInfMeas x) (by intro x hx; exact measure_ne_top μ _)
    have hSum := Tendsto.congr' (Filter.Eventually.of_forall fun n =>
      (hFormula n).symm) hUnionSum
    simpa only [hFormulaInf] using hSum
  have hPatternDiff (n : ℕ) :
      (νn n : Measure LatticeConfiguration).real
        (pottsESLatticeFullSignatureEvent (V n) Positive Negative
          GhostPositive GhostNegative) =
        (νn n : Measure LatticeConfiguration).real
            (pottsESLatticePairGhostPatternEvent (V n) Positive Negative GhostPositive) -
          (νn n : Measure LatticeConfiguration).real
            (⋃ x ∈ GhostNegative, B n x) := by
    unfold pottsESLatticeFullSignatureEvent
    exact measureReal_sdiff (hBsubset n) (hUnionMeas n)
  have hTargetDiff :
      μ.real (pottsESConnectionInfiniteFullSignatureEvent Positive Negative
          GhostPositive GhostNegative) =
        μ.real (pottsESConnectionInfinitePairGhostPatternEvent
            Positive Negative GhostPositive) -
          μ.real (⋃ x ∈ GhostNegative,
            pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
              (GhostPositive ∪ {x})) := by
    unfold pottsESConnectionInfiniteFullSignatureEvent
    exact measureReal_sdiff hBInfSubset hUnionInfMeas
  have hDifference : Tendsto
      (fun n => (νn n : Measure LatticeConfiguration).real
          (pottsESLatticePairGhostPatternEvent (V n) Positive Negative GhostPositive) -
        (νn n : Measure LatticeConfiguration).real
          (⋃ x ∈ GhostNegative, B n x))
      atTop
      (𝓝 (μ.real (pottsESConnectionInfinitePairGhostPatternEvent
          Positive Negative GhostPositive) -
        μ.real (⋃ x ∈ GhostNegative,
          pottsESConnectionInfinitePairGhostPatternEvent Positive Negative
            (GhostPositive ∪ {x})))) := hPositive.sub hUnion
  have hPattern : Tendsto
      (fun n => (νn n : Measure LatticeConfiguration).real
        (pottsESLatticeFullSignatureEvent (V n) Positive Negative
          GhostPositive GhostNegative)) atTop
      (𝓝 (μ.real (pottsESConnectionInfiniteFullSignatureEvent Positive Negative
        GhostPositive GhostNegative))) := by
    have hSeq : (fun n => (νn n : Measure LatticeConfiguration).real
        (pottsESLatticeFullSignatureEvent (V n) Positive Negative
          GhostPositive GhostNegative)) =ᶠ[atTop]
        fun n => (νn n : Measure LatticeConfiguration).real
            (pottsESLatticePairGhostPatternEvent (V n) Positive Negative GhostPositive) -
          (νn n : Measure LatticeConfiguration).real
            (⋃ x ∈ GhostNegative, B n x) := by
      filter_upwards with n
      exact hPatternDiff n
    have hDifference' := Tendsto.congr' hSeq.symm hDifference
    simpa only [hTargetDiff] using hDifference'
  simpa only [νn] using hPattern

end

end PottsContinuity.Thm1
