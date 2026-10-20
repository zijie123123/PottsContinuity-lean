-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxSplitConnectionLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitQuotientLaw
public import PottsContinuity.FKC.FiniteFK.SlitBoxGhostConnectionLaw
public import PottsContinuity.FKC.FiniteFK.WiredArcComponent
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

private theorem slitBoxSplitGhostMap_base (n : ℕ)
    (x : SlitBoxSplitCoverVertex n) :
    slitBoxSplitGhostMap n x =
      slitBoxGhostMap n (slitBoxSplitBaseVertex n x) := by
  cases x with
  | inl u =>
      simp [slitBoxSplitBaseVertex, slitBoxGhostMap,
        slitBoxSplitGhostMap, wiredVertexMap, u.2]
  | inr v =>
      simp [slitBoxSplitBaseVertex, slitBoxGhostMap,
        slitBoxSplitGhostMap, wiredVertexMap]

private theorem slitBoxSplitGhostConnection_preimage (n : ℕ)
    (x : SlitBoxSplitCoverVertex n) :
    (fun A : Configuration (slitBoxSplitCoverGraph n) =>
      A.map (slitBoxSplitGhostEdgeEquiv n).toEmbedding) ⁻¹'
        {B | ActualConnected (slitBoxGhostGraph n) B
          (slitBoxSplitGhostMap n x) none} =
      {A | ∃ y ∈ slitBoxSplitCoverBoundary n,
        ActualConnected (slitBoxSplitCoverGraph n) A x y} := by
  classical
  obtain ⟨v₀, hv₀⟩ := slitBoxSplitCoverBoundary_nonempty n
  have hnone : slitBoxSplitGhostMap n v₀ = none :=
    (slitBoxSplitGhostMap_eq_none_iff_boundary n v₀).2 hv₀
  ext A
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  let ξ := BoundaryCondition.wired (slitBoxSplitCoverBoundary n)
  have hquot := wiredVertexQuotient_componentSetoid_rel_iff
    (slitBoxSplitGhostMap n) (slitBoxSplitGhostMap_surjective n)
    (slitBoxSplitGhostEdgeEquiv n) (slitBoxSplitGhostEdgeEquiv_val n)
    ξ (slitBoxSplitBoundary_partition_eq_ker_commonGhostMap n) A x v₀
  have harc := wired_componentSetoid_rel_iff_exists_actualConnected
    (slitBoxSplitCoverGraph n) A (slitBoxSplitCoverBoundary n)
    (u := x) (v := v₀) hv₀
  constructor
  · intro h
    rw [← hnone] at h
    exact harc.mp (hquot.mpr h)
  · intro h
    rw [← hnone]
    exact hquot.mp (harc.mpr h)

theorem slitBoxSplitWiredArcConnection_measure_eq
    (n : ℕ) (q : ClusterWeight) (x : SlitBoxSplitCoverVertex n) :
    measure (slitBoxSplitCoverGraph n) q
        (BoundaryCondition.wired (slitBoxSplitCoverBoundary n))
        {A | ∃ y ∈ slitBoxSplitCoverBoundary n,
          ActualConnected (slitBoxSplitCoverGraph n) A x y} =
      measure (slitBoxGraph n) q (slitBoxBoundary n)
        (slitBoxWiredArcConnectionEvent n (slitBoxSplitBaseVertex n x)) := by
  classical
  let f : Configuration (slitBoxSplitCoverGraph n) →
      Configuration (slitBoxGhostGraph n) :=
    fun A => A.map (slitBoxSplitGhostEdgeEquiv n).toEmbedding
  let ghostEvent : Set (Configuration (slitBoxGhostGraph n)) :=
    {B | ActualConnected (slitBoxGhostGraph n) B
      (slitBoxSplitGhostMap n x) none}
  let : MeasurableSpace (Configuration (slitBoxSplitCoverGraph n)) := ⊤
  let : MeasurableSpace (Configuration (slitBoxGhostGraph n)) := ⊤
  have hf : Measurable f := by
    intro s hs
    exact MeasurableSpace.measurableSet_top
  have hsplit := congrArg
    (fun μ : PMF (Configuration (slitBoxGhostGraph n)) =>
      μ.toMeasure ghostEvent) (slitBoxSplitLaw_map_ghost n q)
  rw [PMF.toMeasure_map_apply _ _ _ hf MeasurableSpace.measurableSet_top] at hsplit
  rw [slitBoxSplitGhostConnection_preimage] at hsplit
  have hsplitMeasure :
      measure (slitBoxSplitCoverGraph n) q
          (BoundaryCondition.wired (slitBoxSplitCoverBoundary n))
          {A | ∃ y ∈ slitBoxSplitCoverBoundary n,
            ActualConnected (slitBoxSplitCoverGraph n) A x y} =
        measure (slitBoxGhostGraph n) q
          (BoundaryCondition.free (∅ : Set (slitBoxGhostCarrier n))) ghostEvent := by
    simpa [f, ghostEvent, measure] using hsplit
  calc
    measure (slitBoxSplitCoverGraph n) q
        (BoundaryCondition.wired (slitBoxSplitCoverBoundary n))
        {A | ∃ y ∈ slitBoxSplitCoverBoundary n,
          ActualConnected (slitBoxSplitCoverGraph n) A x y} =
      measure (slitBoxGhostGraph n) q
        (BoundaryCondition.free (∅ : Set (slitBoxGhostCarrier n))) ghostEvent :=
          hsplitMeasure
    _ = measure (slitBoxGhostGraph n) q
        (BoundaryCondition.free (∅ : Set (slitBoxGhostCarrier n)))
        (slitBoxGhostConnectionEvent n (slitBoxSplitBaseVertex n x)) := by
          congr 1
          ext B
          simp [ghostEvent, slitBoxGhostConnectionEvent,
            slitBoxSplitGhostMap_base]
    _ = measure (slitBoxGraph n) q (slitBoxBoundary n)
        (slitBoxWiredArcConnectionEvent n (slitBoxSplitBaseVertex n x)) :=
          (slitBoxWiredArcConnectionEvent_measure_eq_ghost n q
            (slitBoxSplitBaseVertex n x)).symm

end
end PottsContinuity.FKC.FiniteFK
