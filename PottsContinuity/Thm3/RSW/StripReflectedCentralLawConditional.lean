module

public import PottsContinuity.Thm3.RSW.StripReflectedCentralDualRead
public import PottsContinuity.Thm3.RSW.StripShiftedVerticalClip
public import PottsContinuity.Thm3.RSW.StripSymmetricSeeds

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance stripReflectedLawEdgeFintype (n k : ℕ) :
    Fintype (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).edgeSet := Fintype.ofFinite _
local instance stripReflectedLawPrimalEdgeFintype (n k : ℕ) :
    Fintype (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).edgeSet := Fintype.ofFinite _

/-- Every event of the literal reflected finite read is clopen in the strip. -/
theorem stripReflectedCentralDualConfiguration_event_isClopen
    (n k : ℕ) (hn : 1 ≤ n)
    (E : Set (Configuration (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)))) :
    IsClopen {ω | stripReflectedCentralDualConfiguration n k hn ω ∈ E} := by
  classical
  let f := embeddedEdgeEmbedding _ _ (stripReflectedCentralDualEmbedding n k hn)
    (stripReflectedCentralDual_map_le n k hn)
  apply strip_isClopen_of_finite_support n (Finset.univ.map f)
  intro ω η hagree
  have heq : stripReflectedCentralDualConfiguration n k hn ω =
      stripReflectedCentralDualConfiguration n k hn η := by
    unfold stripReflectedCentralDualConfiguration
    congr 1
    funext e
    exact hagree (f e) (Finset.mem_map.mpr ⟨e,Finset.mem_univ _,rfl⟩)
  change stripReflectedCentralDualConfiguration n k hn ω ∈ E ↔
    stripReflectedCentralDualConfiguration n k hn η ∈ E
  rw [heq]

/-- Complementing the actual finite central read still depends on finitely
many original strip bonds. -/
theorem stripCentralDualConfiguration_event_isClopen
    (n k : ℕ)
    (E : Set (Configuration (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)))) :
    IsClopen {ω | stripCentralDualConfiguration n k ω ∈ E} := by
  classical
  let f := embeddedEdgeEmbedding _ _ (stripCentralRectangleEmbedding n k)
    (stripCentralRectangle_map_le n k)
  apply strip_isClopen_of_finite_support n (Finset.univ.map f)
  intro ω η hagree
  have heq : stripCentralRectangleConfiguration n k ω = stripCentralRectangleConfiguration n k η := by
    unfold stripCentralRectangleConfiguration
    congr 1
    funext e
    exact hagree (f e) (Finset.mem_map.mpr ⟨e,Finset.mem_univ _,rfl⟩)
  change rectanglePrimalDualConfigurationEquiv _ _ _ (stripCentralRectangleConfiguration n k ω) ∈ E ↔
    rectanglePrimalDualConfigurationEquiv _ _ _ (stripCentralRectangleConfiguration n k η) ∈ E
  rw [heq]

/-- The source primal vertical bound in the small-horizontal branch,
conditional on the exact finite reflected-dual marginal and port-walk
transport. No probability bound is assumed for either event. -/
theorem selfDual_stripCentral_vertical_lower_of_reflectedDualLaw_and_crossingTransport
    (q : Set.Ici (1:ℝ)) (k n : ℕ) (hn : 1 ≤ n)
    (hlaw : Measure.map (stripCentralDualConfiguration n k) (selfDualStripMeasure q n) =
      Measure.map (stripReflectedCentralDualConfiguration n k hn) (selfDualStripMeasure q n))
    (htransport : {ω | stripReflectedCentralDualConfiguration n k hn ω ∈
      rectangleDualBottomTopCrossingEvent (-(k:ℤ)*n,0) (2*k*n) (2*n)} ⊆
      stripConfinedConnection n
        (stripRectangleVertices n (-(k:ℤ)*n) ((k:ℤ)*n-1) (-1) (2*n))
        {u | u.val.2 = -1} {v | v.val.2 = 2*n})
    (hsmall : selfDualStripHorizontalProbability q k n < 1/2) :
    (1/2:ℝ) ≤ (selfDualStripMeasure q n).real
      (stripVerticalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) (2*n)) := by
  have hleft : Measurable (stripCentralDualConfiguration n k) :=
    fun E _ => (stripCentralDualConfiguration_event_isClopen n k E).isOpen.measurableSet
  have hright : Measurable (stripReflectedCentralDualConfiguration n k hn) :=
    fun E _ => (stripReflectedCentralDualConfiguration_event_isClopen n k hn E).isOpen.measurableSet
  have heq := congrArg (fun μ => (μ
    (rectangleDualBottomTopCrossingEvent (-(k:ℤ)*n,0) (2*k*n) (2*n))).toReal) hlaw
  rw [Measure.map_apply hleft MeasurableSpace.measurableSet_top,
    Measure.map_apply hright MeasurableSpace.measurableSet_top] at heq
  have hlow := selfDual_stripCentral_dual_vertical_lower_of_small_horizontal q k n hsmall
  change (selfDualStripMeasure q n).real {ω | stripCentralDualConfiguration n k ω ∈
    rectangleDualBottomTopCrossingEvent (-(k:ℤ)*n,0) (2*k*n) (2*n)} =
    (selfDualStripMeasure q n).real {ω | stripReflectedCentralDualConfiguration n k hn ω ∈
    rectangleDualBottomTopCrossingEvent (-(k:ℤ)*n,0) (2*k*n) (2*n)} at heq
  rw [heq] at hlow
  apply hlow.trans
  exact measureReal_mono (h₂ := measure_ne_top _ _)
    (htransport.trans (strip_shifted_vertical_subset_central n k))

end
end PottsContinuity.RSW
