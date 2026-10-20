-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripTopCylinders.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleLaw
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopBoundary
public import PottsContinuity.FKC.FiniteFK.Expectation

@[expose] public section

open MeasureTheory

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open FiniteProbability
open scoped BigOperators

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance horizontalStripTopCylinderEdgeFintype (M n : ℕ) :
    Fintype (horizontalStripCutRectangle M n).edgeSet := Fintype.ofFinite _
local instance horizontalStripTopCylinderEdgeDecidableEq (M n : ℕ) :
    DecidableEq (horizontalStripCutRectangle M n).edgeSet := Classical.decEq _

/-- The finite all-open event read from the actual original lattice edges of
the strip rectangle. -/
def horizontalStripRectangleCylinderEvent (M n : ℕ)
    (F : Finset squareLattice.edgeSet) :
    Set (Configuration (horizontalStripCutRectangle M n)) :=
  {A | F ⊆ A.image (horizontalStripRectangleOriginalEdge M n)}

theorem horizontalStripRectangleProbabilityMeasure_allOpen
    (q : ClusterWeight) (M n : ℕ)
    (ξ : BoundaryCondition (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)))
    (F : Finset squareLattice.edgeSet) :
    (horizontalStripRectangleProbabilityMeasure q M n ξ : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) =
      measure (horizontalStripCutRectangle M n) q ξ
        (horizontalStripRectangleCylinderEvent M n F) := by
  rw [horizontalStripRectangleProbabilityMeasure_apply_preimage q M n ξ
    (LatticeConfiguration.allOpen F)
    (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  congr 1
  ext A
  simp only [LatticeConfiguration.allOpen, Set.mem_ofPred_eq,
    horizontalStripRectangleCylinderEvent, Finset.subset_iff,
    horizontalStripRectanglePlaneExtension]
  simp only [decide_eq_true_eq]

private theorem horizontalStripRectangleCylinderEvent_upper (M n : ℕ)
    (F : Finset squareLattice.edgeSet) :
    IsUpperSet (horizontalStripRectangleCylinderEvent M n F) := by
  intro A B hAB hA
  exact hA.trans (Finset.image_mono _ hAB)

private theorem horizontalStripRectangleCylinderIndicator_nonneg (M n : ℕ)
    (F : Finset squareLattice.edgeSet) (A : Configuration (horizontalStripCutRectangle M n)) :
    0 ≤ (horizontalStripRectangleCylinderEvent M n F).indicator (fun _ => (1 : ℝ)) A := by
  by_cases h : A ∈ horizontalStripRectangleCylinderEvent M n F <;>
    simp [Set.indicator, h]

private theorem horizontalStripRectangleCylinderIndicator_mono (M n : ℕ)
    (F : Finset squareLattice.edgeSet) :
    Monotone ((horizontalStripRectangleCylinderEvent M n F).indicator (fun _ => (1 : ℝ))) := by
  intro A B hAB
  by_cases hA : A ∈ horizontalStripRectangleCylinderEvent M n F
  · have hB := horizontalStripRectangleCylinderEvent_upper M n F hAB hA
    simp [Set.indicator, hA, hB]
  · simp only [Set.indicator_of_notMem hA]
    exact horizontalStripRectangleCylinderIndicator_nonneg M n F B

private theorem horizontalStripRectangleCylinder_toReal_eq_expectation
    (q : ClusterWeight) (M n : ℕ)
    (ξ : BoundaryCondition (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)))
    (F : Finset squareLattice.edgeSet) :
    ((measure (horizontalStripCutRectangle M n) q ξ
      (horizontalStripRectangleCylinderEvent M n F)).toReal) =
      expectation (law (horizontalStripCutRectangle M n) q ξ)
        ((horizontalStripRectangleCylinderEvent M n F).indicator (fun _ => (1 : ℝ))) := by
  rw [measure_toReal_eq_indicator_sum]
  unfold expectation
  apply Finset.sum_congr rfl
  intro A hA
  have hp := configurationProbability_pos (horizontalStripCutRectangle M n) q ξ A
  simp only [law_apply, ENNReal.toReal_ofReal hp.le]

private theorem horizontalStripRectangleOriginalEdge_compatible
    {M N n : ℕ} (hMN : M ≤ N)
    (hGH : (horizontalStripCutRectangle M n).map
      (horizontalStripRectangleEmbedding (n := n) hMN) ≤ horizontalStripCutRectangle N n)
    (e : (horizontalStripCutRectangle M n).edgeSet) :
    horizontalStripRectangleOriginalEdge N n
        (embeddedEdgeEmbedding (horizontalStripCutRectangle M n)
          (horizontalStripCutRectangle N n)
          (horizontalStripRectangleEmbedding (n := n) hMN) hGH e) =
      horizontalStripRectangleOriginalEdge M n e := by
  apply Subtype.ext
  change Sym2.map (fun v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => v.val)
      (Sym2.map (horizontalStripRectangleEmbedding (n := n) hMN) e.val) =
    Sym2.map (fun v : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n) => v.val) e.val
  rw [Sym2.map_map]
  congr 1

private theorem horizontalStripRectangleCylinder_restrict_iff
    {M N n : ℕ} (hMN : M ≤ N)
    (hGH : (horizontalStripCutRectangle M n).map
      (horizontalStripRectangleEmbedding (n := n) hMN) ≤ horizontalStripCutRectangle N n)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge M n))
    (A : Configuration (horizontalStripCutRectangle N n)) :
    A ∈ horizontalStripRectangleCylinderEvent N n F ↔
      embeddedConfigurationRestriction (horizontalStripCutRectangle M n)
        (horizontalStripCutRectangle N n)
        (horizontalStripRectangleEmbedding (n := n) hMN) hGH A ∈
          horizontalStripRectangleCylinderEvent M n F := by
  constructor
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    have heOpen : e ∈ A.image (horizontalStripRectangleOriginalEdge N n) := hA he
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp heOpen
    have hcompat := horizontalStripRectangleOriginalEdge_compatible hMN hGH x
    have hyx : embeddedEdgeEmbedding (horizontalStripCutRectangle M n)
        (horizontalStripCutRectangle N n)
        (horizontalStripRectangleEmbedding (n := n) hMN) hGH x = y := by
      apply horizontalStripRectangleOriginalEdge_injective N n
      calc
        horizontalStripRectangleOriginalEdge N n
            (embeddedEdgeEmbedding (horizontalStripCutRectangle M n)
              (horizontalStripCutRectangle N n)
              (horizontalStripRectangleEmbedding (n := n) hMN) hGH x) =
            horizontalStripRectangleOriginalEdge M n x := hcompat
        _ = e := hx
        _ = horizontalStripRectangleOriginalEdge N n y := hye.symm
    have hy' : embeddedEdgeEmbedding (horizontalStripCutRectangle M n)
        (horizontalStripCutRectangle N n)
        (horizontalStripRectangleEmbedding (n := n) hMN) hGH x ∈ A := by
      rw [hyx]
      exact hy
    have hrestrict := (mem_embeddedConfigurationRestriction _ _ _ _ A x).mpr hy'
    exact Finset.mem_image.mpr ⟨x, hrestrict, hx⟩
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    have heOpen : e ∈
        (embeddedConfigurationRestriction (horizontalStripCutRectangle M n)
          (horizontalStripCutRectangle N n)
          (horizontalStripRectangleEmbedding (n := n) hMN) hGH A).image
            (horizontalStripRectangleOriginalEdge M n) := hA he
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp heOpen
    have hyx : y = x :=
      horizontalStripRectangleOriginalEdge_injective M n (hye.trans hx.symm)
    have hrestrict : x ∈ embeddedConfigurationRestriction (horizontalStripCutRectangle M n)
        (horizontalStripCutRectangle N n)
        (horizontalStripRectangleEmbedding (n := n) hMN) hGH A := by
      rw [← hyx]
      exact hy
    have hy' := (mem_embeddedConfigurationRestriction _ _ _ _ A x).mp hrestrict
    have hcompat := horizontalStripRectangleOriginalEdge_compatible hMN hGH x
    exact Finset.mem_image.mpr ⟨embeddedEdgeEmbedding (horizontalStripCutRectangle M n)
      (horizontalStripCutRectangle N n)
      (horizontalStripRectangleEmbedding (n := n) hMN) hGH x, hy', hcompat.trans hx⟩

/-- All-open cylinder probabilities are monotone for the finite top-wired
strip rectangles. Cylinders using an edge outside the smaller rectangle have
zero probability there because the whole-plane extension closes that edge. -/
theorem horizontalStripRectangleProbabilityMeasure_allOpen_topWired_mono
    (q : ClusterWeight) (n M N : ℕ) (hMN : M ≤ N)
    (F : Finset squareLattice.edgeSet) :
    (horizontalStripRectangleProbabilityMeasure q M n
      (horizontalStripTopWiredBoundary M n) : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) ≤
    (horizontalStripRectangleProbabilityMeasure q N n
      (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) := by
  let G := horizontalStripCutRectangle M n
  let H := horizontalStripCutRectangle N n
  let f := horizontalStripRectangleEmbedding (n := n) hMN
  have hGH : G.map f ≤ H := by
    change (rectangleGraph (-(M : ℤ), 0) (2 * M) (2 * n)).map
        (horizontalStripRectangleEmbedding (n := n) hMN) ≤
      rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)
    exact horizontalStripRectangle_map_le (n := n) hMN
  by_cases hF : ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge M n)
  · let S := horizontalStripRectangleCylinderEvent M n F
    let T := horizontalStripRectangleCylinderEvent N n F
    have hleft := horizontalStripRectangleProbabilityMeasure_allOpen q M n
      (horizontalStripTopWiredBoundary M n) F
    have hright := horizontalStripRectangleProbabilityMeasure_allOpen q N n
      (horizontalStripTopWiredBoundary N n) F
    have hcmp := horizontalStripTopWired_expectation_mono (n := n) hMN q
      (S.indicator (fun _ => (1 : ℝ)))
      (fun A => horizontalStripRectangleCylinderIndicator_nonneg M n F A)
      (by
        intro A B hAB
        exact horizontalStripRectangleCylinderIndicator_mono M n F hAB)
    have hrestrict := horizontalStripRectangleCylinder_restrict_iff hMN hGH F hF
    have hlarge :
        expectation (law H q (horizontalStripTopWiredBoundary N n))
          (fun A => (S.indicator (fun _ => (1 : ℝ)))
            (embeddedConfigurationRestriction G H f hGH A)) =
        expectation (law H q (horizontalStripTopWiredBoundary N n))
          (T.indicator (fun _ => (1 : ℝ))) := by
      unfold expectation
      apply Finset.sum_congr rfl
      intro A hA
      have heq := hrestrict A
      by_cases hout : A ∈ T
      · have hin : embeddedConfigurationRestriction G H f hGH A ∈ S := by
          simpa [S, T] using heq.mp hout
        simp [S, T, Set.indicator, hout, hin]
      · have hin : embeddedConfigurationRestriction G H f hGH A ∉ S := by
          intro hs
          exact hout (by simpa [S, T] using heq.mpr hs)
        simp [S, T, Set.indicator, hout, hin]
    have hreal :
        ((horizontalStripRectangleProbabilityMeasure q M n
          (horizontalStripTopWiredBoundary M n) : Measure LatticeConfiguration)
            (LatticeConfiguration.allOpen F)).toReal ≤
        ((horizontalStripRectangleProbabilityMeasure q N n
          (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration)
            (LatticeConfiguration.allOpen F)).toReal := by
      calc
        _ = expectation (law G q (horizontalStripTopWiredBoundary M n))
              (S.indicator (fun _ => (1 : ℝ))) := by
                rw [hleft]
                exact horizontalStripRectangleCylinder_toReal_eq_expectation q M n
                  (horizontalStripTopWiredBoundary M n) F
        _ ≤ expectation (law H q (horizontalStripTopWiredBoundary N n))
              (fun A => (S.indicator (fun _ => (1 : ℝ)))
                (embeddedConfigurationRestriction G H f hGH A)) := by
                  convert hcmp using 1 <;> rfl
        _ = expectation (law H q (horizontalStripTopWiredBoundary N n))
              (T.indicator (fun _ => (1 : ℝ))) := hlarge
        _ = _ := by
          rw [← horizontalStripRectangleCylinder_toReal_eq_expectation q N n
            (horizontalStripTopWiredBoundary N n) F, hright]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal
  · push Not at hF
    obtain ⟨e, heF, heRange⟩ := hF
    have hempty : horizontalStripRectangleCylinderEvent M n F = ∅ := by
      ext A
      constructor
      · intro hA
        have heMap : e ∈ A.image (horizontalStripRectangleOriginalEdge M n) := hA heF
        obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp heMap
        exact heRange ⟨a, hEq⟩
      · simp
    rw [horizontalStripRectangleProbabilityMeasure_allOpen q M n
      (horizontalStripTopWiredBoundary M n) F,
      hempty, measure_empty]
    exact bot_le

end
end PottsContinuity.FKC.Medial
