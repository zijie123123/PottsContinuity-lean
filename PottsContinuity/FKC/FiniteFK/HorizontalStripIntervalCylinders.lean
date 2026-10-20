-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripIntervalCylinders.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripIntervalTopBoundary
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopCylinders
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopExhaustion
public import PottsContinuity.FKC.FiniteFK.RectangleDualCarrier
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open FiniteProbability
open scoped BigOperators

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance intervalCylinderEdgeFintype (a : ℤ) (w n : ℕ) :
    Fintype (rectangleGraph (a, 0) w (2 * n)).edgeSet := Fintype.ofFinite _
local instance outerCylinderEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _

/-- Finite cylinder event on an arbitrary horizontal interval, read from the
actual original square-lattice edges. -/
def horizontalStripIntervalCylinderEvent (a : ℤ) (w n : ℕ)
    (F : Finset squareLattice.edgeSet) :
    Set (Configuration (rectangleGraph (a, 0) w (2 * n))) :=
  {A | F ⊆ A.image (rectanglePrimalEdgeToSquareEdge (a, 0) w (2 * n))}

private theorem horizontalStripIntervalCylinderEvent_upper
    (a : ℤ) (w n : ℕ) (F : Finset squareLattice.edgeSet) :
    IsUpperSet (horizontalStripIntervalCylinderEvent a w n F) := by
  intro A B hAB hA
  exact hA.trans (Finset.image_mono _ hAB)

private theorem horizontalStripIntervalEdge_compatible
    {a : ℤ} {w N n : ℕ} (hleft : -(N : ℤ) ≤ a)
    (hright : a + (w : ℤ) ≤ N)
    (e : (rectangleGraph (a, 0) w (2 * n)).edgeSet) :
    horizontalStripRectangleOriginalEdge N n
      (embeddedEdgeEmbedding (rectangleGraph (a, 0) w (2 * n))
        (horizontalStripCutRectangle N n)
        (horizontalStripIntervalEmbedding (n := n) hleft hright)
        (horizontalStripInterval_map_le (n := n) hleft hright) e) =
      rectanglePrimalEdgeToSquareEdge (a, 0) w (2 * n) e := by
  apply Subtype.ext
  change Sym2.map (fun v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => v.val)
      (Sym2.map (horizontalStripIntervalEmbedding (n := n) hleft hright) e.val) =
    Sym2.map (fun v : RectangleVertex (a, 0) w (2 * n) => v.val) e.val
  rw [Sym2.map_map]
  congr 1

private theorem horizontalStripIntervalCylinder_restrict_subset
    {a : ℤ} {w N n : ℕ} (hleft : -(N : ℤ) ≤ a)
    (hright : a + (w : ℤ) ≤ N) (F : Finset squareLattice.edgeSet) :
    {A : Configuration (horizontalStripCutRectangle N n) |
      embeddedConfigurationRestriction (rectangleGraph (a, 0) w (2 * n))
        (horizontalStripCutRectangle N n)
        (horizontalStripIntervalEmbedding (n := n) hleft hright)
        (horizontalStripInterval_map_le (n := n) hleft hright) A ∈
          horizontalStripIntervalCylinderEvent a w n F} ⊆
      {A | F ⊆ A.image (horizontalStripRectangleOriginalEdge N n)} := by
  intro A hA e he
  obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (hA he)
  have hx' : embeddedEdgeEmbedding (rectangleGraph (a, 0) w (2 * n))
      (horizontalStripCutRectangle N n)
      (horizontalStripIntervalEmbedding (n := n) hleft hright)
      (horizontalStripInterval_map_le (n := n) hleft hright) x ∈ A :=
    (mem_embeddedConfigurationRestriction _ _ _ _ A _).mp hx
  exact Finset.mem_image.mpr ⟨embeddedEdgeEmbedding
      (rectangleGraph (a, 0) w (2 * n)) (horizontalStripCutRectangle N n)
      (horizontalStripIntervalEmbedding (n := n) hleft hright)
      (horizontalStripInterval_map_le (n := n) hleft hright) x,
    hx', (horizontalStripIntervalEdge_compatible hleft hright x).trans hxe⟩

/-- The interval cylinder probability is bounded by the centered finite
 top-wired rectangle's actual whole-plane all-open cylinder probability. -/
theorem horizontalStripIntervalTopWired_probability_allOpen_le
    (q : ClusterWeight) (a : ℤ) (w n N : ℕ)
    (hleft : -(N : ℤ) ≤ a) (hright : a + (w : ℤ) ≤ N)
    (F : Finset squareLattice.edgeSet) :
    measure (rectangleGraph (a, 0) w (2 * n)) q
      (horizontalStripIntervalTopWiredBoundary a w n)
      (horizontalStripIntervalCylinderEvent a w n F) ≤
    (horizontalStripRectangleProbabilityMeasure q N n
      (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F) := by
  let G := rectangleGraph (a, 0) w (2 * n)
  let H := horizontalStripCutRectangle N n
  let E := horizontalStripIntervalCylinderEvent a w n F
  let f : RectangleVertex (a, 0) w (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
    horizontalStripIntervalEmbedding (n := n) hleft hright
  have hGH : G.map f ≤ H := horizontalStripInterval_map_le (n := n) hleft hright
  have hfinite := horizontalStripIntervalTopWired_probability_le
    (n := n) hleft hright q E (horizontalStripIntervalCylinderEvent_upper a w n F)
  have hrestrict :
      measure H q (horizontalStripTopWiredBoundary N n)
        {A | embeddedConfigurationRestriction G H f hGH A ∈ E} ≤
      measure H q (horizontalStripTopWiredBoundary N n)
        {A | F ⊆ A.image (horizontalStripRectangleOriginalEdge N n)} :=
    measure_mono (horizontalStripIntervalCylinder_restrict_subset (n := n) hleft hright F)
  have houterCylinder :
      measure H q (horizontalStripTopWiredBoundary N n)
        {A | F ⊆ A.image (horizontalStripRectangleOriginalEdge N n)} =
      (horizontalStripRectangleProbabilityMeasure q N n
        (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) := by
    symm
    exact horizontalStripRectangleProbabilityMeasure_allOpen q N n
      (horizontalStripTopWiredBoundary N n) F
  have hreal :
      (measure G q (horizontalStripIntervalTopWiredBoundary a w n) E).toReal ≤
      ((horizontalStripRectangleProbabilityMeasure q N n
        (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F)).toReal := by
    calc
      _ ≤ (measure H q (horizontalStripTopWiredBoundary N n)
          {A | embeddedConfigurationRestriction G H f hGH A ∈ E}).toReal := hfinite
      _ ≤ (measure H q (horizontalStripTopWiredBoundary N n)
          {A | F ⊆ A.image (horizontalStripRectangleOriginalEdge N n)}).toReal := by
            exact ENNReal.toReal_mono (measure_ne_top _ _) hrestrict
      _ = _ := by rw [houterCylinder]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

/-- A fixed interval cylinder is dominated by the common weak limit of the
centered top-wired strip laws. -/
theorem horizontalStripIntervalTopWired_probability_allOpen_le_limit
    (q : ClusterWeight) (a : ℤ) (w n : ℕ)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ))
    (F : Finset squareLattice.edgeSet) :
    (measure (rectangleGraph (a, 0) w (2 * n)) q
      (horizontalStripIntervalTopWiredBoundary a w n)
      (horizontalStripIntervalCylinderEvent a w n F)).toReal ≤
      ((μ (LatticeConfiguration.allOpen F) : NNReal) : ℝ) := by
  let G := rectangleGraph (a, 0) w (2 * n)
  let E := horizontalStripIntervalCylinderEvent a w n F
  let N₀ := a.natAbs + w
  have habsLower : -(a.natAbs : ℤ) ≤ a := by
    cases a <;> simp [Int.natAbs]; omega
  have habsUpper : a ≤ (a.natAbs : ℤ) := by
    cases a <;> simp [Int.natAbs]; omega
  have htail : ∀ᶠ N : ℕ in atTop,
      (measure G q (horizontalStripIntervalTopWiredBoundary a w n) E).toReal ≤
        ((horizontalStripTopWiredProbabilityMeasures q n N
          (LatticeConfiguration.allOpen F) : NNReal) : ℝ) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨N₀, fun N hN => hN⟩] with N hN
    have hNat : a.natAbs + w ≤ N := by omega
    have hbound : (a.natAbs : ℤ) ≤ N := by exact_mod_cast (Nat.le_trans (Nat.le_add_right _ _) hNat)
    have hleft : -(N : ℤ) ≤ a := by omega
    have hright : a + (w : ℤ) ≤ N := by
      have hsum : (a.natAbs : ℤ) + (w : ℤ) ≤ N := by exact_mod_cast hNat
      omega
    have hfinite := horizontalStripIntervalTopWired_probability_allOpen_le
      q a w n N hleft hright F
    have htmp :
        (measure G q (horizontalStripIntervalTopWiredBoundary a w n) E).toReal ≤
          ((horizontalStripRectangleProbabilityMeasure q N n
            (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration)
            (LatticeConfiguration.allOpen F)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hfinite
    have htmp' :
        (measure G q (horizontalStripIntervalTopWiredBoundary a w n) E).toReal ≤
          ((horizontalStripRectangleProbabilityMeasure q N n
            (horizontalStripTopWiredBoundary N n)
            (LatticeConfiguration.allOpen F) : NNReal) : ℝ) := by
      exact htmp
    simpa [horizontalStripTopWiredProbabilityMeasures] using htmp'
  have hlimNN : Tendsto
      (fun N : ℕ => horizontalStripTopWiredProbabilityMeasures q n N
        (LatticeConfiguration.allOpen F)) atTop
      (𝓝 (μ (LatticeConfiguration.allOpen F))) :=
    LatticeConfiguration.tendsto_allOpen_of_weak hμ F
  have hlimR := (NNReal.continuous_coe.tendsto _).comp hlimNN
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlimR htail

end
end PottsContinuity.FKC.Medial
