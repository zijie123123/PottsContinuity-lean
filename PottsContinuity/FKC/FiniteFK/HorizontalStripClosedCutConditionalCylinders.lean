-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedCutConditionalCylinders.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutConditionalLaw
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutCylinderSupport
public import PottsContinuity.FKC.FiniteFK.HorizontalStripIntervalCylinderRestriction
public import PottsContinuity.FKC.FiniteFK.HorizontalStripIntervalCylinders
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open Finset

noncomputable section

attribute [local instance] PottsContinuity.FKC.FiniteFK.configurationMeasurableSpace

local instance closedCutConditionalCylinderOuterEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance closedCutConditionalCylinderOuterEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _
local instance closedCutConditionalCylinderIntervalEdgeFintype (n : ℕ) (lo hi : ℤ) :
    Fintype (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).edgeSet := Fintype.ofFinite _

/-- Under a successful two-sided closed-cut record, the original outer
cylinder has the same conditional probability as its literal restriction to
the selected interval. The queried edge set is required to lie in that
interval. -/
theorem horizontalStripClosedCutRecord_cylinder_probability_le_limit_of_interval_support
    {N n K : ℕ} (hKN : K ≤ N) (q : ClusterWeight)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hξ : ξ.boundary ⊆ horizontalStripTopSidesSet N n)
    (hTop : (BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition ≤
      ξ.partition)
    (A₀ : Configuration (horizontalStripCutRectangle N n))
    {i j : ℕ}
    (hL : (horizontalStripLeftBlockScan N n K A₀).2 = some i)
    (hR : (horizontalStripRightBlockScan N n K A₀).2 = some j)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range
      (rectanglePrimalEdgeToSquareEdge
        (-(N : ℤ) + (i : ℤ) + 1, 0)
        ((N : ℤ) - 1 - (j : ℤ) - (-(N : ℤ) + (i : ℤ) + 1)).toNat
        (2 * n)))
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ)) :
    (((law (horizontalStripCutRectangle N n) q ξ).filter
      (revealRecordEvent (horizontalStripCutRectangle N n)
        (fun A => horizontalStripClosedCutReveal N n K A) A₀)
      (by
        have hstable : ∀ C C', C' ∩ horizontalStripClosedCutReveal N n K C =
            C ∩ horizontalStripClosedCutReveal N n K C →
            horizontalStripClosedCutReveal N n K C' = horizontalStripClosedCutReveal N n K C := by
          intro C C' hAgree
          exact horizontalStripClosedCutReveal_eq_of_agree N n K C C' hKN hAgree
        rw [revealRecordEvent_eq_frozenStateEvent
          (horizontalStripCutRectangle N n)
          (fun A => horizontalStripClosedCutReveal N n K A) hstable A₀]
        exact frozenStateEvent_support q ξ _ _)).toMeasure
      (horizontalStripRectangleCylinderEvent N n F)).toReal ≤
      ((μ (LatticeConfiguration.allOpen F) : NNReal) : ℝ) := by
  classical
  let : DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _
  let lo : ℤ := -(N : ℤ) + (i : ℤ) + 1
  let hi : ℤ := (N : ℤ) - 1 - (j : ℤ)
  let w : ℕ := (hi - lo).toNat
  let G := horizontalStripCutRectangle N n
  let H := rectangleGraph (lo, 0) w (2 * n)
  have hcenter := horizontalStripClosedCutReveal_window_contains_center N n K A₀ hKN hL hR
  have hsEnds := horizontalStripClosedCutReveal_window_strict_outer_ends N n K A₀ hL hR
  have hw : (w : ℤ) = hi - lo := by
    dsimp [w]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo)]
  have hleft : -(N : ℤ) < lo := by dsimp [lo]; exact hsEnds.1
  have hright : lo + (w : ℤ) < N := by
    have hsum : lo + (hi - lo) = hi := by dsimp [lo, hi]; omega
    rw [hw, hsum]
    exact hsEnds.2
  have hlo : -(N : ℤ) ≤ lo := le_of_lt hleft
  have hhi : hi ≤ N := le_of_lt hsEnds.2
  have hle : lo ≤ hi := by omega
  have hrightWeak : lo + (w : ℤ) ≤ N := le_of_lt hright
  let f : RectangleVertex (lo, 0) w (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
    horizontalStripIntervalEmbedding hlo hrightWeak
  have hGH : H.map f ≤ G := horizontalStripInterval_map_le hlo hrightWeak
  let reveal : Configuration G → Configuration G :=
    fun A => horizontalStripClosedCutReveal N n K A
  have hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C := by
    intro C C' hAgree
    exact horizontalStripClosedCutReveal_eq_of_agree N n K C C' hKN hAgree
  have hsupp : ∃ C ∈ revealRecordEvent G reveal A₀, C ∈ (law G q ξ).support := by
    rw [revealRecordEvent_eq_frozenStateEvent G reveal hstable A₀]
    exact frozenStateEvent_support q ξ _ _
  let P := (law G q ξ).filter (revealRecordEvent G reveal A₀) hsupp
  have hLaw : P.map (embeddedConfigurationRestriction H G f hGH) =
      law H q (horizontalStripIntervalTopWiredBoundary lo w n) := by
    simpa [P, G, H, f, hGH, lo, hi, w] using
      law_filter_horizontalStripClosedCutRecord_map_interval_topOnly
        N n K hKN q ξ hξ hTop A₀ hL hR
  let fcut : RectangleVertex (lo, 0) w (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
    horizontalStripCutWindowIntervalEmbedding hlo hhi hle
  have hf : f = fcut := by
    apply Function.Embedding.ext
    intro v
    apply Subtype.ext
    exact Prod.ext rfl rfl
  let hGcut : H.map fcut ≤ G := horizontalStripCutWindowInterval_map_le hlo hhi hle
  have hrestriction : ∀ A : Configuration G,
      A ∈ horizontalStripRectangleCylinderEvent N n F ↔
        embeddedConfigurationRestriction H G f hGH A ∈
          horizontalStripIntervalCylinderEvent lo w n F := by
    intro A
    have hcut := horizontalStripCutWindowIntervalCylinder_restrict_iff
      hlo hhi hle F hF A
    simpa [f, fcut, hGcut, hGH, hf, G, H, lo, hi, w] using hcut
  let Eout := horizontalStripRectangleCylinderEvent N n F
  let Ein := horizontalStripIntervalCylinderEvent lo w n F
  have hpre : (embeddedConfigurationRestriction H G f hGH) ⁻¹' Ein = Eout := by
    ext A
    exact (hrestriction A).symm
  have hmeas : Measurable (embeddedConfigurationRestriction H G f hGH) := measurable_from_top
  have hmapMeasure : P.toMeasure.map (embeddedConfigurationRestriction H G f hGH) =
      (P.map (embeddedConfigurationRestriction H G f hGH)).toMeasure :=
    PMF.toMeasure_map (embeddedConfigurationRestriction H G f hGH) P hmeas
  have hprob : P.toMeasure Eout = measure H q
      (horizontalStripIntervalTopWiredBoundary lo w n) Ein := by
    calc
      P.toMeasure Eout = P.toMeasure
          ((embeddedConfigurationRestriction H G f hGH) ⁻¹' Ein) := by
            congr 1
            exact hpre.symm
      _ = (P.toMeasure.map (embeddedConfigurationRestriction H G f hGH)) Ein := by
            rw [Measure.map_apply hmeas MeasurableSpace.measurableSet_top]
      _ = (P.map (embeddedConfigurationRestriction H G f hGH)).toMeasure Ein := by
            rw [hmapMeasure]
      _ = (law H q (horizontalStripIntervalTopWiredBoundary lo w n)).toMeasure Ein := by
            rw [hLaw]
      _ = measure H q (horizontalStripIntervalTopWiredBoundary lo w n) Ein := rfl
  have hbound := horizontalStripIntervalTopWired_probability_allOpen_le_limit
    q lo w n μ hμ F
  change (P.toMeasure Eout).toReal ≤ _
  rw [hprob]
  exact hbound

/-- The selected-interval support premise follows whenever all queried edges
lie in the central `K`-box retained by the two successful closed cuts. -/
theorem horizontalStripClosedCutRecord_cylinder_probability_le_limit_of_center_support
    {N n K : ℕ} (hKN : K ≤ N) (q : ClusterWeight)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hξ : ξ.boundary ⊆ horizontalStripTopSidesSet N n)
    (hTop : (BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition ≤
      ξ.partition)
    (A₀ : Configuration (horizontalStripCutRectangle N n))
    {i j : ℕ}
    (hL : (horizontalStripLeftBlockScan N n K A₀).2 = some i)
    (hR : (horizontalStripRightBlockScan N n K A₀).2 = some j)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge K n))
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ)) :
    (((law (horizontalStripCutRectangle N n) q ξ).filter
      (revealRecordEvent (horizontalStripCutRectangle N n)
        (fun A => horizontalStripClosedCutReveal N n K A) A₀)
      (by
        have hstable : ∀ C C', C' ∩ horizontalStripClosedCutReveal N n K C =
            C ∩ horizontalStripClosedCutReveal N n K C →
            horizontalStripClosedCutReveal N n K C' = horizontalStripClosedCutReveal N n K C := by
          intro C C' hAgree
          exact horizontalStripClosedCutReveal_eq_of_agree N n K C C' hKN hAgree
        rw [revealRecordEvent_eq_frozenStateEvent
          (horizontalStripCutRectangle N n)
          (fun A => horizontalStripClosedCutReveal N n K A) hstable A₀]
        exact frozenStateEvent_support q ξ _ _)).toMeasure
      (horizontalStripRectangleCylinderEvent N n F)).toReal ≤
      ((μ (LatticeConfiguration.allOpen F) : NNReal) : ℝ) := by
  have hFinterval := horizontalStripClosedCut_cylinder_edge_support
    hKN A₀ hL hR F hF
  exact horizontalStripClosedCutRecord_cylinder_probability_le_limit_of_interval_support
    hKN q ξ hξ hTop A₀ hL hR F hFinterval μ hμ

end
end PottsContinuity.FKC.Medial
