module

public import PottsContinuity.Thm3.Prop4.TiltedStoppedInterval
public import PottsContinuity.Thm3.Prop4.TiltedIntervalCylinders

/-! # Actual cylinder comparison on a successful two-sided stopping record -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance stoppedCylinderEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _
local instance stoppedCylinderEdgeDecidableEq (n M : ℕ) (t : ℝ) :
    DecidableEq (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- Exact original-edge restriction and the actual stopped interval law imply
the cylinder comparison to the constructed top-only weak limit. -/
theorem tiltedTwoCutRecord_allOpen_le_limit (θ : Parameters)
    (n M : ℕ) (t : ℝ) (a b : ℤ) (K : ℕ) (side : Fin 2)
    (A₀ : Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))))
    (i j : ℕ)
    (hL : (tiltedCutScan n M t (fun r => a+r) K A₀).2 = some i)
    (hR : (tiltedCutScan n M t (fun r => b-r) K A₀).2 = some j)
    (hinside : ∀ z ∈ tiltedInterval n M t (a+i+1) (b-j), z ∉ vertexBoundary (box M))
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : Tendsto (tiltedWindowPlaneProbabilityMeasure θ n t 0) atTop (𝓝 ν))
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding (tiltedInterval n M t (a+i+1) (b-j)))) :
    (((law _ θ (tiltedWindowBoundary n M t side)).filter
      (Exploration.revealRecordEvent (tiltedTwoCutReveal n M t a b K) A₀)
      (by
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent _
          (tiltedTwoCutReveal_stable n M t a b K) A₀]
        exact frozenStateEvent_support θ _ _ _)).toMeasure
      (finiteSubgraphOpenEvent (tiltedWindow n M t) F)).toReal ≤
        ν.toMeasure.real (LatticeConfiguration.allOpen F) := by
  let S := tiltedInterval n M t (a+i+1) (b-j)
  let T := tiltedWindow n M t
  let G := finiteLatticeGraph S
  let H := finiteLatticeGraph T
  let f := tiltedIntervalEmbedding n M t (a+i+1) (b-j)
  have hmap := tiltedInterval_map_le n M t (a+i+1) (b-j)
  let reveal := tiltedTwoCutReveal n M t a b K
  let P := (law H θ (tiltedWindowBoundary n M t side)).filter
    (Exploration.revealRecordEvent reveal A₀)
    (by
      exact ⟨A₀,⟨rfl,rfl⟩,(law_pos H θ (tiltedWindowBoundary n M t side) A₀).ne'⟩)
  have hLaw : P.map (embeddedConfigurationRestriction G H f hmap) =
      law G θ (tiltedIntervalTopBoundary n M t (a+i+1) (b-j)) :=
    law_filter_tiltedTwoCutRecord_map_interval_top θ n M t a b K side A₀ i j hL hR hinside
  have hsets : (embeddedConfigurationRestriction G H f hmap) ⁻¹' finiteSubgraphOpenEvent S F =
      finiteSubgraphOpenEvent T F := by
    ext A
    exact (induced_openEvent_restriction_iff f (fun _ => rfl) hmap F hF A).symm
  have hprob := congrArg (fun Q : PMF (Configuration G) => Q.toMeasure (finiteSubgraphOpenEvent S F)) hLaw
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top,hsets] at hprob
  change (P.toMeasure (finiteSubgraphOpenEvent T F)).toReal ≤ _
  rw [hprob]
  exact tiltedIntervalTop_allOpen_le_limit θ n M t (a+i+1) (b-j) ν hν F hF

end

end PottsContinuity.Thm3.Prop4
