module

public import PottsContinuity.BD12.WiredBoxRadiusProbability
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Exact shell-event probabilities under wired extension when the target
ball is contained in the sampled box. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory
noncomputable section
open scoped Classical
attribute [local instance] configurationMeasurableSpace

/-- Wired extension cannot create a new inner-radius arm without an actual
sampled arm: first-hit truncation stays inside the sampled box. -/
theorem infiniteRadiusEvent_wiredBoxConfiguration_iff (c : LatticeVertex) (N n : ℕ)
    (hnN : n ≤ N) (A : Configuration (boxGraph c N)) :
    wiredBoxConfiguration c N A ∈ infiniteRadiusEvent c n ↔
      A ∈ finiteDomainOneArmEvent (latticeBox c N) c (radiusBoxCenter c N) n := by
  constructor
  · rintro ⟨v,hv,⟨p⟩⟩
    let ω := wiredBoxConfiguration c N A
    obtain ⟨z,q,hz,hq⟩ := walk_reaches_radius_inside_ball (latticeRadius c)
      (infinite_open_radius_step c ω) p n (by simp) hv.ge
    have hzN : z ∈ latticeBox c N := (latticeRadius_le_iff_mem_box c z N).mp (hz.le.trans hnN)
    have hall : ∀ v ∈ q.support, v ∈ (latticeBox c N : Set LatticeVertex) :=
      fun v hv => (latticeRadius_le_iff_mem_box c v N).mp ((hq v hv).trans hnN)
    have hconn : ((PD.rcInfiniteOpenGraph ω).induce (latticeBox c N : Set LatticeVertex)).Reachable
        (radiusBoxCenter c N) ⟨z,hzN⟩ := ⟨q.induce _ hall⟩
    have hres := embeddedRestriction_wiredBoxConfiguration c N A
    have hgraph : openGraph (boxGraph c N) A = (PD.rcInfiniteOpenGraph ω).induce (latticeBox c N : Set LatticeVertex) :=
      (congrArg (openGraph (boxGraph c N)) hres).symm.trans (embeddedRestriction_domainGraph (latticeBox c N) ω)
    refine ⟨⟨z,hzN⟩,hz,?_⟩
    rw [← hgraph] at hconn
    exact hconn
  · intro hA
    exact finite_box_one_arm_subset_wired_radius c N n n le_rfl hA

/-- Exact probability of the inner shell event under the wired box extension. -/
theorem wired_box_radius_probability_eq_finite (θ : Parameters) (c : LatticeVertex)
    (N n : ℕ) (hnN : n ≤ N) :
    (wiredBoxProbabilityMeasure θ c N : Measure LatticeConfiguration).real (infiniteRadiusEvent c n) =
      (measure (boxGraph c N) θ (BoundaryCondition.wired (boxVertexBoundary c N))
        (finiteDomainOneArmEvent (latticeBox c N) c (radiusBoxCenter c N) n)).toReal := by
  change (((law (boxGraph c N) θ (BoundaryCondition.wired (boxVertexBoundary c N))).map
    (wiredBoxConfiguration c N)).toMeasure (infiniteRadiusEvent c n)).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top (infiniteRadiusEvent_isCylinder c n).measurableSet]
  congr 1
  congr 1
  ext A
  exact infiniteRadiusEvent_wiredBoxConfiguration_iff c N n hnN A

end
end PottsContinuity.BD12
