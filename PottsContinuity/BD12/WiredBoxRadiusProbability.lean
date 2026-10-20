module

public import PottsContinuity.BD12.InfiniteRadiusEvent
public import PottsContinuity.BD12.DRTWiredOneArmSequence
public import PottsContinuity.BD12.DRTEventProbability
public import PottsContinuity.PD.FK.WiredBoxLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Finite actual one-arm probabilities are bounded by fixed-radius cylinders
under their literal wired whole-plane extensions. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory
noncomputable section
open scoped Classical
attribute [local instance] configurationMeasurableSpace

/-- Wired extension retains exactly every original sampled box edge. -/
theorem embeddedRestriction_wiredBoxConfiguration (c : LatticeVertex) (N : ℕ)
    (A : Configuration (boxGraph c N)) :
    embeddedRestriction (boxGraph c N) (frozenEdgeEmbedding (latticeBox c N))
      (wiredBoxConfiguration c N A) = A := by
  ext e
  apply (mem_embeddedRestriction (boxGraph c N) _ _ e).trans
  change wiredBoxConfiguration c N A (boxEdgeEmbedding c N e) = true ↔ e ∈ A
  rw [wiredBoxConfiguration_at]
  exact decide_eq_true_iff

/-- A finite open arm remains an actual arm after extension, at every smaller radius. -/
theorem finite_box_one_arm_subset_wired_radius (c : LatticeVertex) (N n m : ℕ) (hmn : m ≤ n) :
    finiteDomainOneArmEvent (latticeBox c N) c (radiusBoxCenter c N) n ⊆
      wiredBoxConfiguration c N ⁻¹' infiniteRadiusEvent c m := by
  rintro A ⟨v,hv,hconn⟩
  let ω := wiredBoxConfiguration c N A
  have hres := embeddedRestriction_wiredBoxConfiguration c N A
  have hgraph : openGraph (boxGraph c N) A = (PD.rcInfiniteOpenGraph ω).induce (latticeBox c N : Set LatticeVertex) :=
    (congrArg (openGraph (boxGraph c N)) hres).symm.trans (embeddedRestriction_domainGraph (latticeBox c N) ω)
  have hconn' : ((PD.rcInfiniteOpenGraph ω).induce (latticeBox c N : Set LatticeVertex)).Reachable
      (radiusBoxCenter c N) v := by
    rw [← hgraph]
    exact hconn
  let f : (PD.rcInfiniteOpenGraph ω).induce (latticeBox c N : Set LatticeVertex) →g
      PD.rcInfiniteOpenGraph ω := { toFun := Subtype.val, map_rel' := fun h => h }
  exact infiniteRadiusEvent_antitone c hmn ⟨v.val,hv,hconn'.map f⟩

/-- Compare finite actual one-arm probabilities with whole-plane shell cylinders. -/
theorem finite_wired_box_one_arm_le_radius (θ : Parameters) (c : LatticeVertex)
    (N n m : ℕ) (hmn : m ≤ n) :
    (measure (boxGraph c N) θ (BoundaryCondition.wired (boxVertexBoundary c N))
      (finiteDomainOneArmEvent (latticeBox c N) c (radiusBoxCenter c N) n)).toReal ≤
    (wiredBoxProbabilityMeasure θ c N : Measure LatticeConfiguration).real (infiniteRadiusEvent c m) := by
  change _ ≤ (((law (boxGraph c N) θ (BoundaryCondition.wired (boxVertexBoundary c N))).map
    (wiredBoxConfiguration c N)).toMeasure (infiniteRadiusEvent c m)).toReal
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top (infiniteRadiusEvent_isCylinder c m).measurableSet]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (finite_box_one_arm_subset_wired_radius c N n m hmn))

/-- The actual source theta_n is bounded by every smaller-radius cylinder. -/
theorem drtWiredOneArmMean_le_radius_box_probability (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β : Set.Ioi (0 : ℝ)) (n m : ℕ) (hmn : m ≤ n) :
    drtWiredOneArmMean q β n ≤
      (wiredBoxProbabilityMeasure (drtHomogeneousParameters q hq β) (0,0) (2*n) :
        Measure LatticeConfiguration).real (infiniteRadiusEvent (0,0) m) := by
  have h := finite_wired_box_one_arm_le_radius (drtHomogeneousParameters q hq β) (0,0) (2*n) n m hmn
  let G := finiteLatticeGraph (latticeBox (0,0) (2*n))
  let ξ := BoundaryCondition.wired (boxVertexBoundary (0,0) (2*n))
  let J : G.edgeSet → Set.Ioi (0 : ℝ) := fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩
  let M := drtMean G q ξ J β
  have hi := finiteDomainOneArmEvent_indicator (latticeBox (0,0) (2*n)) (0,0) (radiusBoxCenter (0,0) (2*n)) n
  have heq := drt_mean_indicator_eq_fk_probability G q hq ξ β
    (finiteDomainOneArmEvent (latticeBox (0,0) (2*n)) (0,0) (radiusBoxCenter (0,0) (2*n)) n)
  exact ((congrArg M hi).symm.trans heq).trans_le h

end
end PottsContinuity.BD12
