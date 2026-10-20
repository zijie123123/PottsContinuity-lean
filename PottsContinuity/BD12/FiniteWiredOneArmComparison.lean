module

public import PottsContinuity.BD12.FiniteDomainOneArmRestriction
public import PottsContinuity.BD12.FiniteWiredRestriction
public import PottsContinuity.BD12.DRTEventProbability
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-! Wired one-arm comparison on nested induced domains containing the full
radius ball. The event restriction is proved by first-hit truncation. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical
local instance wiredOneArmEdges (S : Finset LatticeVertex) :
    Fintype (finiteLatticeGraph S).edgeSet := Fintype.ofFinite _

/-- One-arm probabilities decrease when the wired domain increases, as long
as the entire target-radius ball is retained in the smaller domain. -/
theorem finite_wired_one_arm_probability_le {S T : Finset LatticeVertex}
    (θ : Parameters) (hST : S ⊆ T) (c : LatticeVertex) (n : ℕ)
    (hball : latticeBox c n ⊆ S) (o : (S : Set LatticeVertex)) (ho : o.val = c) :
    (measure (finiteLatticeGraph T) θ (BoundaryCondition.wired (frozenVertexBoundary T))
      (finiteDomainOneArmEvent T c (finiteLatticeVertexEmbedding hST o) n)).toReal ≤
    (measure (finiteLatticeGraph S) θ (BoundaryCondition.wired (frozenVertexBoundary S))
      (finiteDomainOneArmEvent S c o n)).toReal := by
  rw [← finiteDomainOneArmEvent_preimage hST c n hball o ho]
  exact finite_wired_induced_restriction_probability_le θ hST _
    (finiteDomainOneArmEvent_isUpperSet S c o n)

/-- The same inequality for literal one-arm means of the actual homogeneous beta-law. -/
theorem drt_finite_wired_one_arm_mean_le {S T : Finset LatticeVertex}
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (β : Set.Ioi (0 : ℝ))
    (hST : S ⊆ T) (c : LatticeVertex) (n : ℕ) (hball : latticeBox c n ⊆ S)
    (o : (S : Set LatticeVertex)) (ho : o.val = c) :
    drtMean (finiteLatticeGraph T) q (BoundaryCondition.wired (frozenVertexBoundary T))
        (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β
        (radiusOneArmIndicator (finiteLatticeGraph T) (fun v => latticeRadius c v.val)
          (finiteLatticeVertexEmbedding hST o) n) ≤
      drtMean (finiteLatticeGraph S) q (BoundaryCondition.wired (frozenVertexBoundary S))
        (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β
        (radiusOneArmIndicator (finiteLatticeGraph S) (fun v => latticeRadius c v.val) o n) := by
  have h := finite_wired_one_arm_probability_le (drtHomogeneousParameters q hq β) hST c n hball o ho
  rw [← drt_mean_indicator_eq_fk_probability _ q hq _ β,
    ← drt_mean_indicator_eq_fk_probability _ q hq _ β] at h
  simpa only [finiteDomainOneArmEvent_indicator] using h

end
end PottsContinuity.BD12
