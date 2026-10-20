module

public import PottsContinuity.DualityExt.PositiveBoundaryReweighting
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Conditional finite-volume annulus transfer

This module composes a proved FK law duality with a deterministic event
identification and the exact two-boundary reweighting. The topology and the
finite-volume dual-law identity remain explicit inputs; the conclusion is a
conditional consumer, not the source annulus theorem by itself.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability
open scoped BigOperators

noncomputable section

local instance transferConfigFintype {V : Type*} [Finite V]
    {G : SimpleGraph V} : Fintype (Configuration G) := Fintype.ofFinite _
local instance transferTargetConfigFintype {W : Type*} [Finite W]
    {H : SimpleGraph W} : Fintype (Configuration H) := Fintype.ofFinite _
local instance transferSourceEdgeFintype {V : Type*} [Finite V]
    {G : SimpleGraph V} : Fintype G.edgeSet := Fintype.ofFinite _
local instance transferTargetEdgeFintype {W : Type*} [Finite W]
    {H : SimpleGraph W} : Fintype H.edgeSet := Fintype.ofFinite _

private theorem positiveFKProbability_nonneg_transfer
    {V : Type*} [Finite V] {G : SimpleGraph V} {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) (A : Configuration G) :
    0 ≤ positiveFKProbability q p ξ A := by
  unfold positiveFKProbability
  apply div_nonneg
  · exact (positiveFKWeight_pos' hq hp hp1 ξ A).le
  · unfold positiveFKPartitionFunction
    exact (FiniteProbability.partition_pos _
      (positiveFKWeight_pos' hq hp hp1 ξ)).le

/-- A configuration equivalence carrying one finite FK law to another also
preserves the real probability of every event transported by that equivalence.
This is the probability-level consequence used before applying the annulus
two-block wiring correction. -/
theorem positiveFKEventProbability_eq_of_law_map_equiv
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) (η : BoundaryCondition W)
    (d : Configuration G ≃ Configuration H)
    (S : Set (Configuration H))
    (hlaw : (positiveFKLaw G q p hq hp hp1 ξ).map d =
      positiveFKLaw H q p hq hp hp1 η) :
    positiveFKEventProbability (q := q) (p := p) ξ (d ⁻¹' S) =
      positiveFKEventProbability (q := q) (p := p) η S := by
  classical
  have hpoint (A : Configuration G) :
      positiveFKProbability q p ξ A = positiveFKProbability q p η (d A) := by
    have hmass := congrArg (fun μ : PMF (Configuration H) => μ (d A)) hlaw
    rw [PMF.map_apply, tsum_fintype] at hmass
    have hsum : (∑ B : Configuration G,
        if d A = d B then positiveFKLaw G q p hq hp hp1 ξ B else 0) =
        positiveFKLaw G q p hq hp hp1 ξ A := by
      have hiff (B : Configuration G) : d A = d B ↔ A = B :=
        ⟨fun h => d.injective h, fun h => congrArg d h⟩
      calc
        _ = ∑ B : Configuration G,
            if A = B then positiveFKLaw G q p hq hp hp1 ξ B else 0 := by
              apply Finset.sum_congr rfl
              intro B hB
              simp only [hiff B]
        _ = _ := by simp
    have hmass' : positiveFKLaw G q p hq hp hp1 ξ A =
        positiveFKLaw H q p hq hp hp1 η (d A) := by
      calc
        _ = ∑ B : Configuration G,
            if d A = d B then positiveFKLaw G q p hq hp hp1 ξ B else 0 := hsum.symm
        _ = _ := by simpa using hmass
    rw [positiveFKLaw_apply hq hp hp1 ξ A,
      positiveFKLaw_apply hq hp hp1 η (d A)] at hmass'
    have hleft : 0 ≤ positiveFKProbability q p ξ A :=
      positiveFKProbability_nonneg_transfer hq hp hp1 ξ A
    have hright : 0 ≤ positiveFKProbability q p η (d A) :=
      positiveFKProbability_nonneg_transfer hq hp hp1 η (d A)
    exact (ENNReal.ofReal_eq_ofReal_iff hleft hright).mp hmass'
  unfold positiveFKEventProbability
  calc
    (∑ A : Configuration G,
        if A ∈ d ⁻¹' S then positiveFKProbability q p ξ A else 0) =
      ∑ A : Configuration G,
        if d A ∈ S then positiveFKProbability q p η (d A) else 0 := by
          apply Finset.sum_congr rfl
          intro A hA
          simp only [Set.mem_preimage]
          split_ifs <;> simp [hpoint A]
    _ = ∑ B : Configuration H,
        if B ∈ S then positiveFKProbability q p η B else 0 := by
          exact Equiv.sum_comp d
            (fun B : Configuration H =>
              if B ∈ S then positiveFKProbability q p η B else 0)

end
end PottsContinuity.DualityExt
