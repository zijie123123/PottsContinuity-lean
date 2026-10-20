module

public import PottsContinuity.BD12.DRTInnerCovariance
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-! The inner-shell covariance estimate under an actual outer finite FK law,
for all real q>=1 and arbitrary outer boundary partitions and couplings. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section
variable {V W : Type*} [Fintype V] [Nonempty V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W)
local instance innerDiffInnerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance innerDiffInnerEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance innerDiffOuterEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance innerDiffOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
variable {F : Type*} [Fintype F] [DecidableEq F]

variable [MeasurableSpace (PD.FK.Configuration G)] [MeasurableSingletonClass (PD.FK.Configuration G)]
    [MeasurableSpace (Option G.edgeSet)] [MeasurableSingletonClass (Option G.edgeSet)]

/-- Actual outer-law differential inequality obtained by exploring only the
inner edges. Every revealment and covariance estimate is discharged. -/
theorem drt_inner_connection_differential_inequality
    (e : G.edgeSet ⊕ F ≃ H.edgeSet)
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet))
    (r : V → ℕ) (d : V → V → ℕ)
    (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    (n : ℕ) (hn : 1 ≤ n) (hr : ∀ u, r u ≤ n)
    (B : Finset V) (o : V) (ho : r o = 0) (hB : ∀ b ∈ B, n ≤ r b)
    (hd0 : ∀ u, d u u = 0) (hdstep : ∀ u {x y}, G.Adj x y → d u y ≤ d u x + 1)
    (hdom : ∀ u v, Nat.dist (r v) (r u) ≤ d u v)
    (ends₁ ends₂ : G.edgeSet → V) (hends : ∀ a, a.val = s(ends₁ a, ends₂ a))
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (ξ : PD.FK.BoundaryCondition W)
    (J : H.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) (U : ℕ → ℝ)
    (a : ℝ) (ha : 0 ≤ a)
    (hcoeff : ∀ b, a ≤ (J b : ℝ) / (Real.exp ((β : ℝ) * (J b : ℝ)) - 1)) :
    let X := fun C => finiteConnectionToSetIndicator G o B (finitePartitionProjection e C)
    let θ := drtMean H q ξ J β X
    ((a * (n : ℝ)) / (4 * partitionCentredOneArmMaximum G e (drtPositiveWeight H q ξ J β) d n)) *
        (θ * (1 - θ)) ≤
      deriv (fun t : ℝ => (∑ C, drtWeight H q ξ J t C * X C) /
        ∑ C, drtWeight H q ξ J t C) β := by
  let X := fun C => finiteConnectionToSetIndicator G o B (finitePartitionProjection e C)
  let c := fun b => drtCovariance H q ξ J β X (drtEdgeIndicator H b)
  have hX0 : ∀ C, 0 ≤ X C := fun C =>
    (finiteConnectionToSetIndicator_mem_Icc G o B _).1
  have hXm : Monotone X := (finiteConnectionToSetIndicator_monotone G o B).comp
    (finitePartitionProjection_monotone e)
  have hc (b : H.edgeSet) : 0 ≤ c b := drtCovariance_nonneg H q hq ξ J β X
    (drtEdgeIndicator H b) hX0 (drtEdgeIndicator_nonneg H b) hXm (drtEdgeIndicator_monotone H b)
  have hCov := drt_inner_connection_covariance_sum_lower_bound G H e rank r d hstep n hn hr
    B o ho hB hd0 hdstep hdom ends₁ ends₂ hends q hq ξ J β U
  have hI (b : H.edgeSet) : (fun C : PD.FK.Configuration H => if b ∈ C then (1 : ℝ) else 0) =
      drtEdgeIndicator H b := by
    funext C
    by_cases hb : b ∈ C <;> simp [drtEdgeIndicator, hb]
  simp_rw [hI] at hCov
  have hcoeffsum : a * ∑ b, c b ≤
      ∑ b, ((J b : ℝ) / (Real.exp ((β : ℝ) * (J b : ℝ)) - 1)) * c b := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right (hcoeff b) (hc b))
  have hderiv := hcoeffsum.trans (drt_russo_lower_bound H q hq ξ J β X hX0 hXm)
  have h := (mul_le_mul_of_nonneg_left hCov ha).trans hderiv
  dsimp only at h ⊢
  convert h using 1; ring

end
end PottsContinuity.BD12
