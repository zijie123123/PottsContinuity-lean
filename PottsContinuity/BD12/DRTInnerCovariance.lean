module

public import PottsContinuity.BD12.PartitionCovarianceAllEdges
public import PottsContinuity.BD12.DRTHybridFirstCross
public import Mathlib.Tactic
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
local instance innerCovInnerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance innerCovInnerEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance innerCovOuterEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance innerCovOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
variable {F : Type*} [Fintype F] [DecidableEq F]

/-- Generic positive-weight covariance agrees with the actual DRT covariance. -/
theorem drt_positiveCovariance_eq (q : Set.Ioi (0 : ℝ)) (ξ : PD.FK.BoundaryCondition W)
    (J : H.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (f g : PD.FK.Configuration H → ℝ) :
    finitePositiveCovariance (drtPositiveWeight H q ξ J β) f g = drtCovariance H q ξ J β f g := by
  simp only [finitePositiveCovariance, finitePositiveMean, drt_pinnedMean_empty_eq, drtCovariance]

variable [MeasurableSpace (PD.FK.Configuration G)] [MeasurableSingletonClass (PD.FK.Configuration G)]
    [MeasurableSpace (Option G.edgeSet)] [MeasurableSingletonClass (Option G.edgeSet)]

/-- The law is the actual full outer FK law; only the exploration is inner.
The sum includes ALL outer edges, while the one-arm maximum ranges only over
inner vertices and uses their restricted paths in that same outer law. -/
theorem drt_inner_connection_covariance_sum_lower_bound
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
    (J : H.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) (U : ℕ → ℝ) :
    let X := fun C => finiteConnectionToSetIndicator G o B (finitePartitionProjection e C)
    let θ := drtMean H q ξ J β X
    ((n : ℝ) / (4 * partitionCentredOneArmMaximum G e (drtPositiveWeight H q ξ J β) d n)) *
        (θ * (1 - θ)) ≤
      ∑ a : H.edgeSet, drtCovariance H q ξ J β X (fun C => if a ∈ C then 1 else 0) := by
  have h := partition_connection_covariance_sum_lower_bound_all_edges G e (drtPositiveWeight H q ξ J β)
    (drtWeight_lattice_condition H q hq ξ J β) rank r d hstep n hn hr B o ho hB
    hd0 hdstep hdom ends₁ ends₂ hends U
  simp only [finitePositiveMean, drt_pinnedMean_empty_eq, drt_positiveCovariance_eq] at h
  exact h

end
end PottsContinuity.BD12
