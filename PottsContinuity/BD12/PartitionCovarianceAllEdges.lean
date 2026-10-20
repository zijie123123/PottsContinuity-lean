module

public import PottsContinuity.BD12.PartitionCentredCovariance
public import PottsContinuity.BD12.MarginalCovarianceSum
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-! DRT's inner exploration covariance bound under a true larger-cube law.
All probabilities below are outer-law expectations of inner path events.
The outside coordinates remain random throughout. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
local instance partitionAllCovEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance partitionAllCovEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
variable {F O : Type*} [Fintype F] [DecidableEq F] [Fintype O] [DecidableEq O]

variable [MeasurableSpace (PD.FK.Configuration G)] [MeasurableSingletonClass (PD.FK.Configuration G)]
    [MeasurableSpace (Option G.edgeSet)] [MeasurableSingletonClass (Option G.edgeSet)]

/-- The centred covariance-sum estimate after marginalising all outer edges.
The maximum ranges only over inner vertices; neither an outside boundary
pattern nor an FK representation of the marginal is required. -/
theorem partition_connection_covariance_sum_lower_bound_all_edges
    (e : G.edgeSet ⊕ F ≃ O) (w : Finset O → Set.Ioi (0 : ℝ))
    (hw : ∀ A D, (w A : ℝ) * w D ≤ (w (A ∩ D) : ℝ) * w (A ∪ D))
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet))
    (r : V → ℕ) (d : V → V → ℕ)
    (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    (n : ℕ) (hn : 1 ≤ n) (hr : ∀ u, r u ≤ n)
    (B : Finset V) (o : V) (ho : r o = 0) (hB : ∀ b ∈ B, n ≤ r b)
    (hd0 : ∀ u, d u u = 0) (hdstep : ∀ u {x y}, G.Adj x y → d u y ≤ d u x + 1)
    (hdom : ∀ u v, Nat.dist (r v) (r u) ≤ d u v)
    (ends₁ ends₂ : G.edgeSet → V) (hends : ∀ a, a.val = s(ends₁ a, ends₂ a)) (U : ℕ → ℝ) :
    let X := fun C => finiteConnectionToSetIndicator G o B (finitePartitionProjection e C)
    let θ := finitePositiveMean w X
    ((n : ℝ) / (4 * partitionCentredOneArmMaximum G e w d n)) * (θ * (1 - θ)) ≤
      ∑ a : O, finitePositiveCovariance w X (fun C => if a ∈ C then 1 else 0) := by
  have h := partition_connection_covariance_sum_lower_bound G e w hw rank r d hstep n hn hr
    B o ho hB hd0 hdstep hdom ends₁ ends₂ hends U
  let X := fun C => finiteConnectionToSetIndicator G o B (finitePartitionProjection e C)
  have hX0 : ∀ C, 0 ≤ X C := fun C =>
    (finiteConnectionToSetIndicator_mem_Icc G o B _).1
  have hXm : Monotone X := (finiteConnectionToSetIndicator_monotone G o B).comp
    (finitePartitionProjection_monotone e)
  have hsum := finite_embedded_covariance_sum_le
    (Function.Embedding.inl.trans e.toEmbedding) w hw X hX0 hXm
  exact h.trans hsum

end
end PottsContinuity.BD12
