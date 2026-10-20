module

public import PottsContinuity.BD12.PositiveCentredCovariance
public import PottsContinuity.BD12.MarginalCovariance
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
local instance partitionCovEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance partitionCovEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
variable {F O : Type*} [Fintype F] [DecidableEq F] [Fintype O] [DecidableEq O]

/-- Maximum over INNER vertices of the actual outer-law inner one-arm sums. -/
def partitionCentredOneArmMaximum (e : G.edgeSet ⊕ F ≃ O)
    (w : Finset O → Set.Ioi (0 : ℝ)) (d : V → V → ℕ) (n : ℕ) : ℝ :=
  (Finset.univ.image (fun u => ∑ j ∈ Finset.range n,
    finitePositiveMean w (fun C => radiusOneArmIndicator G (d u) u j
      (finitePartitionProjection e C)))).max' (Finset.univ_nonempty.image _)

theorem partitionCentredOneArmMaximum_eq (e : G.edgeSet ⊕ F ≃ O)
    (w : Finset O → Set.Ioi (0 : ℝ)) (d : V → V → ℕ) (n : ℕ) :
    positiveCentredOneArmMaximum G (finitePartitionMarginalWeight e w) d n =
      partitionCentredOneArmMaximum G e w d n := by
  have hf : positiveCentredOneArmSum G (finitePartitionMarginalWeight e w) d n =
      fun u => ∑ j ∈ Finset.range n, finitePositiveMean w (fun C =>
        radiusOneArmIndicator G (d u) u j (finitePartitionProjection e C)) := by
    funext u
    simp only [positiveCentredOneArmSum, finitePositiveMean, finitePartitionMarginalWeight_mean]
  unfold positiveCentredOneArmMaximum partitionCentredOneArmMaximum
  simp only [hf]


variable [MeasurableSpace (PD.FK.Configuration G)] [MeasurableSingletonClass (PD.FK.Configuration G)]
    [MeasurableSpace (Option G.edgeSet)] [MeasurableSingletonClass (Option G.edgeSet)]

/-- The centred covariance-sum estimate after marginalising all outer edges.
The maximum ranges only over inner vertices; neither an outside boundary
pattern nor an FK representation of the marginal is required. -/
theorem partition_connection_covariance_sum_lower_bound
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
      ∑ a, finitePositiveCovariance w X (fun C => if e (Sum.inl a) ∈ C then 1 else 0) := by
  have h := positive_connection_covariance_sum_lower_bound G rank r d hstep n hn hr B o ho hB
    hd0 hdstep hdom ends₁ ends₂ hends (finitePartitionMarginalWeight e w)
    (finitePartitionMarginalWeight_lattice_condition e w hw) U
  dsimp only at h ⊢
  simp only [partitionCentredOneArmMaximum_eq, finitePartitionMarginalWeight_edge_covariance,
    finitePositiveMean, finitePartitionMarginalWeight_mean] at h
  exact h

end
end PottsContinuity.BD12
