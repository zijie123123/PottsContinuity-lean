module

public import PottsContinuity.BD12.PositiveOneArmComparison
public import PottsContinuity.BD12.DRTRadiusSum
public import PottsContinuity.BD12.PositiveShellConnectionMaximum
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Nat.Dist

/-! Compare actual shell sums to centred one-arm sums by radius differences.
All metric hypotheses are explicit structural inequalities on vertex functions. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance positiveCentredSumEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveCentredSumEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Actual centred one-arm sum over radii 0,...,n-1. -/
def positiveCentredOneArmSum (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ))
    (d : V → V → ℕ) (n : ℕ) (u : V) : ℝ :=
  ∑ j ∈ Finset.range n, finitePositiveMean w (radiusOneArmIndicator G (d u) u j)

/-- Genuine maximum over the nonempty finite vertex carrier. -/
def positiveCentredOneArmMaximum [Nonempty V] (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ)) (d : V → V → ℕ) (n : ℕ) : ℝ :=
  (Finset.univ.image (positiveCentredOneArmSum G w d n)).max' (Finset.univ_nonempty.image _)

theorem positiveCentredOneArmSum_le_maximum [Nonempty V]
    (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ)) (d : V → V → ℕ) (n : ℕ) (u : V) :
    positiveCentredOneArmSum G w d n u ≤ positiveCentredOneArmMaximum G w d n := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩

/-- Source factor two for a fixed endpoint, with the radius-n endpoint term
retained correctly by the antitone sequence estimate. -/
theorem positiveShellConnectionSum_le_twice_centred
    (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ))
    (r : V → ℕ) (d : V → V → ℕ) (n : ℕ) (u : V) (hr : r u ≤ n)
    (hd0 : d u u = 0) (hdstep : ∀ {x y}, G.Adj x y → d u y ≤ d u x + 1)
    (hdom : ∀ v, Nat.dist (r v) (r u) ≤ d u v) :
    positiveShellConnectionSum G w r n u ≤ 2 * positiveCentredOneArmSum G w d n u := by
  let a := fun j => finitePositiveMean w (radiusOneArmIndicator G (d u) u j)
  have ha (j : ℕ) : 0 ≤ a j := finitePositiveMean_nonneg w _
    (fun A => (finiteConnectionToSetIndicator_mem_Icc G u (finiteRadiusShell (d u) j) A).1)
  have ham : Antitone a := positive_radius_one_arm_antitone G w (d u) u hd0 hdstep
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 n, a (Nat.dist k (r u)) :=
      Finset.sum_le_sum (fun k _ => positive_seed_shell_connection_le_one_arm G w r (d u) u k hd0 hdstep hdom)
    _ ≤ _ := drt_radius_sum_le_twice_partial_sum a ha ham n (r u) hr

/-- The actual maximum of shell sums is at most twice the actual maximum
centred one-arm sum, on a radius-n finite vertex domain. -/
theorem positiveShellConnectionMaximum_le_twice_centred [Nonempty V]
    (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ))
    (r : V → ℕ) (d : V → V → ℕ) (n : ℕ) (hr : ∀ u, r u ≤ n)
    (hd0 : ∀ u, d u u = 0) (hdstep : ∀ u {x y}, G.Adj x y → d u y ≤ d u x + 1)
    (hdom : ∀ u v, Nat.dist (r v) (r u) ≤ d u v) :
    positiveShellConnectionMaximum G w r n ≤ 2 * positiveCentredOneArmMaximum G w d n := by
  apply Finset.max'_le
  intro y hy
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hy
  exact (positiveShellConnectionSum_le_twice_centred G w r d n u (hr u) (hd0 u) (hdstep u) (hdom u)).trans
    (mul_le_mul_of_nonneg_left (positiveCentredOneArmSum_le_maximum G w d n u) (by norm_num))

end
end PottsContinuity.BD12
