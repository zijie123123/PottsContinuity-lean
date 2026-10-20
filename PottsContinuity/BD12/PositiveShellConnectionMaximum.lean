module

public import PottsContinuity.BD12.PositiveSeedConnectionOSSS
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! The finite sum and genuine maximum of endpoint-to-shell connection
probabilities used when averaging DRT's boundary-seed explorations. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance positiveShellMaxEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveShellMaxEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Sum over the literal radius shells 1,...,n of the actual probability that u
is connected to at least one vertex of that shell. -/
def positiveShellConnectionSum (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ))
    (r : V → ℕ) (n : ℕ) (u : V) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, finitePositiveMean w (fun A =>
    if FKC.FiniteFK.actualMultiClusterConnected G (finiteRadiusShell r k) A u then 1 else 0)

/-- Maximum of those shell sums over all vertices of a nonempty finite graph.
There is no empty-carrier default: existence of a vertex is explicit. -/
def positiveShellConnectionMaximum [Nonempty V] (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ)) (r : V → ℕ) (n : ℕ) : ℝ :=
  (Finset.univ.image (positiveShellConnectionSum G w r n)).max'
    (Finset.univ_nonempty.image _)

/-- Every actual vertex shell sum is bounded by the actual finite maximum. -/
theorem positiveShellConnectionSum_le_maximum [Nonempty V]
    (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ)) (r : V → ℕ) (n : ℕ) (u : V) :
    positiveShellConnectionSum G w r n u ≤ positiveShellConnectionMaximum G w r n := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩

end
end PottsContinuity.BD12
