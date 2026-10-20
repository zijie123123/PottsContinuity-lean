module

public import PottsContinuity.Thm3.RSW.FiniteBoundary
public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# Actual finite arm events and the nonempty square-pair maximum

DCST Lemma 5, TeX lines 1489–1513. The maximum runs over ALL (m+1)^2
pairs of vertices on opposite sides of [0,m]^2, including m=0. There is no
empty-index or zero fallback. Boundary wiring changes the measure only.
-/

@[expose] public section

namespace PottsContinuity.RSW

open MeasureTheory

/-- Actual finite open connection. If an endpoint is outside V, the event is
empty by its explicit membership requirement. -/
def finiteConnectionEvent (V : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) :
    Set ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :=
  {ω | ∃ hx : x ∈ V, ∃ hy : y ∈ V, (rcOpenGraph V ω).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

/-- The finite-box actual arm event, without virtual boundary paths. -/
def finiteArmEvent (N k : ℕ) :
    Set ((squareLattice.induce (box N : Set (ℤ × ℤ))).edgeSet → Bool) :=
  {ω | ∃ y ∈ vertexBoundary (box k), ω ∈ finiteConnectionEvent (box N) (0, 0) y}

/-- Free finite-box one-arm probability. -/
noncomputable def finiteArmProbability (θ : PD.FK.Parameters) (N k : ℕ) : ℝ :=
  finiteBoundaryEventProbability (box N) θ (PD.FK.frozenBoundaryCondition (box N) 0)
    (fun ω => ω ∈ finiteArmEvent N k)

/-- Actual free probability of a connection between two prescribed opposite-side
vertices of the square. The indices include BOTH endpoint heights 0 and m. -/
noncomputable def squarePairProbability (θ : PD.FK.Parameters) (m : ℕ)
    (i j : Fin (m + 1)) : ℝ :=
  finiteBoundaryEventProbability (latticeRectangle 0 m 0 m) θ
    (PD.FK.frozenBoundaryCondition (latticeRectangle 0 m 0 m) 0)
    (fun ω => ω ∈ finiteConnectionEvent (latticeRectangle 0 m 0 m)
      (0, (i.val : ℤ)) ((m : ℤ), (j.val : ℤ)))

/-- The genuine finite maximum over the nonempty set of opposite-side pairs. -/
noncomputable def maxSquarePairProbability (θ : PD.FK.Parameters) (m : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin (m + 1) × Fin (m + 1))).sup' Finset.univ_nonempty
    (fun ij => squarePairProbability θ m ij.1 ij.2)

/-- Every pair probability is nonnegative. -/
theorem squarePairProbability_nonneg (θ : PD.FK.Parameters) (m : ℕ)
    (i j : Fin (m + 1)) : 0 ≤ squarePairProbability θ m i j := ENNReal.toReal_nonneg

/-- Every source pair is bounded by the actual finite maximum. -/
theorem squarePairProbability_le_max (θ : PD.FK.Parameters) (m : ℕ)
    (i j : Fin (m + 1)) : squarePairProbability θ m i j ≤ maxSquarePairProbability θ m := by
  exact Finset.le_sup' (fun ij : Fin (m + 1) × Fin (m + 1) =>
    squarePairProbability θ m ij.1 ij.2) (Finset.mem_univ (i, j))

/-- The maximum is nonnegative even at m=0. -/
theorem maxSquarePairProbability_nonneg (θ : PD.FK.Parameters) (m : ℕ) :
    0 ≤ maxSquarePairProbability θ m :=
  le_trans (squarePairProbability_nonneg θ m 0 0) (squarePairProbability_le_max θ m 0 0)

/-- An honest bound on every square pair bounds the genuine maximum. -/
theorem maxSquarePairProbability_le (θ : PD.FK.Parameters) (m : ℕ) (c : ℝ)
    (h : ∀ i j : Fin (m + 1), squarePairProbability θ m i j ≤ c) :
    maxSquarePairProbability θ m ≤ c := by
  apply Finset.sup'_le
  intro ij _
  exact h ij.1 ij.2

end PottsContinuity.RSW
