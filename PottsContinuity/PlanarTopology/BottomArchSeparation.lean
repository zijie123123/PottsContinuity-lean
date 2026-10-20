module

public import PottsContinuity.PlanarTopology.OpenArchRayIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- The complementary telescoping formula when every visit just left of the
ray lies below its starting row. -/
theorem rayIndex_telescope_of_high_column_absent (v : LatticeVertex)
    {s t : LatticeVertex} (p : PD.squareLattice.Walk s t)
    (hp : ∀ z ∈ p.support, v.2 ≤ z.2 → z.1 ≠ v.1-1) :
    rayIndex v p =
      ((if s.2 < v.2 then 1 else 0)-1) * (if v.1 ≤ s.1 then 1 else 0) -
      ((if t.2 < v.2 then 1 else 0)-1) * (if v.1 ≤ t.1 then 1 else 0) := by
  induction p with
  | nil => simp [rayIndex]
  | @cons s z t hadj p ih =>
    have hs := hp s (by simp)
    have hz := hp z (by simp)
    have hstep : rayStep v s z =
        ((if s.2 < v.2 then 1 else 0)-1) * (if v.1 ≤ s.1 then 1 else 0) -
        ((if z.2 < v.2 then 1 else 0)-1) * (if v.1 ≤ z.1 then 1 else 0) := by
      have hcoord := (squareLattice_adj_iff _ _).mp hadj
      rcases hcoord with ⟨hx | hx,hy⟩ | ⟨hx,hy⟩ <;>
        dsimp [rayStep] <;> split_ifs <;> omega
    rw [rayIndex,hstep,ih (fun z hz => hp z (by simp [hz]))]
    omega

end
end PottsContinuity.PlanarTopology
