module

public import PottsContinuity.PD.Duality.RayIndexSeparation
public import PottsContinuity.PlanarTopology.InterlacedPaths
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-! # The signed ray index of four supported lattice walks -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality

/-- Cyclic top/right/bottom/left walks have signed ray index -1 around every
point satisfying the four strict/non-strict half-plane bounds. -/
theorem four_strip_closedWalk_rayIndex_eq_neg_one
    (x : LatticeVertex) {u₁ u₂ u₃ u₄ : LatticeVertex}
    (pT : PD.FK.squareLattice.Walk u₁ u₂)
    (pR : PD.FK.squareLattice.Walk u₂ u₃)
    (pB : PD.FK.squareLattice.Walk u₃ u₄)
    (pL : PD.FK.squareLattice.Walk u₄ u₁)
    (hT : ∀ v ∈ pT.support, x.2 ≤ v.2)
    (hR : ∀ v ∈ pR.support, x.1 ≤ v.1)
    (hB : ∀ v ∈ pB.support, v.2 < x.2)
    (hL : ∀ v ∈ pL.support, v.1 < x.1) :
    rayIndex x ((pT.append pR).append (pB.append pL)) = -1 := by
  have ht : rayIndex x pT = 0 := rayIndex_zero_of_level x pT 0
    (fun v hv => ite_eq_right (not_lt_of_ge (hT v hv)))
  have hb : rayIndex x pB = 0 := rayIndex_zero_of_level x pB 1
    (fun v hv => ite_eq_left (hB v hv))
  have hl : rayIndex x pL = 0 := rayIndex_zero_of_right x pL hL
  have hr := rayIndex_left_telescope x pR hR
  have hu₂ := hT u₂ (by simp)
  have hu₃ := hB u₃ (by simp)
  rw [ite_eq_right (not_lt_of_ge hu₂),ite_eq_left hu₃] at hr
  rw [PlanarTopology.rayIndex_append,PlanarTopology.rayIndex_append,
    PlanarTopology.rayIndex_append,ht,hr,hb,hl]
  norm_num

end PottsContinuity.RSW
