module

public import PottsContinuity.Thm3.RSW.FourStripRayIndex
public import PottsContinuity.Thm3.Easy.P5ClosedWalkCycle
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! # Four supported actual walks yield an actual simple nonzero-index cycle -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality

/-- The cycle is taken in the ORIGINAL sampled graph G, with its original
edges. The map to the square lattice is used only to compute its ray index.
The combinatorial cycle extraction is `Thm3.Easy.closedWalk_exists_simpleNonzeroRayIndex`. -/
theorem four_supported_walks_simple_cycle
    {X : Type*} [DecidableEq X] {G : SimpleGraph X}
    (φ : G →g PD.FK.squareLattice) (x : LatticeVertex)
    {u₁ u₂ u₃ u₄ : X}
    (pT : G.Walk u₁ u₂) (pR : G.Walk u₂ u₃)
    (pB : G.Walk u₃ u₄) (pL : G.Walk u₄ u₁)
    (hT : ∀ v ∈ pT.support, x.2 ≤ (φ v).2)
    (hR : ∀ v ∈ pR.support, x.1 ≤ (φ v).1)
    (hB : ∀ v ∈ pB.support, (φ v).2 < x.2)
    (hL : ∀ v ∈ pL.support, (φ v).1 < x.1) :
    ∃ y : X, ∃ q : G.Walk y y,
      q.IsCycle ∧ rayIndex x (q.map φ) ≠ 0 ∧
        q.edges ⊆ ((pT.append pR).append (pB.append pL)).edges := by
  let p := (pT.append pR).append (pB.append pL)
  have hindex : rayIndex x (p.map φ) = -1 := by
    simp only [p,SimpleGraph.Walk.map_append]
    apply four_strip_closedWalk_rayIndex_eq_neg_one
    · intro v hv
      rw [SimpleGraph.Walk.support_map,List.mem_map] at hv
      obtain ⟨w,hw,rfl⟩ := hv
      exact hT w hw
    · intro v hv
      rw [SimpleGraph.Walk.support_map,List.mem_map] at hv
      obtain ⟨w,hw,rfl⟩ := hv
      exact hR w hw
    · intro v hv
      rw [SimpleGraph.Walk.support_map,List.mem_map] at hv
      obtain ⟨w,hw,rfl⟩ := hv
      exact hB w hw
    · intro v hv
      rw [SimpleGraph.Walk.support_map,List.mem_map] at hv
      obtain ⟨w,hw,rfl⟩ := hv
      exact hL w hw
  apply Thm3.Easy.closedWalk_exists_simpleNonzeroRayIndex φ x p
  rw [hindex]
  norm_num

end PottsContinuity.RSW
