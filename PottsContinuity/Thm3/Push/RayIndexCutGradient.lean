module

public import PottsContinuity.PD.Duality.RayIndex
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.Duality

/-- A single traversal of a vertical bond changes the ray index across the
crossing horizontal bond. The walk need not be closed, but its edges may not
repeat. This supplies the nonzero jump needed for a simple frontier cycle. -/
theorem rayIndex_horizontal_jump_ne_zero (x y : ℤ) {u v : LatticeVertex}
    (p : squareLattice.Walk u v) (hn : p.edges.Nodup)
    (he : s((x,y-1),(x,y)) ∈ p.edges) :
    rayIndex (x,y) p ≠ rayIndex (x+1,y) p := by
  induction p with
  | nil => simp at he
  | @cons u z v huz p ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases hh : s(u,z) = s((x,y-1),(x,y))
    · have htail : s((x,y-1),(x,y)) ∉ p.edges := by
        have hnot : s(u,z) ∉ p.edges := hn'.1
        simpa only [hh] using hnot
      have hidx := rayIndex_horizontal_invariant x y p htail
      rcases Sym2.eq_iff.mp hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simp only [rayIndex, rayStep] at *
        split_ifs at * <;> omega
      · simp only [rayIndex, rayStep] at *
        split_ifs at * <;> omega
    · have htail : s((x,y-1),(x,y)) ∈ p.edges := by
        rcases List.mem_cons.mp he with hhead | htail
        · exact (hh hhead.symm).elim
        · exact htail
      have hne := ih hn'.2 htail
      have hs := rayStep_horizontal_invariant x y u z huz hh
      simp only [rayIndex]
      omega

/-- Explicit endpoint correction for the vertical ray-index derivative. -/
def rayRowMarker (x y : ℤ) (z : LatticeVertex) : ℤ :=
  if z.2 = y ∧ x ≤ z.1 then 1 else 0

/-- The horizontal-bond counterpart of the nonzero ray-index jump. Endpoint
corrections are retained, so the statement is valid for arbitrary open walks. -/
theorem rayIndex_vertical_jump_corrected_ne_zero (x y : ℤ) {u v : LatticeVertex}
    (p : squareLattice.Walk u v) (hn : p.edges.Nodup)
    (he : s((x-1,y),(x,y)) ∈ p.edges) :
    rayIndex (x,y+1) p - rayIndex (x,y) p - rayRowMarker x y u + rayRowMarker x y v ≠ 0 := by
  induction p with
  | nil => simp at he
  | @cons u z v huz p ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases hh : s(u,z) = s((x-1,y),(x,y))
    · have htail : s((x-1,y),(x,y)) ∉ p.edges := by
        have hnot : s(u,z) ∉ p.edges := hn'.1
        simpa only [hh] using hnot
      have hidx := rayIndex_vertical_difference x y p htail
      change rayIndex (x,y+1) p - rayIndex (x,y) p =
        rayRowMarker x y z - rayRowMarker x y v at hidx
      rcases Sym2.eq_iff.mp hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simp only [rayIndex, rayStep, rayRowMarker, true_and] at *
        split_ifs at * <;> omega
      · simp only [rayIndex, rayStep, rayRowMarker, true_and] at *
        split_ifs at * <;> omega
    · have htail : s((x-1,y),(x,y)) ∈ p.edges := by
        rcases List.mem_cons.mp he with hhead | htail
        · exact (hh hhead.symm).elim
        · exact htail
      have hne := ih hn'.2 htail
      have hs := rayStep_vertical_difference x y u z huz hh
      change rayStep (x,y+1) u z - rayStep (x,y) u z =
        rayRowMarker x y u - rayRowMarker x y z at hs
      simp only [rayIndex]
      omega

/-- On a closed edge-simple walk, a crossed horizontal bond has a nonzero
vertical index jump, with no endpoint term left over. -/
theorem rayIndex_vertical_jump_ne_zero (x y : ℤ) {u : LatticeVertex}
    (p : squareLattice.Walk u u) (hn : p.edges.Nodup)
    (he : s((x-1,y),(x,y)) ∈ p.edges) :
    rayIndex (x,y+1) p ≠ rayIndex (x,y) p := by
  have h := rayIndex_vertical_jump_corrected_ne_zero x y p hn he
  omega

end PottsContinuity.Push
