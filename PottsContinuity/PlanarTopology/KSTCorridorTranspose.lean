module

public import PottsContinuity.PlanarTopology.KSTCorridor
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Interchanging the two lattice coordinates preserves nearest neighbours. -/
abbrev latticeTransposeIso : PD.squareLattice ≃g PD.squareLattice where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro u v
    simp only [squareLattice_adj_iff]
    change ((u.2+1 = v.2 ∨ v.2+1 = u.2) ∧ u.1 = v.1 ∨
      u.2 = v.2 ∧ (u.1+1 = v.1 ∨ v.1+1 = u.1)) ↔ _
    omega

/-- The coordinate-interchanged original walk, retaining its chronology. -/
abbrev transposeWalk {u v : LatticeVertex} (p : PD.squareLattice.Walk u v) :=
  p.map latticeTransposeIso.toHom

@[simp] theorem transposeWalk_twice {u v : LatticeVertex} (p : PD.squareLattice.Walk u v) :
    transposeWalk (transposeWalk p) = p := by
  simp only [transposeWalk,SimpleGraph.Walk.map_map]
  change p.map SimpleGraph.Hom.id = p
  exact p.map_id

@[simp] theorem mem_transposeWalk_support {u v : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (z : LatticeVertex) :
    z ∈ (transposeWalk p).support ↔ z.swap ∈ p.support := by
  rw [SimpleGraph.Walk.support_map,List.mem_map]
  constructor
  · rintro ⟨w,hw,he⟩
    change w.swap = z at he
    rw [← he]
    exact hw
  · intro hz
    exact ⟨z.swap,hz,rfl⟩

end
end PottsContinuity.PlanarTopology
