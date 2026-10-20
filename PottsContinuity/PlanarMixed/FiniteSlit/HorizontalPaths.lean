module

public import PottsContinuity.PlanarMixed.FiniteSlit.Domain
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PlanarTopology
noncomputable section

/-- A horizontal segment on either one side of the slit retains every
original bond, at every height in the finite box. -/
theorem horizontal_walk (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (u v : Vertex M x) (hrow : u.val.2 = v.val.2)
    (hside : (u.val.1 ≤ x-1 ∧ v.val.1 ≤ x-1) ∨
      (x ≤ u.val.1 ∧ x ≤ v.val.1)) :
    ∃ p : (graph M x y).Walk u v,
      ∀ w ∈ p.support,
        min u.val.1 v.val.1 ≤ w.val.1 ∧ w.val.1 ≤ max u.val.1 v.val.1 ∧
          w.val.2 = u.val.2 := by
  have hu := (mem_rectangle_iff M x (by omega) u.val).mp u.property
  have hv := (mem_rectangle_iff M x (by omega) v.val).mp v.property
  obtain ⟨r,hr⟩ := horizontal_walk_between u.val.1 v.val.1 u.val.2
  let S : Set LatticeVertex := {w | w ∈ PD.FK.latticeRectangle (x-(M:ℤ),0) (2*M-1) M ∧
    min u.val.1 v.val.1 ≤ w.1 ∧ w.1 ≤ max u.val.1 v.val.1 ∧ w.2 = u.val.2}
  have hrS : ∀ w ∈ r.support, w ∈ S := by
    intro w hw
    have hh := hr w hw
    refine ⟨(mem_rectangle_iff M x (by omega) w).mpr ?_,hh⟩
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  let φ : (PD.FK.squareLattice.induce S) →g graph M x y := {
    toFun := fun w => ⟨w.val,w.property.1⟩
    map_rel' := by
      intro a b hab
      refine ⟨hab,?_⟩
      have ha := a.property.2
      have hb := b.property.2
      change ¬ (y < a.val.2 ∧ y < b.val.2 ∧
        ((a.val.1 = x-1 ∧ b.val.1 = x) ∨ (b.val.1 = x-1 ∧ a.val.1 = x)))
      rcases hside with hs | hs <;> omega }
  have hvEq : (v.val.1,u.val.2) = v.val := Prod.ext rfl hrow
  let p := ((r.induce S hrS).map φ).copy
    (show φ ⟨(u.val.1,u.val.2),hrS _ r.start_mem_support⟩ = u from rfl)
    (show φ ⟨(v.val.1,u.val.2),hrS _ r.end_mem_support⟩ = v from Subtype.ext hvEq)
  refine ⟨p,?_⟩
  intro w hw
  change w ∈ (((r.induce S hrS).map φ).copy _ _).support at hw
  rw [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map] at hw
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
  exact z.property.2

end
end PottsContinuity.PlanarMixed.FiniteSlit
