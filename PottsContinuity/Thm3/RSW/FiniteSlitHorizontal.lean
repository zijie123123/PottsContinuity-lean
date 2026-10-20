module

public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutSeparation
public import PottsContinuity.PlanarTopology.HorizontalWalks

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK BD12 PlanarTopology PlanarMixed.FiniteSlit
noncomputable section

/-- A horizontal interval not crossing the deleted seam is a physical slit
walk. Its support contains no vertex outside the original horizontal interval. -/
theorem finiteSlit_horizontal_walk (M : ℕ) (x y : ℤ) (hM : 1 ≤ M)
    (u v : Vertex M x) (huv : u.val.2 = v.val.2)
    (hseam : u.val.2 ≤ y ∨ max u.val.1 v.val.1 ≤ x-1 ∨ x ≤ min u.val.1 v.val.1) :
    ∃ p : (graph M x y).Walk u v,
      ∀ w ∈ p.support,
        min u.val.1 v.val.1 ≤ w.val.1 ∧ w.val.1 ≤ max u.val.1 v.val.1 ∧
          w.val.2 = u.val.2 := by
  classical
  let S : Set LatticeVertex := {z | min u.val.1 v.val.1 ≤ z.1 ∧
    z.1 ≤ max u.val.1 v.val.1 ∧ z.2 = u.val.2}
  have hu := (mem_rectangle_iff M x hM u.val).mp u.property
  have hv := (mem_rectangle_iff M x hM v.val).mp v.property
  have hrect : ∀ z ∈ S, z ∈ PD.FK.latticeRectangle (x-(M:ℤ),0) (2*M-1) M := by
    intro z hz
    apply (mem_rectangle_iff M x hM z).mpr
    dsimp only [S, Set.mem_ofPred_eq] at hz
    constructor
    · exact le_trans (le_min hu.1 hv.1) hz.1
    constructor
    · exact le_trans hz.2.1 (max_le hu.2.1 hv.2.1)
    · rw [hz.2.2]
      exact hu.2.2
  let f : (PD.FK.squareLattice.induce S) →g graph M x y := {
    toFun := fun z => ⟨z.val, hrect z.val z.property⟩
    map_rel' := by
      intro a b hab
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      refine ⟨hab, ?_⟩
      change ¬ (y < a.2 ∧ y < b.2 ∧
        ((a.1 = x-1 ∧ b.1 = x) ∨ (b.1 = x-1 ∧ a.1 = x)))
      change min u.val.1 v.val.1 ≤ a.1 ∧ a.1 ≤ max u.val.1 v.val.1 ∧ a.2 = u.val.2 at ha
      change min u.val.1 v.val.1 ≤ b.1 ∧ b.1 ≤ max u.val.1 v.val.1 ∧ b.2 = u.val.2 at hb
      rcases hseam with h | h | h <;> omega }
  obtain ⟨p, hp⟩ := horizontal_walk_between u.val.1 v.val.1 u.val.2
  let P := p.copy (show (u.val.1,u.val.2) = u.val from rfl)
    (show (v.val.1,u.val.2) = v.val from Prod.ext rfl huv)
  have hP : ∀ z ∈ P.support, z ∈ S := by
    intro z hz
    rw [SimpleGraph.Walk.support_copy] at hz
    exact hp z hz
  let Q := (P.induce S hP).map f
  refine ⟨Q.copy (Subtype.ext rfl) (Subtype.ext rfl), ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_copy] at hw
  change w ∈ ((P.induce S hP).map f).support at hw
  rw [SimpleGraph.Walk.support_map] at hw
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
  exact z.property

end
end PottsContinuity.RSW
