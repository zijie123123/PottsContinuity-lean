module

public import PottsContinuity.PlanarTopology.KSTRectangleRealization
public import PottsContinuity.PlanarTopology.InterlacedPaths
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Interlacing on an arbitrary horizontal boundary line, using the original
walks and allowing endpoint equalities. -/
theorem band_interlaced_walks_intersect (bottom : ℤ) {u v x y : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (q : PD.squareLattice.Walk x y)
    (hu : u.2 = bottom) (hv : v.2 = bottom) (hx : x.2 = bottom) (hy : y.2 = bottom)
    (hux : u.1 ≤ x.1) (hxv : x.1 ≤ v.1) (hvy : v.1 ≤ y.1)
    (hp : ∀ z ∈ p.support, bottom ≤ z.2)
    (hq : ∀ z ∈ q.support, bottom ≤ z.2) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  let e := latticeTranslationIso (0,-bottom)
  have eu : e u = (u.1,0) := by ext <;> dsimp [e,latticeTranslationIso,latticeTranslate] <;> omega
  have ev : e v = (v.1,0) := by ext <;> dsimp [e,latticeTranslationIso,latticeTranslate] <;> omega
  have ex : e x = (x.1,0) := by ext <;> dsimp [e,latticeTranslationIso,latticeTranslate] <;> omega
  have ey : e y = (y.1,0) := by ext <;> dsimp [e,latticeTranslationIso,latticeTranslate] <;> omega
  let P := (p.map e.toHom).copy eu ev
  let Q := (q.map e.toHom).copy ex ey
  have hP : ∀ z ∈ P.support, 0 ≤ z.2 := by
    intro z hz
    rw [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    change 0 ≤ w.2+ -bottom
    have := hp w hw
    omega
  have hQ : ∀ z ∈ Q.support, 0 ≤ z.2 := by
    intro z hz
    rw [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    change 0 ≤ w.2+ -bottom
    have := hq w hw
    omega
  obtain ⟨z,hzp,hzq⟩ := upperHalfPlane_interlaced_walks_intersect
    u.1 x.1 v.1 y.1 P Q hux hxv hvy hP hQ
  rw [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map] at hzp hzq
  obtain ⟨a,ha,hea⟩ := List.mem_map.mp hzp
  obtain ⟨b,hb,heb⟩ := List.mem_map.mp hzq
  have hab : a = b := e.injective (hea.trans heb.symm)
  exact ⟨a,ha,hab ▸ hb⟩

end
end PottsContinuity.PlanarTopology
