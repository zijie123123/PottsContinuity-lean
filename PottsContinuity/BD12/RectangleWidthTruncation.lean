module

public import PottsContinuity.BD12.RectangleConfinedWalk
public import PottsContinuity.BD12.WalkRadiusPrefix
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! First-hit truncation in the horizontal coordinate narrows a rectangle
crossing while retaining the original lower-left side and vertical bounds. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section

/-- A crossing to a more distant right side reaches every nearer right side. -/
theorem horizontalRectangle_mono_width (a : LatticeVertex) (w W h : ℕ) (hw : w ≤ W) :
    horizontalRectangle a W h ⊆ horizontalRectangle a w h := by
  intro ω hω
  obtain ⟨u,v,p,hu,hv,hall⟩ := (horizontalRectangle_iff_confined_open_walk a W h ω).mp hω
  let G := (PD.rcInfiniteOpenGraph ω).induce (latticeRectangle a W h : Set LatticeVertex)
  let u' : RectangleVertex a W h := ⟨u,hall u p.start_mem_support⟩
  let v' : RectangleVertex a W h := ⟨v,hall v p.end_mem_support⟩
  let r : RectangleVertex a W h → ℕ := fun z => (z.val.1-a.1).toNat
  have hstep : ∀ {x y}, G.Adj x y → r y ≤ r x+1 := by
    intro x y hxy
    obtain ⟨he,_⟩ := (rcInfiniteOpenGraph_adj ω x.val y.val).mp hxy
    have hadj := PD.squareLattice.mem_edgeSet.mp he
    rw [squareLattice_adj_iff] at hadj
    dsimp only [r]
    omega
  have hur : r u' = 0 := by dsimp only [r,u']; omega
  have hvr : r v' = W := by dsimp only [r,v']; omega
  have p' : G.Walk u' v' := p.induce _ hall
  obtain ⟨z,q,hz,hq⟩ := walk_reaches_radius_inside_ball r hstep p' w
    (by rw [hur]; omega) (by rw [hvr]; exact hw)
  have hz1 : z.val.1 = a.1+(w : ℤ) := by
    have hb := (mem_latticeRectangle a z.val W h).mp z.property
    dsimp only [r] at hz
    omega
  let f : G →g PD.rcInfiniteOpenGraph ω := { toFun := Subtype.val, map_rel' := fun h => h }
  apply (horizontalRectangle_iff_confined_open_walk a w h ω).mpr
  refine ⟨u,z.val,q.map f,hu,hz1,?_⟩
  intro t ht
  rw [SimpleGraph.Walk.support_map] at ht
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ht
  have hb := (mem_latticeRectangle a x.val W h).mp x.property
  have hxr := hq x hx
  dsimp only [r] at hxr
  rw [mem_latticeRectangle]
  change (a.1 ≤ x.val.1 ∧ x.val.1 ≤ a.1+(w : ℤ)) ∧ a.2 ≤ x.val.2 ∧ x.val.2 ≤ a.2+(h : ℤ)
  omega

end
end PottsContinuity.BD12
