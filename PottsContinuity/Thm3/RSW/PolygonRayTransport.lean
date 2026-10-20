module

public import PottsContinuity.Thm3.RSW.PolygonRayLocation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section

private theorem polygonRay_ext {m : ℕ} (P Q : FKC.LatticePolygon m)
    (h : P.vertex = Q.vertex) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Point location for any polygon with the same ordered vertices as an
actual simple lattice cycle, with no separate enclosure premise. -/
theorem latticePolygon_mem_domain_of_rayIndex_ne_zero
    {z : LatticeVertex} (p : PD.FK.squareLattice.Walk z z)
    (P : FKC.LatticePolygon ((p.map polygonRayLatticeHom).length-3))
    (hp : p.IsCycle)
    (hvertices : ∀ i : ZMod ((p.map polygonRayLatticeHom).length-3+3), P.vertex i = p.getVert i.val)
    (x : LatticeVertex) (hindex : rayIndex x p ≠ 0)
    (hnot : ∀ i : ZMod ((p.map polygonRayLatticeHom).length-3+3), P.vertex i ≠ x) :
    FKC.latticeEmbed ⟨1,zero_lt_one⟩ x ∈ P.domain ⟨1,zero_lt_one⟩ := by
  let r := p.map polygonRayLatticeHom
  have hr : r.IsCycle := (p.isCycle_map_iff_of_injective
    (show Function.Injective polygonRayLatticeHom from fun _ _ h => h)).mpr hp
  let Q := FKC.latticePolygonOfCycle hr
  have hPQ : P = Q := by
    have hv : P.vertex = Q.vertex := by
      funext i
      rw [hvertices i]
      change p.getVert i.val = (p.map polygonRayLatticeHom).getVert i.val
      rw [SimpleGraph.Walk.getVert_map]
      rfl
    exact polygonRay_ext P Q hv
  have hx : x ∉ p.support := by
    intro hx
    have hxR : x ∈ r.support := by
      rw [SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨x,hx,rfl⟩
    have hxRange : x ∈ Set.range r.support.get := by
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxR
      exact ⟨i,hi⟩
    rw [← FKC.latticePolygonOfCycle_vertex_support hr] at hxRange
    obtain ⟨i,hi⟩ := hxRange
    exact hnot i (by rw [hPQ]; exact hi)
  rw [hPQ]
  exact latticePolygonOfCycle_mem_domain_of_rayIndex_ne_zero p hp x hx hindex

end
end PottsContinuity.RSW
