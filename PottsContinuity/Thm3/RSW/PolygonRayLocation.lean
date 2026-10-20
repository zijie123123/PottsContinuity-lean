module

public import PottsContinuity.Thm3.RSW.PolygonRayExterior
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section

/-- An integer vertex is in the closure of its southwest open unit cell. -/
theorem latticeVertex_mem_closure_southwest_cell (x : LatticeVertex) :
    FKC.latticeEmbed ⟨1,zero_lt_one⟩ x ∈
      closure (FKC.openLatticeCell ⟨1,zero_lt_one⟩ (x.1-1,x.2-1)) := by
  let a := FKC.latticeEmbed ⟨1,zero_lt_one⟩ x
  let b := FKC.latticeCellCenter ⟨1,zero_lt_one⟩ (x.1-1,x.2-1)
  have hseg : openSegment ℝ a b ⊆
      FKC.openLatticeCell ⟨1,zero_lt_one⟩ (x.1-1,x.2-1) := by
    rw [openSegment_eq_image]
    rintro w ⟨t,⟨ht,ht1⟩,rfl⟩
    simp only [FKC.openLatticeCell, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Ioo, a, b, FKC.latticeCellCenter, FKC.latticeEmbed,
      Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      Int.cast_sub, Int.cast_one,
      one_mul, smul_eq_mul]
    constructor <;> constructor <;> nlinarith
  exact closure_mono hseg
    (segment_subset_closure_openSegment (left_mem_segment ℝ a b))

/-- An off-cycle vertex with nonzero discrete ray index lies in the actual
bounded Jordan domain of the polygon carried by that same simple cycle. -/
theorem latticePolygonOfCycle_mem_domain_of_rayIndex_ne_zero {z : LatticeVertex}
    (p : PD.FK.squareLattice.Walk z z) (hp : p.IsCycle)
    (x : LatticeVertex) (hx : x ∉ p.support) (hindex : rayIndex x p ≠ 0) :
    FKC.latticeEmbed ⟨1,zero_lt_one⟩ x ∈ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective (show Function.Injective polygonRayLatticeHom from
        fun _ _ h => h)).mpr hp)).domain ⟨1,zero_lt_one⟩ := by
  let r := p.map polygonRayLatticeHom
  have hr : r.IsCycle := (p.isCycle_map_iff_of_injective
    (show Function.Injective polygonRayLatticeHom from fun _ _ h => h)).mpr hp
  let P := FKC.latticePolygonOfCycle hr
  have hmark : Push.faceIndexMark (x.1-1,x.2-1) = x := by
    simp only [Push.faceIndexMark, sub_add_cancel, Prod.eta]
  have hcenter := polygonRay_cellCenter_mem_domain_of_ne_zero p hp
    ⟨1,zero_lt_one⟩ (x.1-1,x.2-1) (by simpa only [hmark] using hindex)
  have hsub := (P.openLatticeCell_subset_domain_iff_center ⟨1,zero_lt_one⟩
    (x.1-1,x.2-1)).mpr hcenter
  have hclosure : FKC.latticeEmbed ⟨1,zero_lt_one⟩ x ∈
      closure (P.domain ⟨1,zero_lt_one⟩) :=
    closure_mono hsub (latticeVertex_mem_closure_southwest_cell x)
  rw [P.closure_domain] at hclosure
  rcases hclosure with h | h
  · exact h
  · obtain ⟨i, hi⟩ := (P.latticeEmbed_mem_carrier_iff ⟨1,zero_lt_one⟩ x).mp h
    apply (hx ?_).elim
    have hi' : p.getVert i.val = x := by
      change (p.map polygonRayLatticeHom).getVert i.val = x at hi
      rw [SimpleGraph.Walk.getVert_map] at hi
      exact hi
    rw [← hi']
    exact p.getVert_mem_support i.val

end
end PottsContinuity.RSW
