module

public import PottsContinuity.PlanarTopology.WalkIntersection
public import PottsContinuity.PD.Duality.PrimalDualSegments
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Order.CompletePartialOrder

/-! # Access from a primal edge midpoint to an unvisited endpoint -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Curves
noncomputable section

private theorem other_endpoint_not_mem_half_segment (x y : ℂ) (hne : x ≠ y) :
    y ∉ segment ℝ ((x+y)/2) x := by
  intro hy
  have hy' : y ∈ segment ℝ x ((x+y)/2) := by rwa [segment_symm] at hy
  have hb := norm_sub_le_of_mem_segment hy'
  have hm : (x+y)/2-x = (y-x)/2 := by ring
  rw [hm,norm_div] at hb
  norm_num at hb
  have hpos : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  linarith

/-- The half of an original lattice edge adjacent to an unvisited endpoint
misses the entire interpolated walk. Contacts at the other endpoint are
excluded by using the HALF edge, rather than the whole bond. -/
theorem primal_half_edge_segment_disjoint_walk (δ : PositiveMesh)
    {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (x y : LatticeVertex) (hxy : PD.squareLattice.Adj x y) (hx : x ∉ p.support) :
    Disjoint (Set.range (latticeWalkPath δ p))
      (segment ℝ ((latticeEmbed δ x+latticeEmbed δ y)/2) (latticeEmbed δ x)) := by
  have hne : latticeEmbed δ x ≠ latticeEmbed δ y := by
    intro he
    exact (PD.squareLattice.ne_of_adj hxy) (PlanarTopology.latticeEmbed_injective δ he)
  have hyhalf := other_endpoint_not_mem_half_segment (latticeEmbed δ x) (latticeEmbed δ y) hne
  have hsub : segment ℝ ((latticeEmbed δ x+latticeEmbed δ y)/2) (latticeEmbed δ x) ⊆
      segment ℝ (latticeEmbed δ x) (latticeEmbed δ y) := by
    apply (convex_segment _ _).segment_subset
    · have hm : (latticeEmbed δ x+latticeEmbed δ y)/2 =
          midpoint ℝ (latticeEmbed δ x) (latticeEmbed δ y) := by
        rw [midpoint_eq_smul_add]
        simp only [Complex.real_smul,invOf_eq_inv]
        push_cast
        ring
      rw [hm]
      exact midpoint_mem_segment _ _
    · exact left_mem_segment ℝ _ _
  apply Set.disjoint_left.mpr
  intro z hzP hzH
  obtain ⟨a,b,ha,hb,hab,hzAB⟩ := latticeWalkPath_range_subset_segments δ p hzP
  rw [Path.range_segment] at hzAB
  rcases hab with rfl | hab
  · have hzA : z = latticeEmbed δ a := by simpa only [segment_same,Set.mem_singleton_iff] using hzAB
    have haXY := (PlanarTopology.latticeEmbed_mem_segment_iff δ hxy).mp (hzA ▸ hsub hzH)
    rcases haXY with rfl | rfl
    · exact hx ha
    · exact hyhalf (hzA ▸ hzH)
  · by_cases he : s(a,b) = s(x,y)
    · rcases Sym2.eq_iff.mp he with ⟨rfl,_⟩ | ⟨_,rfl⟩
      · exact hx ha
      · exact hx hb
    · obtain ⟨hAB,hXY⟩ := PlanarTopology.mem_inter_lattice_segments_endpoints δ hab hxy he ⟨hzAB,hsub hzH⟩
      have hzX : z = latticeEmbed δ x := by
        rcases hXY with hX | hY
        · exact hX
        · exact (hyhalf (hY ▸ hzH)).elim
      rcases hAB with hA | hB
      · have hxa : x = a := PlanarTopology.latticeEmbed_injective δ (hzX.symm.trans hA)
        exact hx (hxa.symm ▸ ha)
      · have hxb : x = b := PlanarTopology.latticeEmbed_injective δ (hzX.symm.trans hB)
        exact hx (hxb.symm ▸ hb)


/-- The same half-edge avoidance statement for a normalized original bond,
using its actual midpoint and either of its two primal endpoints. -/
theorem primal_half_bond_segment_disjoint_walk (δ : PositiveMesh)
    {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (b : PD.FK.Medial.LatticeBond) (x : LatticeVertex)
    (hxb : x = b.source ∨ x = b.target) (hx : x ∉ p.support) :
    Disjoint (Set.range (latticeWalkPath δ p))
      (segment ℝ (b.midpoint δ) (latticeEmbed δ x)) := by
  rcases hxb with rfl | rfl
  · exact primal_half_edge_segment_disjoint_walk δ p b.source b.target b.adjacent hx
  · have hm : (latticeEmbed δ b.target+latticeEmbed δ b.source)/2 = b.midpoint δ := by
      dsimp only [PD.FK.Medial.LatticeBond.midpoint]
      rw [add_comm]
    simpa only [hm] using primal_half_edge_segment_disjoint_walk δ p b.target b.source b.adjacent.symm hx

end
end PottsContinuity.Thm3.Prop4
