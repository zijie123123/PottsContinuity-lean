-- Support-intersection proofs adapted from FKconvergence, an earlier formalization by the same
-- author that is not publicly accessible (see `related_formalizations` in formalization.yaml):
-- file `FiniteFK/RectangleCrossingIntersection.lean`.
-- Reuses PD walk interpolation and the ported LatticeEdges geometry; no FKconvergence import.
module

public import PottsContinuity.PlanarTopology.LatticeEdges
public import PottsContinuity.PD.Duality.LatticeWalkInterpolation
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Curves unitInterval
noncomputable section

private theorem latticePoint_in_walkSegment_endpoint_support
    (δ : PositiveMesh) {u v : LatticeVertex}
    (p : squareLattice.Walk u v) {x y z : LatticeVertex}
    (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : x = y ∨ squareLattice.Adj x y)
    (hz : latticeEmbed δ z ∈ segment ℝ (latticeEmbed δ x) (latticeEmbed δ y)) :
    z ∈ p.support := by
  rcases hxy with hxy | hadj
  · subst y
    rw [segment_same] at hz
    have hzx : z = x := latticeEmbed_injective δ (Set.mem_singleton_iff.mp hz)
    simpa [hzx] using hx
  · rcases (latticeEmbed_mem_segment_iff δ hadj).mp hz with h | h
    · simpa [h] using hx
    · simpa [h] using hy

private theorem walkSegments_point_intersection_common_support
    (δ : PositiveMesh) {u v u' v' : LatticeVertex}
    (p : squareLattice.Walk u v) (q : squareLattice.Walk u' v')
    {x y x' y' : LatticeVertex} {z : ℂ}
    (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : x = y ∨ squareLattice.Adj x y)
    (hx' : x' ∈ q.support) (hy' : y' ∈ q.support)
    (hxy' : x' = y' ∨ squareLattice.Adj x' y')
    (hz : z ∈ segment ℝ (latticeEmbed δ x) (latticeEmbed δ y) ∩
      segment ℝ (latticeEmbed δ x') (latticeEmbed δ y')) :
    ∃ a, a ∈ p.support ∧ a ∈ q.support := by
  rcases hxy with hxy | hadj
  · subst y
    rw [segment_same] at hz
    have hzx : z = latticeEmbed δ x := Set.mem_singleton_iff.mp hz.1
    have hzq : latticeEmbed δ x ∈ segment ℝ (latticeEmbed δ x') (latticeEmbed δ y') := by
      rw [← hzx]
      exact hz.2
    exact ⟨x, hx, latticePoint_in_walkSegment_endpoint_support δ q hx' hy' hxy' hzq⟩
  · rcases hxy' with hxy' | hadj'
    · subst y'
      rw [segment_same] at hz
      have hzx : z = latticeEmbed δ x' := Set.mem_singleton_iff.mp hz.2
      have hzp : latticeEmbed δ x' ∈ segment ℝ (latticeEmbed δ x) (latticeEmbed δ y) := by
        rw [← hzx]
        exact hz.1
      exact ⟨x', latticePoint_in_walkSegment_endpoint_support δ p hx hy (Or.inr hadj) hzp,
        hx'⟩
    · by_cases hedge : s(x, y) = s(x', y')
      · rcases Sym2.eq_iff.mp hedge with ⟨hxx, hyy⟩ | ⟨hxy'', hyx⟩
        · exact ⟨x, hx, by simpa [hxx] using hx'⟩
        · exact ⟨x, hx, by simpa [hxy''] using hy'⟩
      · have hend := mem_inter_lattice_segments_endpoints δ hadj hadj' hedge hz
        rcases hend with ⟨hend, hend'⟩
        rcases hend with hzX | hzY
        · rcases hend' with hzX' | hzY'
          · refine ⟨x, hx, ?_⟩
            have heq : x = x' := latticeEmbed_injective δ (hzX.symm.trans hzX')
            simpa [heq] using hx'
          · refine ⟨x, hx, ?_⟩
            have heq : x = y' := latticeEmbed_injective δ (hzX.symm.trans hzY')
            simpa [heq] using hy'
        · rcases hend' with hzX' | hzY'
          · refine ⟨y, hy, ?_⟩
            have heq : y = x' := latticeEmbed_injective δ (hzY.symm.trans hzX')
            simpa [heq] using hx'
          · refine ⟨y, hy, ?_⟩
            have heq : y = y' := latticeEmbed_injective δ (hzY.symm.trans hzY')
            simpa [heq] using hy'

theorem latticeWalkPaths_intersection_common_support
    (δ : PositiveMesh) {u v u' v' : LatticeVertex}
    (p : squareLattice.Walk u v) (q : squareLattice.Walk u' v')
    {s t : I} (hst : latticeWalkPath δ p s = latticeWalkPath δ q t) :
    ∃ x, x ∈ p.support ∧ x ∈ q.support := by
  let z := latticeWalkPath δ p s
  have hzp : z ∈ Set.range (latticeWalkPath δ p) := ⟨s, rfl⟩
  have hzq : z ∈ Set.range (latticeWalkPath δ q) := by
    refine ⟨t, ?_⟩
    dsimp [z]
    exact hst.symm
  obtain ⟨x, y, hx, hy, hxy, hseg⟩ :=
    latticeWalkPath_range_subset_segments δ p hzp
  obtain ⟨x', y', hx', hy', hxy', hseg'⟩ :=
    latticeWalkPath_range_subset_segments δ q hzq
  rw [Path.range_segment] at hseg hseg'
  exact walkSegments_point_intersection_common_support δ p q hx hy hxy hx' hy' hxy'
    ⟨hseg, hseg'⟩

end
end PottsContinuity.PlanarTopology
