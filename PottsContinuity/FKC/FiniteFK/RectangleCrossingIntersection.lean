-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleCrossingIntersection.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleConnectivity
public import PottsContinuity.FKC.Curves.RectanglePathIntersection
public import PottsContinuity.FKC.Curves.LatticeWalkInterpolation
public import PottsContinuity.FKC.Medial.PrimalDualSegments
public import PottsContinuity.FKC.Domains.LatticeEdges

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Curves
open PottsContinuity.FKC.Medial
open unitInterval

noncomputable section

def rectangleOpenGraphToSquare (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    openGraph (rectangleGraph a w h) A →g squareLattice where
  toFun := fun v => v.val
  map_rel' := fun huv =>
    (rectangleGraph_adj_iff a w h _ _).mp (openGraph_le (rectangleGraph a w h) A huv)

theorem rectangleOpenWalk_support_mapped_mem (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v)
    {x : LatticeVertex} (hx : x ∈ (p.map (rectangleOpenGraphToSquare a w h A)).support) :
    x ∈ latticeRectangle a w h := by
  rw [SimpleGraph.Walk.support_map] at hx
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact y.property

private theorem complex_segment_coordinate_bounds (a b : ℂ) {z : ℂ}
    {l r d u : ℝ}
    (hz : z ∈ segment ℝ a b)
    (hax : l ≤ a.re) (hbx : l ≤ b.re)
    (hxa : a.re ≤ r) (hxb : b.re ≤ r)
    (hay : d ≤ a.im) (hby : d ≤ b.im)
    (hya : a.im ≤ u) (hyb : b.im ≤ u) :
    l ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ u := by
  rw [segment_eq_image] at hz
  rcases hz with ⟨t, ht, rfl⟩
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im, add_zero]
  constructor
  · nlinarith [ht.1, ht.2]
  constructor
  · nlinarith [ht.1, ht.2]
  constructor
  · nlinarith [ht.1, ht.2]
  · nlinarith [ht.1, ht.2]

 def unitMesh : PositiveMesh := ⟨1, by norm_num⟩

theorem latticeWalkPath_coordinate_bounds {u v : LatticeVertex}
    (p : squareLattice.Walk u v) {l r d top : ℝ}
    (hpoints : ∀ x ∈ p.support,
      l ≤ (x.1 : ℝ) ∧ (x.1 : ℝ) ≤ r ∧
      d ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ top) :
    ∀ t : I,
      l ≤ (latticeWalkPath unitMesh p t).re ∧
      (latticeWalkPath unitMesh p t).re ≤ r ∧
      d ≤ (latticeWalkPath unitMesh p t).im ∧
      (latticeWalkPath unitMesh p t).im ≤ top := by
  intro t
  have hmem : latticeWalkPath unitMesh p t ∈ Set.range (latticeWalkPath unitMesh p) :=
    ⟨t, rfl⟩
  obtain ⟨x, y, hx, hy, _, hseg⟩ := latticeWalkPath_range_subset_segments unitMesh p hmem
  rw [Path.range_segment] at hseg
  have hx' := hpoints x hx
  have hy' := hpoints y hy
  have hcoords := complex_segment_coordinate_bounds
    (latticeEmbed unitMesh x) (latticeEmbed unitMesh y) hseg
    (by simpa [unitMesh] using hx'.1) (by simpa [unitMesh] using hy'.1)
    (by simpa [unitMesh] using hx'.2.1) (by simpa [unitMesh] using hy'.2.1)
    (by simpa [unitMesh] using hx'.2.2.1) (by simpa [unitMesh] using hy'.2.2.1)
    (by simpa [unitMesh] using hx'.2.2.2) (by simpa [unitMesh] using hy'.2.2.2)
  simpa [unitMesh] using hcoords

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

theorem rectangleOpenWalk_mapped_support_preimage (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v) {x : LatticeVertex}
    (hx : x ∈ (p.map (rectangleOpenGraphToSquare a w h A)).support) :
    ∃ z ∈ p.support, z.val = x := by
  rw [SimpleGraph.Walk.support_map] at hx
  rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
  exact ⟨z, hz, rfl⟩

end
end PottsContinuity.FKC.FiniteFK
