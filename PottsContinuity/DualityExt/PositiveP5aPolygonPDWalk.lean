module

public import PottsContinuity.DualityExt.PositivePolygonCycleDomain
public import PottsContinuity.DualityExt.PositivePolygonRayIndex
public import PottsContinuity.DualityExt.PositiveP5aAnnulusInnerClass
public import PottsContinuity.DualityExt.PositiveP5aRayIndexBarrier
public import PottsContinuity.DualityExt.PositiveDualSubgraphEdgeState

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality
open PottsContinuity.FKC
open PottsContinuity.RSW
open SimpleGraph

noncomputable section

noncomputable def p5aPolygonToPD :
    FKC.squareLattice →g PD.FK.squareLattice where
  toFun := id
  map_rel' := fun h => (PD.FK.squareLattice_adj_iff _ _).mpr
    ((FKC.squareLattice_adj_iff _ _).mp h)

 noncomputable def p5aForwardPolygonCycle {m : ℕ}
    (P : FKC.LatticePolygon m) :=
  (polygonCycle P).reverse

private theorem p5aForwardPolygonCycle_isCycle {m : ℕ}
    (P : FKC.LatticePolygon m) : (p5aForwardPolygonCycle P).IsCycle :=
  (polygonCycle_isCycle P).reverse

noncomputable def p5aPolygonCyclePD {m : ℕ}
    (P : FKC.LatticePolygon m) :=
  (p5aForwardPolygonCycle P).map p5aPolygonToPD

private theorem p5aPolygonCyclePD_isCycle {m : ℕ}
    (P : FKC.LatticePolygon m) : (p5aPolygonCyclePD P).IsCycle := by
  exact (Walk.isCycle_map_iff_of_injective
    (show Function.Injective p5aPolygonToPD.toFun from fun _ _ h => h)).2
      (p5aForwardPolygonCycle_isCycle P)

private theorem p5aPolygonCyclePD_map_isCycle {m : ℕ}
    (P : FKC.LatticePolygon m) :
    ((p5aPolygonCyclePD P).map polygonRayLatticeHom).IsCycle := by
  exact (Walk.isCycle_map_iff_of_injective
    (show Function.Injective polygonRayLatticeHom from fun _ _ h => h)).2
      (p5aPolygonCyclePD_isCycle P)

private theorem p5aPolygonCyclePD_back {m : ℕ} (P : FKC.LatticePolygon m) :
    (p5aPolygonCyclePD P).map polygonRayLatticeHom = p5aForwardPolygonCycle P := by
  rw [p5aPolygonCyclePD, Walk.map_map]
  change Walk.map Hom.id (p5aForwardPolygonCycle P) = _
  exact Walk.map_id _

private theorem p5aCycleDomain_eq_of_walk_eq {z : FKC.LatticeVertex}
    {p q : FKC.squareLattice.Walk z z} (hp : p.IsCycle) (hq : q.IsCycle)
    (h : p = q) :
    (latticePolygonOfCycle hp).domain ⟨1, by norm_num⟩ =
      (latticePolygonOfCycle hq).domain ⟨1, by norm_num⟩ := by
  cases h
  rfl

private theorem p5aPolygonCyclePD_domain {m : ℕ} (P : FKC.LatticePolygon m) :
    (latticePolygonOfCycle (p5aPolygonCyclePD_map_isCycle P)).domain ⟨1, by norm_num⟩ =
      P.domain ⟨1, by norm_num⟩ := by
  let p := p5aPolygonCyclePD P
  let hback : p.map polygonRayLatticeHom = p5aForwardPolygonCycle P :=
    p5aPolygonCyclePD_back P
  let hpFKC : (p.map polygonRayLatticeHom).IsCycle := p5aPolygonCyclePD_map_isCycle P
  let hpSource : (p5aForwardPolygonCycle P).IsCycle := p5aForwardPolygonCycle_isCycle P
  have hdom := p5aCycleDomain_eq_of_walk_eq hpFKC hpSource hback
  have hdom' : (latticePolygonOfCycle hpSource).domain ⟨1, by norm_num⟩ =
      P.domain ⟨1, by norm_num⟩ := by
    exact positive_polygonCycle_domain_eq P
  change (latticePolygonOfCycle hpFKC).domain ⟨1, by norm_num⟩ = P.domain ⟨1, by norm_num⟩
  calc
    (latticePolygonOfCycle hpFKC).domain ⟨1, by norm_num⟩ =
        (latticePolygonOfCycle hpSource).domain ⟨1, by norm_num⟩ := hdom
    _ = P.domain ⟨1, by norm_num⟩ := hdom'

private theorem p5aForwardPolygonCycle_support_vertices {m : ℕ}
    (P : FKC.LatticePolygon m) {x : FKC.LatticeVertex}
    (hx : x ∈ (p5aForwardPolygonCycle P).support) :
    ∃ i : ZMod (m + 3), P.vertex i = x := by
  have hwalkSupport : (polygonCyclicWalk P).support = polygonCyclicList P := by
    simp only [polygonCyclicWalk, Walk.support_ofSupport]
  have hhead : (polygonCyclicList P).head (by simp [polygonCyclicList]) = P.vertex 0 := by
    simp [polygonCyclicList]
  have hx' : x ∈ polygonCyclicList P ∨ x = P.vertex 0 := by
    have h := hx
    simp only [p5aForwardPolygonCycle, Walk.support_reverse, polygonCycle,
      Walk.support_cons, Walk.support_reverse, List.reverse_cons,
      List.reverse_reverse] at h
    rw [hwalkSupport, hhead] at h
    simpa only [List.mem_append, List.mem_singleton] using h
  rcases hx' with hxList | hxZero
  · rcases List.mem_ofFn.mp hxList with ⟨i, hi⟩
    exact ⟨(i.val : ZMod (m + 3)), hi⟩
  · exact ⟨0, hxZero.symm⟩

private theorem p5aPolygonCyclePD_support_vertices {m : ℕ}
    (P : FKC.LatticePolygon m) {x : PD.FK.LatticeVertex}
    (hx : x ∈ (p5aPolygonCyclePD P).support) :
    ∃ i : ZMod (m + 3), P.vertex i = x := by
  have hx' : x ∈ (p5aForwardPolygonCycle P).support := by
    simpa [p5aPolygonCyclePD, p5aPolygonToPD] using hx
  exact p5aForwardPolygonCycle_support_vertices P hx'

private theorem p5aAnnulusVertexSet_ne_outerBoundary {N : ℕ}
    (hN : 2 ≤ N) (y x : PD.FK.LatticeVertex)
    (hy : y ∈ PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
    (hx : x ∈ annulusOuterBoundary (2 * N)) : y ≠ x := by
  have hsmall := (PottsContinuity.Foundations.mem_box_iff_interval
    (2 * (N - 1)) y).mp (Finset.mem_sdiff.mp hy).1
  have hx' := hx
  unfold annulusOuterBoundary at hx'
  rcases Finset.mem_filter.mp hx' with ⟨_, hside⟩
  rcases hside with hright | hleft | htop | hbottom
  · intro hxy
    rw [hxy] at hsmall
    have hycoord := hsmall.1.2
    omega
  · intro hxy
    rw [hxy] at hsmall
    have hycoord := hsmall.1.1
    omega
  · intro hxy
    rw [hxy] at hsmall
    have hycoord := hsmall.2.2
    omega
  · intro hxy
    rw [hxy] at hsmall
    have hycoord := hsmall.2.1
    omega

private theorem p5aPolygonPDWalk_outerBoundary_not_mem_support {m : ℕ}
    {N : ℕ} (hN : 2 ≤ N) (P : FKC.LatticePolygon m)
    (hvertices : ∀ i : ZMod (m + 3),
      P.vertex i ∈ PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
    (x : PD.FK.LatticeVertex) (hx : x ∈ annulusOuterBoundary (2 * N)) :
    x ∉ (p5aPolygonCyclePD P).support := by
  intro hxSupport
  obtain ⟨i, hi⟩ := p5aPolygonCyclePD_support_vertices P hxSupport
  exact (p5aAnnulusVertexSet_ne_outerBoundary hN (P.vertex i) x
    (hvertices i) hx) hi

theorem p5aPolygonPDWalk_outerBoundary_rayIndex_zero {m : ℕ}
    {N : ℕ} (hN : 2 ≤ N) (P : FKC.LatticePolygon m)
    (hvertices : ∀ i : ZMod (m + 3),
      P.vertex i ∈ PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
    (x : PD.FK.LatticeVertex) (hx : x ∈ annulusOuterBoundary (2 * N))
    (hnotDomain : FKC.latticeEmbed ⟨1, by norm_num⟩ x ∉
      P.domain ⟨1, by norm_num⟩) :
    rayIndex x (p5aPolygonCyclePD P) = 0 := by
  by_contra hzero
  have hdomain := latticePolygonOfCycle_mem_domain_of_rayIndex_ne_zero
    (p5aPolygonCyclePD P) (p5aPolygonCyclePD_isCycle P) x
    (p5aPolygonPDWalk_outerBoundary_not_mem_support hN P hvertices x hx) hzero
  rw [p5aPolygonCyclePD_domain P] at hdomain
  exact hnotDomain hdomain

/-- A polygon containing the origin yields a PD cycle with nonzero ray index
at the origin. -/
theorem p5aPolygon_origin_rayIndex_ne_zero {m : ℕ}
    (P : FKC.LatticePolygon m)
    (horigin : FKC.latticeEmbed ⟨1, by norm_num⟩ (0, 0) ∈
      P.domain ⟨1, by norm_num⟩) :
    rayIndex (0, 0) (p5aPolygonCyclePD P) ≠ 0 := by
  let p := p5aPolygonCyclePD P
  let hp := p5aPolygonCyclePD_isCycle P
  have hdom := p5aPolygonCyclePD_domain P
  have hpFKC : (p.map polygonRayLatticeHom).IsCycle := p5aPolygonCyclePD_map_isCycle P
  have horigin' : FKC.latticeEmbed ⟨1, by norm_num⟩ (0, 0) ∈
      (latticePolygonOfCycle hpFKC).domain ⟨1, by norm_num⟩ := by
    rw [hdom]
    exact horigin
  exact polygonRay_domain_vertex_index_ne_zero p hp (0, 0) horigin'

/-- Any lattice point in the polygon domain has nonzero index for its
represented PD cycle. -/
theorem p5aPolygon_rayIndex_ne_zero_of_mem_domain {m : ℕ}
    (P : FKC.LatticePolygon m) (x : PD.FK.LatticeVertex)
    (hx : FKC.latticeEmbed ⟨1, by norm_num⟩ x ∈
      P.domain ⟨1, by norm_num⟩) :
    rayIndex x (p5aPolygonCyclePD P) ≠ 0 := by
  let p := p5aPolygonCyclePD P
  let hp := p5aPolygonCyclePD_isCycle P
  have hdom := p5aPolygonCyclePD_domain P
  have hpFKC : (p.map polygonRayLatticeHom).IsCycle :=
    p5aPolygonCyclePD_map_isCycle P
  have hx' : FKC.latticeEmbed ⟨1, by norm_num⟩ x ∈
      (latticePolygonOfCycle hpFKC).domain ⟨1, by norm_num⟩ := by
    rw [hdom]
    exact hx
  exact polygonRay_domain_vertex_index_ne_zero p hp x hx'

end

end PottsContinuity.DualityExt
