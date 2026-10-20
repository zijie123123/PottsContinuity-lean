module

public import PottsContinuity.Thm3.RSW.PolygonRayCell
public import PottsContinuity.Thm3.RSW.PolygonRayExterior
public import PottsContinuity.Thm3.RSW.PolygonRayLocation
public import PottsContinuity.Thm3.RSW.PolygonBoxBounds
public import PottsContinuity.PD.Duality.RayIndexSeparation
public import PottsContinuity.PD.RCInfinite.BoxConnector
public import PottsContinuity.DualityExt.PositiveAnnulusDualShell
public import PottsContinuity.DualityExt.PositiveP5aAnnulusActualDualJordan
public import PottsContinuity.FKC.Domains.LatticePolygonCellConnectivity
public import PottsContinuity.FKC.Domains.LatticePolygonInteriorNeighbor

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.Duality
open PottsContinuity.FKC
open PottsContinuity.RSW
open Filter

noncomputable section

private theorem polygonRay_interiorCell_adjacent_index
    {z : PD.FK.LatticeVertex} (p : PD.FK.squareLattice.Walk z z) (hp : p.IsCycle)
    (δ : FKC.PositiveMesh) {u v : FKC.LatticeVertex}
    (hadj : FKC.squareLattice.Adj u v)
    (hu : u ∈ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective
        (show Function.Injective polygonRayLatticeHom from fun _ _ h => h)).mpr hp)).interiorCellBases δ)
    (hv : v ∈ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective
        (show Function.Injective polygonRayLatticeHom from fun _ _ h => h)).mpr hp)).interiorCellBases δ) :
    rayIndex (Push.faceIndexMark u) p = rayIndex (Push.faceIndexMark v) p := by
  obtain ⟨d, hd⟩ := FKC.Medial.LatticeBond.exists_of_adj hadj
  let b := FKC.Medial.primalBondOfDual d
  have hs : b.faceBase false = d.source := by
    rw [← FKC.Medial.dualBondOfPrimal_source,
      FKC.Medial.dualBondOfPrimal_primalBondOfDual]
  have ht : b.faceBase true = d.target := by
    rw [← FKC.Medial.dualBondOfPrimal_target,
      FKC.Medial.dualBondOfPrimal_primalBondOfDual]
  have hnot : b.toSym2 ∉ p.edges := by
    intro hb
    have hdiff := (polygonRay_bond_mem_iff_cell_difference p hp b δ).mp hb
    rw [hs, ht] at hdiff
    have heq : s(d.source, d.target) = s(u, v) := by
      simpa [FKC.Medial.LatticeBond.toSym2] using hd
    rcases Sym2.eq_iff.mp heq with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
    · subst u
      subst v
      exact hdiff (propext ⟨fun _ => hu, fun _ => hv⟩)
    · subst u
      subst v
      exact hdiff (propext ⟨fun _ => hv, fun _ => hu⟩)
  let dPD : PD.FK.Medial.LatticeBond :=
    ⟨d.base, match d.axis with
      | FKC.Medial.LatticeAxis.horizontal => PD.FK.Medial.LatticeAxis.horizontal
      | FKC.Medial.LatticeAxis.vertical => PD.FK.Medial.LatticeAxis.vertical⟩
  let bPD := PD.FK.Medial.primalBondOfDual dPD
  have hbFaceFalse : bPD.faceBase false = b.faceBase false := by
    cases d with
    | mk base axis => cases axis <;> rfl
  have hbFaceTrue : bPD.faceBase true = b.faceBase true := by
    cases d with
    | mk base axis => cases axis <;> rfl
  have hbEdge : bPD.toSym2 = b.toSym2 := by
    cases d with
    | mk base axis => cases axis <;> rfl
  have hnotPD : bPD.toSym2 ∉ p.edges := by
    simpa [hbEdge] using hnot
  have hindex := Push.rayIndex_bond_faces_eq_of_not_mem p bPD hnotPD
  rw [hbFaceFalse, hbFaceTrue] at hindex
  rw [hs, ht] at hindex
  have heq : s(d.source, d.target) = s(u, v) := by
    simpa [FKC.Medial.LatticeBond.toSym2] using hd
  rcases Sym2.eq_iff.mp heq with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
  · simpa [h₁, h₂] using hindex
  · simpa [h₁, h₂] using hindex.symm

/-- Every lattice vertex in the bounded Jordan domain of a simple lattice
cycle has nonzero horizontal-ray index. -/
theorem polygonRay_domain_vertex_index_ne_zero
    {z : PD.FK.LatticeVertex} (p : PD.FK.squareLattice.Walk z z) (hp : p.IsCycle)
    (x : PD.FK.LatticeVertex)
    (hx : FKC.latticeEmbed ⟨1, by norm_num⟩ x ∈ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective
        (show Function.Injective polygonRayLatticeHom from fun _ _ h => h)).mpr hp)).domain
      ⟨1, by norm_num⟩) :
    rayIndex x p ≠ 0 := by
  classical
  let δ : FKC.PositiveMesh := ⟨1, by norm_num⟩
  let r := p.map polygonRayLatticeHom
  have hr : r.IsCycle := (p.isCycle_map_iff_of_injective
    (show Function.Injective polygonRayLatticeHom from fun _ _ h => h)).mpr hp
  let P := FKC.latticePolygonOfCycle hr
  let S := P.interiorCellBases δ
  have hvertexDomain : FKC.latticeEmbed δ x ∈ P.domain δ := by
    simpa only [P, δ] using hx
  let cₓ : FKC.LatticeVertex := (x.1 - 1, x.2 - 1)
  have hcellCenter : latticeCellCenter δ cₓ ∈ P.domain δ := by
    have hclosure := latticeVertex_mem_closure_southwest_cell x
    have hneighborhood : P.domain δ ∈ nhds (FKC.latticeEmbed δ x) :=
      (P.isJordanDomain δ).isOpen.mem_nhds hvertexDomain
    have hintersection : (P.domain δ ∩ openLatticeCell δ cₓ).Nonempty := by
      have hclosure' := (mem_closure_iff_nhds.mp hclosure) (P.domain δ) hneighborhood
      rcases hclosure' with ⟨y, hy⟩
      exact ⟨y, hy.1, hy.2⟩
    rcases P.openLatticeCell_subset_domain_or_exterior δ cₓ with hD | hE
    · exact hD (latticeCellCenter_mem δ cₓ)
    · rcases hintersection with ⟨y, hyD, hyCell⟩
      exact (Set.disjoint_left.mp (P.disjoint_domain_exterior δ) hyD (hE hyCell)).elim
  have hcₓ : cₓ ∈ S := (P.mem_interiorCellBases_iff δ cₓ).mpr hcellCenter
  have hboundary : ∃ b : FKC.Medial.LatticeBond, b.toSym2 ∈ p.edges := by
    obtain ⟨b, hb⟩ := FKC.Medial.LatticeBond.exists_of_adj (P.adjacent 0)
    refine ⟨b, ?_⟩
    have hbR : b.toSym2 ∈ r.edges :=
      (FKC.latticePolygonOfCycle_edge_iff hr b.toSym2).mpr ⟨0, ?_⟩
    · have hedge : r.edges = p.edges := by
        rw [SimpleGraph.Walk.edges_map]
        change List.map (Sym2.map id) p.edges = p.edges
        simp only [Sym2.map_id, List.map_id]
      simpa [hedge] using hbR
    · let i : ZMod (r.length - 3 + 3) := 0
      have hfirst : P.vertex i = r.getVert 0 := rfl
      have hnext : P.vertex (i + 1) = r.getVert 1 := by
        rw [FKC.latticePolygonOfCycle_vertex_succ hr i]
        rfl
      rw [hfirst, hnext]
      exact hb
  obtain ⟨b, hb⟩ := hboundary
  have hdiff : (b.faceBase true ∈ S) ≠ (b.faceBase false ∈ S) :=
    (polygonRay_bond_mem_iff_cell_difference p hp b δ).mp hb
  let bPD : PD.FK.Medial.LatticeBond :=
    ⟨b.base, match b.axis with
      | FKC.Medial.LatticeAxis.horizontal => PD.FK.Medial.LatticeAxis.horizontal
      | FKC.Medial.LatticeAxis.vertical => PD.FK.Medial.LatticeAxis.vertical⟩
  have hbFaceFalse : bPD.faceBase false = b.faceBase false := by
    cases b with
    | mk base axis => cases axis <;> rfl
  have hbFaceTrue : bPD.faceBase true = b.faceBase true := by
    cases b with
    | mk base axis => cases axis <;> rfl
  have hbEdge : bPD.toSym2 = b.toSym2 := by
    cases b with
    | mk base axis => cases axis <;> rfl
  have hbPD : bPD.toSym2 ∈ p.edges := by
    simpa [hbEdge] using hb
  have hfaceIndexNe := Push.rayIndex_bond_faces_ne_of_mem p hp.edges_nodup bPD hbPD
  have hbaseIndex : ∃ c : FKC.LatticeVertex, c ∈ S ∧ rayIndex (Push.faceIndexMark c) p ≠ 0 := by
    by_cases hfalse : b.faceBase false ∈ S
    · have htrue : b.faceBase true ∉ S := by
        intro htrue
        exact hdiff (propext ⟨fun _ => hfalse, fun _ => htrue⟩)
      have hzero := polygonRay_exterior_cell_zero p hp δ (b.faceBase true) htrue
      refine ⟨b.faceBase false, hfalse, ?_⟩
      intro hz
      have hz' : rayIndex (Push.faceIndexMark (bPD.faceBase false)) p = 0 := by
        simpa [hbFaceFalse] using hz
      have hzero' : rayIndex (Push.faceIndexMark (bPD.faceBase true)) p = 0 := by
        simpa [hbFaceTrue] using hzero
      exact hfaceIndexNe (hz'.trans hzero'.symm)
    · have htrue : b.faceBase true ∈ S := by
        by_contra htrue
        exact hdiff (propext ⟨fun ht => (htrue ht).elim, fun hf => (hfalse hf).elim⟩)
      have hzero := polygonRay_exterior_cell_zero p hp δ (b.faceBase false) hfalse
      refine ⟨b.faceBase true, htrue, ?_⟩
      intro hz
      have hz' : rayIndex (Push.faceIndexMark (bPD.faceBase true)) p = 0 := by
        simpa [hbFaceTrue] using hz
      have hzero' : rayIndex (Push.faceIndexMark (bPD.faceBase false)) p = 0 := by
        simpa [hbFaceFalse] using hzero
      exact hfaceIndexNe (hzero'.trans hz'.symm)
  obtain ⟨c, hc, hcnz⟩ := hbaseIndex
  let G := FKC.squareLattice.induce (↑S : Set FKC.LatticeVertex)
  have hconn : G.Connected :=
    FKC.LatticePolygon.interiorCellBases_connected_of_cycle hr δ
  obtain ⟨w⟩ := hconn.preconnected ⟨cₓ, hcₓ⟩ ⟨c, hc⟩
  have hconstant : ∀ {a b : {v : FKC.LatticeVertex // v ∈ S}}, (G.Walk a b) →
      rayIndex (Push.faceIndexMark a.val) p = rayIndex (Push.faceIndexMark b.val) p := by
    intro a b q
    induction q with
    | nil => rfl
    | @cons a b t hadj q ih =>
      exact (polygonRay_interiorCell_adjacent_index p hp δ hadj a.property b.property).trans ih
  have hxIndex : rayIndex (Push.faceIndexMark cₓ) p ≠ 0 := by
    intro hz
    exact hcnz ((hconstant w).symm.trans hz)
  have hmark : Push.faceIndexMark cₓ = x := by
    simp [cₓ, Push.faceIndexMark]
  simpa only [hmark] using hxIndex

/-- The Jordan domain of a polygon in the outer face box misses every vertex
of the primal outer annulus boundary. -/
theorem polygon_domain_avoids_outerBoundary_of_faceBox
    {m : ℕ} (P : FKC.LatticePolygon m) (N : ℕ)
    (hvertices : ∀ i : ZMod (m + 3),
      P.vertex i ∈ dualFaceBox (2 * N))
    (x : PD.FK.LatticeVertex) (hx : x ∈ annulusOuterBoundary (2 * N)) :
    FKC.latticeEmbed ⟨1, by norm_num⟩ x ∉ P.domain ⟨1, by norm_num⟩ := by
  let δ : FKC.PositiveMesh := ⟨1, by norm_num⟩
  have hx' := (Finset.mem_filter.mp hx).2
  have hcoords (i : ZMod (m + 3)) :=
    (mem_dualFaceBox (2 * N) (P.vertex i)).mp (hvertices i)
  have hright : ∀ i, (P.vertex i).1 ≤ 2 * (N : ℤ) - 1 := by
    intro i
    exact (hcoords i).2.1
  have hleft : ∀ i, -(2 * (N : ℤ)) ≤ (P.vertex i).1 := by
    intro i
    exact (hcoords i).1
  have htop : ∀ i, (P.vertex i).2 ≤ 2 * (N : ℤ) - 1 := by
    intro i
    exact (hcoords i).2.2.2
  have hbottom : ∀ i, -(2 * (N : ℤ)) ≤ (P.vertex i).2 := by
    intro i
    exact (hcoords i).2.2.1
  rcases hx' with hxright | hxleft | hxtop | hxbottom
  · intro hdomain
    have hbound := RSW.latticePolygon_domain_coordinate_lt P δ Complex.reLm
      Complex.continuous_re Complex.isOpenMap_re
      ((2 * (N : ℤ) - 1 : ℤ) : ℝ) (by
        intro i
        change (FKC.latticeEmbed δ (P.vertex i)).re ≤ _
        rw [FKC.latticeEmbed_re]
        norm_num [δ]
        exact_mod_cast hright i) (FKC.latticeEmbed δ x) hdomain
    change (FKC.latticeEmbed δ x).re < _ at hbound
    have hxcoord : (FKC.latticeEmbed δ x).re =
        ((2 * (N : ℤ) : ℤ) : ℝ) := by
      rw [FKC.latticeEmbed_re]
      simp [δ, hxright]
    rw [hxcoord] at hbound
    push_cast at hbound
    linarith
  · intro hdomain
    have hbound := RSW.latticePolygon_domain_coordinate_lt P δ (-Complex.reLm)
      Complex.continuous_re.neg
      ((Homeomorph.neg ℝ).isOpenMap.comp Complex.isOpenMap_re)
      ((2 * (N : ℤ) : ℤ) : ℝ) (by
        intro i
        change -(FKC.latticeEmbed δ (P.vertex i)).re ≤ _
        rw [FKC.latticeEmbed_re]
        norm_num [δ]
        have hi := hleft i
        exact_mod_cast (by omega : -((P.vertex i).1 : ℤ) ≤ 2 * (N : ℤ)))
      (FKC.latticeEmbed δ x) hdomain
    change -(FKC.latticeEmbed δ x).re < _ at hbound
    have hxcoord : (FKC.latticeEmbed δ x).re =
        ((-(2 * (N : ℤ)) : ℤ) : ℝ) := by
      rw [FKC.latticeEmbed_re]
      simp [δ, hxleft]
    rw [hxcoord] at hbound
    push_cast at hbound
    linarith
  · intro hdomain
    have hbound := RSW.latticePolygon_domain_coordinate_lt P δ Complex.imLm
      Complex.continuous_im Complex.isOpenMap_im
      ((2 * (N : ℤ) - 1 : ℤ) : ℝ) (by
        intro i
        change (FKC.latticeEmbed δ (P.vertex i)).im ≤ _
        rw [FKC.latticeEmbed_im]
        norm_num [δ]
        exact_mod_cast htop i) (FKC.latticeEmbed δ x) hdomain
    change (FKC.latticeEmbed δ x).im < _ at hbound
    have hxcoord : (FKC.latticeEmbed δ x).im =
        ((2 * (N : ℤ) : ℤ) : ℝ) := by
      rw [FKC.latticeEmbed_im]
      simp [δ, hxtop]
    rw [hxcoord] at hbound
    push_cast at hbound
    linarith
  · intro hdomain
    have hbound := RSW.latticePolygon_domain_coordinate_lt P δ (-Complex.imLm)
      Complex.continuous_im.neg
      ((Homeomorph.neg ℝ).isOpenMap.comp Complex.isOpenMap_im)
      ((2 * (N : ℤ) : ℤ) : ℝ) (by
        intro i
        change -(FKC.latticeEmbed δ (P.vertex i)).im ≤ _
        rw [FKC.latticeEmbed_im]
        norm_num [δ]
        have hi := hbottom i
        exact_mod_cast (by omega : -((P.vertex i).2 : ℤ) ≤ 2 * (N : ℤ)))
      (FKC.latticeEmbed δ x) hdomain
    change -(FKC.latticeEmbed δ x).im < _ at hbound
    have hxcoord : (FKC.latticeEmbed δ x).im =
        ((-(2 * (N : ℤ)) : ℤ) : ℝ) := by
      rw [FKC.latticeEmbed_im]
      simp [δ, hxbottom]
    rw [hxcoord] at hbound
    push_cast at hbound
    linarith

end
end PottsContinuity.DualityExt
