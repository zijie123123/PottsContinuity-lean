module

public import PottsContinuity.Thm3.OuterCircuit.CandidateEnvelope
public import PottsContinuity.Thm3.OuterCircuit.CyclePolygonRecovery
public import PottsContinuity.Thm3.OuterCircuit.SourcePolygonCode
public import PottsContinuity.Thm3.RSW.PolygonRayLocation
public import PottsContinuity.FKC.Domains.LatticePolygonOfCycle
public import PottsContinuity.FKC.Medial.LatticePorts

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality
open PottsContinuity.FKC
open PottsContinuity.RSW
open PottsContinuity.Exploration
open PottsContinuity.FKC.Medial

noncomputable section

local instance outerCircuitHostRegionDecidableEq {n : ℕ} :
    DecidableEq (OuterCircuitHostVertex n) :=
  PottsContinuity.Exploration.envelopeMaxIndexDecidableEq

theorem outerCircuitCandidateValid_shape {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) (i : OuterCircuitPolygonCode n)
    (hvalid : outerCircuitCandidateValid C i) :
    outerCircuitCandidateShape i := by
  exact ⟨hvalid.1, hvalid.2.1⟩

/-- Two valid polygon codes have a bounded source polygon representing an
envelope of their finite cell interiors. -/
theorem outerCircuitEnvelopeCode_exists {n : ℕ}
    (i j : OuterCircuitPolygonCode n)
    (hi : outerCircuitCandidateShape i)
    (hj : outerCircuitCandidateShape j) :
    ∃ k : OuterCircuitPolygonCode n,
      outerCircuitCandidateShape k ∧
      outerCircuitCandidateInside i ∪ outerCircuitCandidateInside j ⊆
        outerCircuitCandidateInside k ∧
      outerCircuitCandidateSupport k ⊆
        outerCircuitCandidateSupport i ∪ outerCircuitCandidateSupport j := by
  let P := outerCircuitCodePolygon i
  let Q := outerCircuitCodePolygon j
  have hradP : ∀ t : ZMod (i.1.val + 3), outerCircuitShellVertex n (P.vertex t) :=
    fun t => hi.2 t
  have hradQ : ∀ t : ZMod (j.1.val + 3), outerCircuitShellVertex n (Q.vertex t) :=
    fun t => hj.2 t
  obtain ⟨z, c, hc, hfill, hrayP, _, hEdges⟩ :=
    outerCircuitShapedCandidates_have_envelope i j hi hj
  let R := outerCircuitEnvelopePolygon c hc
  have hradR : ∀ t : ZMod ((c.map RSW.polygonRayLatticeHom).length - 3 + 3),
      outerCircuitShellVertex n (R.vertex t) :=
    outerCircuitEnvelopePolygon_vertex_shell P Q hradP hradQ c hc hEdges
  have hvertices : ∀ t : ZMod ((c.map RSW.polygonRayLatticeHom).length - 3 + 3),
      R.vertex t ∈ PottsContinuity.PD.box (56*n) :=
    outerCircuitPolygon_vertex_mem_host_of_radius R (fun t => (hradR t).2)
  let k := outerCircuitPolygonCodeOfHostPolygon R hvertices
  have hcode : outerCircuitCodePolygon k = R :=
    outerCircuitCodePolygon_of_hostPolygon_eq R hvertices
  have hindex : rayIndex (0, 0) c ≠ 0 := by
    apply hrayP (0, 0)
    change rayIndex (PottsContinuity.Push.faceIndexMark (-1, -1))
        (sourcePolygonWalk P) ≠ 0
    exact outerCircuitCandidateShape_origin_rayIndex_ne_zero i hi
  have hzero_not_support : (0, 0) ∉ c.support := by
    intro hzero
    have hrad0 := outerCircuitEnvelopeWalk_vertex_shell P Q hradP hradQ c hc hEdges hzero
    have hpositive : (7*n : ℤ) < 0 := by
      simpa [outerCircuitShellVertex] using hrad0.1
    omega
  have horiginR : FKC.latticeEmbed ⟨1, zero_lt_one⟩ (0, 0) ∈ R.domain ⟨1, zero_lt_one⟩ := by
    exact latticePolygonOfCycle_mem_domain_of_rayIndex_ne_zero c hc
      (0, 0) hzero_not_support hindex
  have hshape : outerCircuitCandidateShape k := by
    refine ⟨?_, ?_⟩
    · rw [hcode]
      exact horiginR
    · intro t
      rw [hcode]
      exact hradR t
  have hfillCandidate := hfill
  rw [outerCircuitCodePolygon_envelopePolygon_region_eq i,
    outerCircuitCodePolygon_envelopePolygon_region_eq j] at hfillCandidate
  change P.interiorCellBases ⟨1, zero_lt_one⟩ ∪
      Q.interiorCellBases ⟨1, zero_lt_one⟩ ⊆ R.interiorCellBases ⟨1, zero_lt_one⟩ at hfillCandidate
  have hfill' := hfillCandidate
  refine ⟨k, hshape, ?_, ?_⟩
  · intro x hx
    have hxsource : x.val ∈ P.interiorCellBases ⟨1, zero_lt_one⟩ ∪
        Q.interiorCellBases ⟨1, zero_lt_one⟩ := by
      rcases Finset.mem_union.mp hx with hx | hx
      · have hx' : x.val ∈ (outerCircuitCodePolygon i).interiorCellBases ⟨1, zero_lt_one⟩ := by
          simpa [outerCircuitCandidateInside] using hx
        exact Finset.mem_union.mpr (Or.inl (by simpa [P] using hx'))
      · have hx' : x.val ∈ (outerCircuitCodePolygon j).interiorCellBases ⟨1, zero_lt_one⟩ := by
          simpa [outerCircuitCandidateInside] using hx
        exact Finset.mem_union.mpr (Or.inr (by simpa [Q] using hx'))
    have hxR := hfill' hxsource
    have hxK : x.val ∈ (outerCircuitCodePolygon k).interiorCellBases ⟨1, zero_lt_one⟩ := by
      rw [hcode]
      exact hxR
    simpa [outerCircuitCandidateInside] using hxK
  · classical
    intro e he
    have hboundary : ∃ t : ZMod (k.1.val + 3), e = outerCircuitBoundaryEdge k t := by
      simpa [outerCircuitCandidateSupport] using he
    obtain ⟨t, rfl⟩ := hboundary
    have hp : (c.map RSW.polygonRayLatticeHom).IsCycle :=
      (c.isCycle_map_iff_of_injective
        (f := RSW.polygonRayLatticeHom) (by intro a b hab; exact hab)).mpr hc
    have hRedgeMapped : (R.boundaryBond t).toSym2 ∈
        (c.map RSW.polygonRayLatticeHom).edges := by
      apply (FKC.latticePolygonOfCycle_edge_iff hp _).2
      exact ⟨t, R.boundaryBond_toSym2 t⟩
    have hRedge : (R.boundaryBond t).toSym2 ∈ c.edges := by
      simpa [RSW.polygonRayLatticeHom, Sym2.map_id] using hRedgeMapped
    rcases hEdges _ hRedge with hPedge | hQedge
    · obtain ⟨u, hEq⟩ := sourcePolygonWalk_edge_index P
        (u := (R.boundaryBond t).source) (v := (R.boundaryBond t).target)
        (by simpa [FKC.Medial.LatticeBond.toSym2] using hPedge)
      have hsym : (R.boundaryBond t).toSym2 = (P.boundaryBond u).toSym2 := by
        calc
          (R.boundaryBond t).toSym2 =
              s((R.boundaryBond t).source, (R.boundaryBond t).target) := rfl
          _ = s(P.vertex u, P.vertex (u+1)) := hEq
          _ = (P.boundaryBond u).toSym2 := (P.boundaryBond_toSym2 u).symm
      have hbonds : R.boundaryBond t = P.boundaryBond u :=
        FKC.Medial.LatticeBond.toSym2_injective hsym
      have hinput : outerCircuitHostEdgeBond (outerCircuitBoundaryEdge k t) =
          (outerCircuitCodePolygon i).boundaryBond u := by
        calc
          outerCircuitHostEdgeBond (outerCircuitBoundaryEdge k t) =
              (outerCircuitCodePolygon k).boundaryBond t :=
            outerCircuitHostEdgeBond_boundaryBond k t
          _ = R.boundaryBond t := by rw [hcode]; rfl
          _ = P.boundaryBond u := hbonds
          _ = (outerCircuitCodePolygon i).boundaryBond u := rfl
      exact Finset.mem_union.mpr (Or.inl
        (outerCircuitHostEdge_mem_candidateSupport_of_boundaryBond i _ u hinput))
    · obtain ⟨u, hEq⟩ := sourcePolygonWalk_edge_index Q
        (u := (R.boundaryBond t).source) (v := (R.boundaryBond t).target)
        (by simpa [FKC.Medial.LatticeBond.toSym2] using hQedge)
      have hsym : (R.boundaryBond t).toSym2 = (Q.boundaryBond u).toSym2 := by
        calc
          (R.boundaryBond t).toSym2 =
              s((R.boundaryBond t).source, (R.boundaryBond t).target) := rfl
          _ = s(Q.vertex u, Q.vertex (u+1)) := hEq
          _ = (Q.boundaryBond u).toSym2 := (Q.boundaryBond_toSym2 u).symm
      have hbonds : R.boundaryBond t = Q.boundaryBond u :=
        FKC.Medial.LatticeBond.toSym2_injective hsym
      have hinput : outerCircuitHostEdgeBond (outerCircuitBoundaryEdge k t) =
          (outerCircuitCodePolygon j).boundaryBond u := by
        calc
          outerCircuitHostEdgeBond (outerCircuitBoundaryEdge k t) =
              (outerCircuitCodePolygon k).boundaryBond t :=
            outerCircuitHostEdgeBond_boundaryBond k t
          _ = R.boundaryBond t := by rw [hcode]; rfl
          _ = Q.boundaryBond u := hbonds
          _ = (outerCircuitCodePolygon j).boundaryBond u := rfl
      exact Finset.mem_union.mpr (Or.inr
        (outerCircuitHostEdge_mem_candidateSupport_of_boundaryBond j _ u hinput))

theorem outerCircuitCandidateSupport_subset_outside_of_region_subset {n : ℕ}
    (i j : OuterCircuitPolygonCode n)
    (hinside : outerCircuitCandidateInside i ⊆ outerCircuitCandidateInside j) :
    outerCircuitCandidateSupport j ⊆
      outerCircuitOutside (outerCircuitCandidateInside i) := by
  classical
  intro e he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change ¬ ((∃ x ∈ outerCircuitCandidateInside i,
      x.val = (outerCircuitHostEdgeBond e).faceBase true) ∧
    (∃ y ∈ outerCircuitCandidateInside i,
      y.val = (outerCircuitHostEdgeBond e).faceBase false))
  intro hboth
  have houtsideJ := outerCircuitCandidateSupport_subset_outside j he
  have hnotJ : ¬ ((∃ x ∈ outerCircuitCandidateInside j,
      x.val = (outerCircuitHostEdgeBond e).faceBase true) ∧
    (∃ y ∈ outerCircuitCandidateInside j,
      y.val = (outerCircuitHostEdgeBond e).faceBase false)) := by
    simpa [outerCircuitOutside] using (Finset.mem_filter.mp houtsideJ).2
  apply hnotJ
  constructor
  · rcases hboth.1 with ⟨x, hx, hval⟩
    exact ⟨x, hinside hx, hval⟩
  · rcases hboth.2 with ⟨y, hy, hval⟩
    exact ⟨y, hinside hy, hval⟩

end
end PottsContinuity.OuterCircuit
