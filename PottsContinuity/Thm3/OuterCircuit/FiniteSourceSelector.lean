module

public import PottsContinuity.Thm3.OuterCircuit.FinitePolygonFamily
public import PottsContinuity.Thm3.RSW.PolygonRayCell
public import PottsContinuity.Exploration.FiniteEnvelopeMaxSelector
public import PottsContinuity.FKC.Medial.WholePlaneDualConfiguration
public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryGraph

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open PottsContinuity.RSW
open PottsContinuity.Exploration

noncomputable section

noncomputable instance outerCircuitAmbientEdgeFintype (n : ℕ) :
    Fintype (lemma4AmbientGraph n).edgeSet := Fintype.ofFinite _

noncomputable instance outerCircuitAmbientEdgeDecidableEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _

/-- A source-box edge, mapped through the two lattice coordinate identities
into the FKC edge carrier. -/
def outerCircuitHostEdgeToFKC {n : ℕ} :
    (lemma4AmbientGraph n).edgeSet → FKC.squareLattice.edgeSet :=
  (RSW.polygonRayLatticeHom.comp
    (SimpleGraph.Embedding.induce (G := PD.FK.squareLattice)
      (PD.box (56*n) : Set PD.FK.LatticeVertex)).toHom).mapEdgeSet

/-- The whole-plane bond across one source-box edge. -/
def outerCircuitHostEdgeBond {n : ℕ}
    (e : (lemma4AmbientGraph n).edgeSet) : LatticeBond :=
  wholePlaneBondEdgeEquiv.symm (outerCircuitHostEdgeToFKC e)

theorem outerCircuitHostEdgeBond_injective {n : ℕ} :
    Function.Injective (outerCircuitHostEdgeBond (n := n)) := by
  intro e f hef
  apply Subtype.ext
  have hmap : outerCircuitHostEdgeToFKC e = outerCircuitHostEdgeToFKC f :=
    wholePlaneBondEdgeEquiv.symm.injective hef
  unfold outerCircuitHostEdgeToFKC at hmap
  let h := RSW.polygonRayLatticeHom.comp
    (SimpleGraph.Embedding.induce (G := PD.FK.squareLattice)
      (PD.box (56*n) : Set PD.FK.LatticeVertex)).toHom
  have hfun : Function.Injective h := by
    intro u v huv
    apply Subtype.ext
    exact huv
  have hef' : e = f := SimpleGraph.Hom.mapEdgeSet.injective (f := h) hfun hmap
  exact congrArg Subtype.val hef'

/-- The source polygon bond at one cyclic index, viewed in the ambient box. -/
def outerCircuitBoundaryEdge {n : ℕ} (i : OuterCircuitPolygonCode n)
    (j : ZMod (i.1.val + 3)) : (lemma4AmbientGraph n).edgeSet := by
  let P := outerCircuitCodePolygon i
  let u : OuterCircuitHostVertex n :=
    ⟨P.vertex j, outerCircuitCodePolygon_vertex_mem i j⟩
  let v : OuterCircuitHostVertex n :=
    ⟨P.vertex (j + 1), outerCircuitCodePolygon_vertex_mem i (j + 1)⟩
  have huv : (lemma4AmbientGraph n).Adj u v := by
    change PD.FK.squareLattice.Adj u.val v.val
    exact (PD.FK.squareLattice_adj_iff u.val v.val).2
      ((FKC.squareLattice_adj_iff u.val v.val).1 (P.adjacent j))
  exact ⟨s(u, v), (lemma4AmbientGraph n).mem_edgeSet.mpr huv⟩

theorem outerCircuitBoundaryEdge_val {n : ℕ}
    (i : OuterCircuitPolygonCode n) (j : ZMod (i.1.val + 3)) :
    (outerCircuitBoundaryEdge i j).val =
      s(⟨(outerCircuitCodePolygon i).vertex j,
          outerCircuitCodePolygon_vertex_mem i j⟩,
        ⟨(outerCircuitCodePolygon i).vertex (j+1),
          outerCircuitCodePolygon_vertex_mem i (j+1)⟩) := by
  rfl

theorem outerCircuitHostEdgeBond_boundaryBond {n : ℕ}
    (i : OuterCircuitPolygonCode n) (j : ZMod (i.1.val + 3)) :
    outerCircuitHostEdgeBond (outerCircuitBoundaryEdge i j) =
      (outerCircuitCodePolygon i).boundaryBond j := by
  apply wholePlaneBondEdgeEquiv.injective
  apply Subtype.ext
  simp only [outerCircuitHostEdgeBond, Equiv.apply_symm_apply]
  unfold outerCircuitHostEdgeToFKC
  change _ = ((outerCircuitCodePolygon i).boundaryBond j).toSym2
  rw [(outerCircuitCodePolygon i).boundaryBond_toSym2]
  change Sym2.map
    (fun x : OuterCircuitHostVertex n =>
      RSW.polygonRayLatticeHom
        (SimpleGraph.Embedding.induce (G := PD.FK.squareLattice)
          (PD.box (56*n) : Set PD.FK.LatticeVertex) x))
    (s(⟨(outerCircuitCodePolygon i).vertex j,
        outerCircuitCodePolygon_vertex_mem i j⟩,
      ⟨(outerCircuitCodePolygon i).vertex (j+1),
        outerCircuitCodePolygon_vertex_mem i (j+1)⟩)) = _
  have hfun : (fun x : OuterCircuitHostVertex n =>
      RSW.polygonRayLatticeHom
        (SimpleGraph.Embedding.induce (G := PD.FK.squareLattice)
          (PD.box (56*n) : Set PD.FK.LatticeVertex) x)) =
      (fun x => x.val) := by
    funext x
    rfl
  rw [hfun]
  simp

/-- Candidate source geometry and openness on its literal sampled bonds. -/
def outerCircuitCandidateValid {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) (i : OuterCircuitPolygonCode n) : Prop :=
  FKC.latticeEmbed ⟨1, zero_lt_one⟩ (0, 0) ∈
      (outerCircuitCodePolygon i).domain ⟨1, zero_lt_one⟩ ∧
    (∀ j : ZMod (i.1.val + 3),
      (7*n : ℤ) < max |((outerCircuitCodePolygon i).vertex j).1|
        |((outerCircuitCodePolygon i).vertex j).2| ∧
      max |((outerCircuitCodePolygon i).vertex j).1|
        |((outerCircuitCodePolygon i).vertex j).2| ≤ (14*n : ℤ)) ∧
    ∀ j : ZMod (i.1.val + 3), outerCircuitBoundaryEdge i j ∈ C

/-- The finite set of host lattice vertices that are bases of interior cells. -/
def outerCircuitCandidateInside {n : ℕ} (i : OuterCircuitPolygonCode n) :
    Finset (OuterCircuitHostVertex n) := by
  classical
  exact Finset.univ.filter fun x =>
    x.val ∈ (outerCircuitCodePolygon i).interiorCellBases ⟨1, zero_lt_one⟩

/-- The sampled bonds that directly recognize one candidate polygon. -/
def outerCircuitCandidateSupport {n : ℕ} (i : OuterCircuitPolygonCode n) :
    Finset (lemma4AmbientGraph n).edgeSet := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ j : ZMod (i.1.val + 3), e = outerCircuitBoundaryEdge i j

/-- The edges exterior to the cell interior of one finite candidate region. -/
def outerCircuitOutside {n : ℕ}
    (S : Finset (OuterCircuitHostVertex n)) :
    Finset (lemma4AmbientGraph n).edgeSet := by
  classical
  exact Finset.univ.filter fun e =>
    let b := outerCircuitHostEdgeBond e
    ¬ ((∃ x ∈ S, x.val = b.faceBase true) ∧
      (∃ y ∈ S, y.val = b.faceBase false))

theorem outerCircuitBoundaryEdge_mem_support {n : ℕ}
    (i : OuterCircuitPolygonCode n) (j : ZMod (i.1.val + 3)) :
    outerCircuitBoundaryEdge i j ∈ outerCircuitCandidateSupport i := by
  classical
  simp [outerCircuitCandidateSupport]

theorem outerCircuitHostEdge_mem_candidateSupport_of_boundaryBond {n : ℕ}
    (i : OuterCircuitPolygonCode n) (e : (lemma4AmbientGraph n).edgeSet)
    (j : ZMod (i.1.val + 3))
    (hbond : outerCircuitHostEdgeBond e =
      (outerCircuitCodePolygon i).boundaryBond j) :
    e ∈ outerCircuitCandidateSupport i := by
  have heq : e = outerCircuitBoundaryEdge i j :=
    outerCircuitHostEdgeBond_injective (hbond.trans
      (outerCircuitHostEdgeBond_boundaryBond i j).symm)
  rw [heq]
  exact outerCircuitBoundaryEdge_mem_support i j

/-- Candidate validity reads the sample only on its ordered boundary bonds. -/
theorem outerCircuitCandidateValid_eq_of_support_agreement {n : ℕ}
    (C C' : Configuration (lemma4AmbientGraph n))
    (i : OuterCircuitPolygonCode n)
    (hagree : Exploration.candidateStatesAgree C C'
      (outerCircuitCandidateSupport i)) :
    outerCircuitCandidateValid C i ↔ outerCircuitCandidateValid C' i := by
  unfold outerCircuitCandidateValid
  constructor
  · rintro ⟨hcenter, hradial, hopen⟩
    refine ⟨hcenter, hradial, ?_⟩
    intro j
    exact (hagree (outerCircuitBoundaryEdge i j)
      (outerCircuitBoundaryEdge_mem_support i j)).mp (hopen j)
  · rintro ⟨hcenter, hradial, hopen⟩
    refine ⟨hcenter, hradial, ?_⟩
    intro j
    exact (hagree (outerCircuitBoundaryEdge i j)
      (outerCircuitBoundaryEdge_mem_support i j)).mpr (hopen j)

theorem outerCircuitCandidateSupport_subset_outside {n : ℕ}
    (i : OuterCircuitPolygonCode n) :
    outerCircuitCandidateSupport i ⊆
      outerCircuitOutside (outerCircuitCandidateInside i) := by
  classical
  intro e he
  have he' : ∃ j : ZMod (i.1.val + 3), e = outerCircuitBoundaryEdge i j := by
    simpa [outerCircuitCandidateSupport] using he
  rcases he' with ⟨j, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change ¬ ((∃ x ∈ outerCircuitCandidateInside i,
      x.val = (outerCircuitHostEdgeBond (outerCircuitBoundaryEdge i j)).faceBase true) ∧
    (∃ y ∈ outerCircuitCandidateInside i,
      y.val = (outerCircuitHostEdgeBond (outerCircuitBoundaryEdge i j)).faceBase false))
  rw [outerCircuitHostEdgeBond_boundaryBond]
  intro hboth
  let P := outerCircuitCodePolygon i
  let δ : FKC.PositiveMesh := ⟨1, zero_lt_one⟩
  have hboundary := (FKC.LatticePolygon.mem_latticeCellBoundaryBonds_interiorCellBases_iff_boundaryBond
    P δ (P.boundaryBond j)).2 ⟨j, rfl⟩
  have hdiff := (FKC.mem_latticeCellBoundaryBonds _ _).mp hboundary
  have htrue : (P.boundaryBond j).faceBase true ∈ P.interiorCellBases δ := by
    rcases hboth.1 with ⟨x, hx, hval⟩
    have hx' : x.val ∈ P.interiorCellBases δ := by
      simpa [outerCircuitCandidateInside, P, δ] using hx
    rw [← hval]
    exact hx'
  have hfalse : (P.boundaryBond j).faceBase false ∈ P.interiorCellBases δ := by
    rcases hboth.2 with ⟨y, hy, hval⟩
    have hy' : y.val ∈ P.interiorCellBases δ := by
      simpa [outerCircuitCandidateInside, P, δ] using hy
    rw [← hval]
    exact hy'
  exact hdiff (propext ⟨fun _ => hfalse, fun _ => htrue⟩)

end
end PottsContinuity.OuterCircuit
