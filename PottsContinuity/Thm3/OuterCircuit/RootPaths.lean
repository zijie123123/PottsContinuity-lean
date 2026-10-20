module

public import PottsContinuity.Thm3.OuterCircuit.ResidualClosure

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.FKC.Medial

noncomputable section

local instance outerCircuitRootPathEdgeFintype (n : ℕ) :
    Fintype (lemma4AmbientGraph n).edgeSet := Fintype.ofFinite _

local instance outerCircuitRootPathEdgeDecidableEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _

theorem outerCircuitSourceWalk_support_in_host {n : ℕ}
    (p : OuterCircuitPolygonCode n) {x : PD.FK.LatticeVertex}
    (hx : x ∈ (sourcePolygonWalk (outerCircuitCodePolygon p)).support) :
    x ∈ PD.box (56*n) := by
  let P := outerCircuitCodePolygon p
  have hnotnil : ¬ (sourcePolygonWalk P).Nil := by
    intro hnil
    have hlen := (sourcePolygonWalk_isCycle P).three_le_length
    have hzero : (sourcePolygonWalk P).length = 0 :=
      (SimpleGraph.Walk.length_eq_zero_iff).mpr hnil
    omega
  obtain ⟨e, he, hxedge⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnotnil).mp hx
  induction e using Sym2.inductionOn with
  | _ u v =>
    have he' : s(u,v) ∈ (sourcePolygonWalk P).edges := by
      simpa using he
    obtain ⟨i, hi⟩ := sourcePolygonWalk_edge_index P he'
    have hu_box : u ∈ PD.box (56*n) := by
      rcases Sym2.eq_iff.mp hi with ⟨hu, _⟩ | ⟨hu, _⟩
      · rw [hu]
        exact outerCircuitCodePolygon_vertex_mem p i
      · rw [hu]
        exact outerCircuitCodePolygon_vertex_mem p (i + 1)
    have hv_box : v ∈ PD.box (56*n) := by
      rcases Sym2.eq_iff.mp hi with ⟨_, hv⟩ | ⟨_, hv⟩
      · rw [hv]
        exact outerCircuitCodePolygon_vertex_mem p (i + 1)
      · rw [hv]
        exact outerCircuitCodePolygon_vertex_mem p i
    have hx' : x = u ∨ x = v := by
      simpa [Sym2.mem_iff] using hxedge
    rcases hx' with hx | hx
    · simpa [hx] using hu_box
    · simpa [hx] using hv_box

def outerCircuitOriginHostVertex (n : ℕ) : OuterCircuitHostVertex n :=
  ⟨(0,0), by simp [PottsContinuity.box]⟩

noncomputable def outerCircuitRootOfIndex {n : ℕ}
    (i : OuterCircuitSelectorIndex n) : OuterCircuitHostVertex n :=
  match i with
  | .inl p =>
    ⟨(sourcePolygonWalk (outerCircuitCodePolygon p)).getVert 0,
      outerCircuitSourceWalk_support_in_host p
        ((sourcePolygonWalk (outerCircuitCodePolygon p)).getVert_mem_support 0)⟩
  | .inr _ => outerCircuitOriginHostVertex n

/-- On a selected observation this is the start vertex of its selected source
circuit. It is totalized at the origin only on records with no polygon
candidate, where the root-path record fields impose no condition. -/
noncomputable def outerCircuitSelectedRoot {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) : OuterCircuitHostVertex n :=
  (outerCircuitMaximumCandidate C).elim (outerCircuitOriginHostVertex n)
    outerCircuitRootOfIndex

def outerCircuitResidualBoundarySet {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    Set (OuterCircuitResidualVertices n C) :=
  {x | outerCircuitResidualBoundaryVertex C x.val}

private theorem outerCircuitWalk_getVert_transfer
    {V : Type*} {G H : SimpleGraph V} {u v : V}
    (P : G.Walk u v)
    (h : ∀ e, e ∈ P.edges → e ∈ H.edgeSet) (j : ℕ) :
    (P.transfer H h).getVert j = P.getVert j := by
  revert h
  induction P generalizing j with
  | nil =>
      intro h
      cases j <;> rfl
  | @cons u v w huv tail ih =>
      intro h
      cases j with
      | zero => rfl
      | succ j => exact ih j (fun e he => h e (by simp [he]))

theorem outerCircuitSourceOpenCircuitWalk {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    (hvalid : outerCircuitCandidateValid C p) :
    ∃ W : (openGraph (lemma4AmbientGraph n)
      (C ∩ outerCircuitSelectorReveal C)).Walk
      ⟨(sourcePolygonWalk (outerCircuitCodePolygon p)).getVert 0,
        outerCircuitSourceWalk_support_in_host p
          ((sourcePolygonWalk (outerCircuitCodePolygon p)).getVert_mem_support 0)⟩
      ⟨(sourcePolygonWalk (outerCircuitCodePolygon p)).getVert 0,
        outerCircuitSourceWalk_support_in_host p
          ((sourcePolygonWalk (outerCircuitCodePolygon p)).getVert_mem_support 0)⟩,
      ∀ j : Fin (p.1.val + 3),
        W.getVert j.val =
          ⟨(outerCircuitCodePolygon p).vertex (j.val : ZMod (p.1.val + 3)),
            outerCircuitCodePolygon_vertex_mem p (j.val : ZMod (p.1.val + 3))⟩ := by
  let S := sourcePolygonWalk (outerCircuitCodePolygon p)
  have hsupport : ∀ z ∈ S.support,
      z ∈ (PottsContinuity.box (56*n) : Set PD.FK.LatticeVertex) := by
    intro z hz
    apply Finset.mem_coe.mpr
    simpa only [PD.box, PottsContinuity.box] using
      outerCircuitSourceWalk_support_in_host p hz
  let W := S.induce (PottsContinuity.box (56*n)) hsupport
  have hWmap : W.map (SimpleGraph.Embedding.induce (G := PD.FK.squareLattice)
      (PottsContinuity.box (56*n) : Set PD.FK.LatticeVertex)).toHom = S := by
    exact SimpleGraph.Walk.map_induce S hsupport
  have hWedgesMap :
      (W.map (SimpleGraph.Embedding.induce (G := PD.FK.squareLattice)
        (PottsContinuity.box (56*n) : Set PD.FK.LatticeVertex)).toHom).edges =
        W.edges.map (Sym2.map Subtype.val) := by
    exact SimpleGraph.Walk.edges_map _ W
  have hWedgesEq :
      (W.map (SimpleGraph.Embedding.induce (G := PD.FK.squareLattice)
        (PottsContinuity.box (56*n) : Set PD.FK.LatticeVertex)).toHom).edges = S.edges :=
    congrArg SimpleGraph.Walk.edges hWmap
  have hWedges : ∀ e, e ∈ W.edges →
      e ∈ (openGraph (lemma4AmbientGraph n)
        (C ∩ outerCircuitSelectorReveal C)).edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : (lemma4AmbientGraph n).Adj x y := W.adj_of_mem_edges (by simpa using he)
      have hsource : s(x.val,y.val) ∈ S.edges := by
        have heMapped : s(x.val,y.val) ∈
            (W.edges.map (Sym2.map Subtype.val)) := by
          exact List.mem_map.mpr ⟨s(x,y), by simpa using he, by simp⟩
        rw [← hWedgesEq, hWedgesMap]
        exact heMapped
      obtain ⟨i, hidx⟩ := sourcePolygonWalk_edge_index
        (outerCircuitCodePolygon p) hsource
      let e' : (lemma4AmbientGraph n).edgeSet := ⟨s(x,y),
        (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩
      have himage : Sym2.map Subtype.val e'.val =
          Sym2.map Subtype.val (outerCircuitBoundaryEdge p i).val := by
        change s(x.val,y.val) = _
        rw [outerCircuitBoundaryEdge_val]
        exact hidx
      have heq : e' = outerCircuitBoundaryEdge p i := by
        apply Subtype.ext
        exact (Function.Embedding.sym2Map
          ⟨Subtype.val, Subtype.val_injective⟩).injective himage
      have hopen : outerCircuitBoundaryEdge p i ∈ C := hvalid.2.2 i
      have heopen : e' ∈ C := by simpa only [heq] using hopen
      have hsupp : outerCircuitBoundaryEdge p i ∈ outerCircuitCandidateSupport p :=
        outerCircuitBoundaryEdge_mem_support p i
      have hout : outerCircuitBoundaryEdge p i ∈
          outerCircuitOutside (outerCircuitCandidateInside p) :=
        outerCircuitCandidateSupport_subset_outside p hsupp
      have hrevealed : outerCircuitBoundaryEdge p i ∈ outerCircuitSelectorReveal C := by
        rw [outerCircuitSelectorReveal_eq_candidateOutside C p hselected]
        exact hout
      have heRecord : e' ∈ C ∩ outerCircuitSelectorReveal C := by
        apply Finset.mem_inter.mpr
        exact ⟨heopen, by simpa only [heq] using hrevealed⟩
      rw [openGraph_edgeSet]
      exact (coe_mem_openEdges_iff (lemma4AmbientGraph n)
        (C ∩ outerCircuitSelectorReveal C) e').mpr heRecord
  let Wopen := W.transfer (openGraph (lemma4AmbientGraph n)
    (C ∩ outerCircuitSelectorReveal C)) hWedges
  let root : OuterCircuitHostVertex n :=
    ⟨S.getVert 0, outerCircuitSourceWalk_support_in_host p
      (S.getVert_mem_support 0)⟩
  let Q : (openGraph (lemma4AmbientGraph n)
      (C ∩ outerCircuitSelectorReveal C)).Walk root root := Wopen.copy (by
      apply Subtype.ext
      simp [S, root, SimpleGraph.Walk.getVert_zero]) (by
      apply Subtype.ext
      simp [S, root, SimpleGraph.Walk.getVert_zero])
  refine ⟨Q, ?_⟩
  intro j
  apply Subtype.ext
  have htransfer := outerCircuitWalk_getVert_transfer W hWedges j.val
  have hmapVert := congrArg (fun Q : _ => Q.getVert j.val) hWmap
  have hinduce : (W.getVert j.val).val = S.getVert j.val := by
    simp only [SimpleGraph.Walk.getVert_map] at hmapVert
    simp only [SimpleGraph.Embedding.induce] at hmapVert
    change (W.getVert j.val).val = S.getVert j.val at hmapVert
    exact hmapVert
  have hindexed := sourcePolygonWalk_indexed_vertex
    (outerCircuitCodePolygon p) j
  calc
    (Q.getVert j.val).val = (W.getVert j.val).val := by
      calc
        (Q.getVert j.val).val = (Wopen.getVert j.val).val := by simp [Q]
        _ = (W.getVert j.val).val := by
          simpa only [Wopen] using congrArg Subtype.val htransfer
    _ = S.getVert j.val := hinduce
    _ = (outerCircuitCodePolygon p).vertex (j.val : ZMod (p.1.val + 3)) := hindexed

theorem outerCircuitSelectedBoundary_actualConnected {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    (hvalid : outerCircuitCandidateValid C p)
    {x : OuterCircuitHostVertex n}
    (hB : outerCircuitResidualBoundaryVertex C x) :
    ActualConnected (lemma4AmbientGraph n)
      (C ∩ outerCircuitSelectorReveal C) x (outerCircuitSelectedRoot C) := by
  rcases hB with ⟨q, hq, j, hx⟩
  have hqp : q = p := by
    have hsum : Sum.inl q = Sum.inl p := Option.some.inj (hq.symm.trans hselected)
    exact Sum.inl.inj hsum
  subst q
  obtain ⟨W, hindexed⟩ := outerCircuitSourceOpenCircuitWalk C p hselected hvalid
  have hxW : x = W.getVert j.val := by
    apply Subtype.ext
    calc
      x.val = (outerCircuitCodePolygon p).vertex
          (j.val : ZMod (p.1.val + 3)) := hx
      _ = (W.getVert j.val).val := (congrArg Subtype.val (hindexed j)).symm
  have hrootSelected : outerCircuitSelectedRoot C =
      (⟨(sourcePolygonWalk (outerCircuitCodePolygon p)).getVert 0,
        outerCircuitSourceWalk_support_in_host p
          ((sourcePolygonWalk (outerCircuitCodePolygon p)).getVert_mem_support 0)⟩ :
        OuterCircuitHostVertex n) := by
    simp [outerCircuitSelectedRoot, outerCircuitRootOfIndex, hselected]
  rw [actualConnected_iff_walk]
  refine ⟨(W.take j.val).reverse.copy hxW.symm hrootSelected.symm⟩

theorem outerCircuitResidualBoundary_actualConnected_of_removed {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    (hvalid : outerCircuitCandidateValid C p)
    (hremoved : outerCircuitSelectorReveal C =
      subgraphRemovedEdges ((outerCircuitResidualGraph C).map
        (outerCircuitResidualEmbedding C)) (lemma4AmbientGraph n))
    {x : OuterCircuitResidualVertices n C}
    (hB : x ∈ outerCircuitResidualBoundarySet C) :
    ActualConnected (lemma4AmbientGraph n)
      (C ∩ subgraphRemovedEdges ((outerCircuitResidualGraph C).map
        (outerCircuitResidualEmbedding C)) (lemma4AmbientGraph n))
      (outerCircuitResidualEmbedding C x) (outerCircuitSelectedRoot C) := by
  have hconn := outerCircuitSelectedBoundary_actualConnected C p hselected hvalid
    (by simpa [outerCircuitResidualBoundarySet] using hB)
  change ActualConnected (lemma4AmbientGraph n)
    (C ∩ subgraphRemovedEdges ((outerCircuitResidualGraph C).map
      (outerCircuitResidualEmbedding C)) (lemma4AmbientGraph n))
    x.val (outerCircuitSelectedRoot C)
  simpa only [hremoved] using hconn

end
end PottsContinuity.OuterCircuit
