module

public import PottsContinuity.Thm3.OuterCircuit.SelectedRecord
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryVertexStar

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Exploration
open PottsContinuity.FKC.Medial

noncomputable section

local instance outerCircuitResidualEdgeFintype (n : ℕ) :
    Fintype (lemma4AmbientGraph n).edgeSet := Fintype.ofFinite _

local instance outerCircuitResidualEdgeDecidableEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _

def outerCircuitFourCellStar (x : FKC.LatticeVertex) :
    Finset FKC.LatticeVertex :=
  {x, (x.1 - 1, x.2), (x.1, x.2 - 1), (x.1 - 1, x.2 - 1)}

theorem outerCircuitBond_faceBases_mem_fourCellStar
    (b : FKC.Medial.LatticeBond) (x : FKC.LatticeVertex)
    (hx : x = b.source ∨ x = b.target) :
    b.faceBase true ∈ outerCircuitFourCellStar x ∧
      b.faceBase false ∈ outerCircuitFourCellStar x := by
  rcases b with ⟨⟨a, c⟩, axis⟩
  cases axis with
  | horizontal =>
    rcases hx with hx | hx
    · subst x
      simp [outerCircuitFourCellStar, FKC.Medial.LatticeBond.source,
        FKC.Medial.LatticeBond.faceBase]
    · subst x
      simp [outerCircuitFourCellStar, FKC.Medial.LatticeBond.target,
        FKC.Medial.LatticeBond.faceBase]
  | vertical =>
    rcases hx with hx | hx
    · subst x
      simp [outerCircuitFourCellStar, FKC.Medial.LatticeBond.source,
        FKC.Medial.LatticeBond.faceBase]
    · subst x
      simp [outerCircuitFourCellStar, FKC.Medial.LatticeBond.target,
        FKC.Medial.LatticeBond.faceBase]

theorem outerCircuitHostEdgeBond_faceBases_mem_fourCellStar {n : ℕ}
    (x y : OuterCircuitHostVertex n)
    (hxy : (lemma4AmbientGraph n).Adj x y) :
    (outerCircuitHostEdgeBond ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩).faceBase true ∈
        outerCircuitFourCellStar x.val ∧
      (outerCircuitHostEdgeBond ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩).faceBase false ∈
        outerCircuitFourCellStar x.val := by
  let e : (lemma4AmbientGraph n).edgeSet :=
    ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩
  let b := outerCircuitHostEdgeBond e
  have hb : b.toSym2 = s(x.val,y.val) := by
    have heq := wholePlaneBondEdgeEquiv.apply_symm_apply
      (outerCircuitHostEdgeToFKC e)
    have hval := congrArg Subtype.val heq
    change b.toSym2 = (outerCircuitHostEdgeToFKC e).val at hval
    unfold outerCircuitHostEdgeToFKC at hval
    change b.toSym2 = Sym2.map
      (fun z : OuterCircuitHostVertex n =>
        RSW.polygonRayLatticeHom
          (SimpleGraph.Embedding.induce (G := PD.FK.squareLattice)
            (PD.box (56*n) : Set PD.FK.LatticeVertex) z))
      (s(x,y)) at hval
    change b.toSym2 = s(x.val,y.val) at hval
    exact hval
  have hincident : x.val ∈ b.toSym2 := by
    rw [hb]
    simp
  rcases Sym2.mem_iff.mp hincident with hx | hx
  · have hstar := outerCircuitBond_faceBases_mem_fourCellStar b x.val (Or.inl hx)
    exact hstar
  · have hstar := outerCircuitBond_faceBases_mem_fourCellStar b x.val (Or.inr hx)
    exact hstar

noncomputable def outerCircuitUnrevealedAmbientGraph {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    SimpleGraph (OuterCircuitHostVertex n) := by
  classical
  exact SimpleGraph.fromEdgeSet
    {e | ∃ he : e ∈ (lemma4AmbientGraph n).edgeSet,
      (⟨e, he⟩ : (lemma4AmbientGraph n).edgeSet) ∉
        outerCircuitSelectorReveal (n := n) C}

def outerCircuitResidualVertex {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (x : OuterCircuitHostVertex n) : Prop :=
  (∃ y : OuterCircuitHostVertex n,
      (outerCircuitUnrevealedAmbientGraph C).Adj x y) ∨
    (∃ p : OuterCircuitPolygonCode n,
      outerCircuitMaximumCandidate C = some (.inl p) ∧
      ∃ j : Fin (p.1.val + 3),
        x.val = (outerCircuitCodePolygon p).vertex
          (j.val : ZMod (p.1.val + 3)))

abbrev OuterCircuitResidualVertices (n : ℕ)
    (C : Configuration (lemma4AmbientGraph n)) :=
  {x : OuterCircuitHostVertex n // outerCircuitResidualVertex C x}

theorem outerCircuitUnrevealedAmbientGraph_adj {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (x y : OuterCircuitHostVertex n) :
    (outerCircuitUnrevealedAmbientGraph C).Adj x y ↔
      ∃ hxy : (lemma4AmbientGraph n).Adj x y,
        (⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩ :
          (lemma4AmbientGraph n).edgeSet) ∉ outerCircuitSelectorReveal C := by
  rw [outerCircuitUnrevealedAmbientGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨he, hopen⟩, _⟩
    have hxy : (lemma4AmbientGraph n).Adj x y :=
      (lemma4AmbientGraph n).mem_edgeSet.mp he
    refine ⟨hxy, ?_⟩
    have heEq : (⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩ :
        (lemma4AmbientGraph n).edgeSet) = ⟨s(x,y), he⟩ := by
      apply Subtype.ext
      rfl
    simpa only [heEq] using hopen
  · rintro ⟨hxy, hopen⟩
    refine ⟨⟨(lemma4AmbientGraph n).mem_edgeSet.mpr hxy, hopen⟩, ?_⟩
    exact (lemma4AmbientGraph n).ne_of_adj hxy

theorem outerCircuitUnrevealedAmbientGraph_le {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    outerCircuitUnrevealedAmbientGraph C ≤ lemma4AmbientGraph n := by
  intro x y hxy
  exact ((outerCircuitUnrevealedAmbientGraph_adj C x y).mp hxy).choose

def outerCircuitResidualGraph {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    SimpleGraph (OuterCircuitResidualVertices n C) :=
  (outerCircuitUnrevealedAmbientGraph C).comap Subtype.val

def outerCircuitResidualEmbedding {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    OuterCircuitResidualVertices n C ↪ OuterCircuitHostVertex n :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem outerCircuitResidualGraph_map_eq_unrevealed {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    (outerCircuitResidualGraph C).map (outerCircuitResidualEmbedding C) =
      outerCircuitUnrevealedAmbientGraph C := by
  apply le_antisymm
  · intro x y hxy
    obtain ⟨u, v, huv, hux, hvy⟩ :=
      (SimpleGraph.map_adj _ _ _ _).mp hxy
    have hbase : (outerCircuitUnrevealedAmbientGraph C).Adj u.val v.val := by
      simpa only [outerCircuitResidualGraph, SimpleGraph.comap_adj] using huv
    rw [← hux, ← hvy]
    exact hbase
  · intro x y hxy
    let u : OuterCircuitResidualVertices n C := ⟨x, Or.inl ⟨y, hxy⟩⟩
    let v : OuterCircuitResidualVertices n C := ⟨y, Or.inl ⟨x, hxy.symm⟩⟩
    have huv : (outerCircuitResidualGraph C).Adj u v := by
      change (outerCircuitUnrevealedAmbientGraph C).Adj x y
      exact hxy
    exact (SimpleGraph.map_adj _ _ _ _).2 ⟨u, v, huv, rfl, rfl⟩

theorem outerCircuitResidualGraph_map_le {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    (outerCircuitResidualGraph C).map (outerCircuitResidualEmbedding C) ≤
      lemma4AmbientGraph n := by
  rw [outerCircuitResidualGraph_map_eq_unrevealed]
  exact outerCircuitUnrevealedAmbientGraph_le C

theorem outerCircuitUnrevealedAmbientGraph_edge_mem {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (e : (lemma4AmbientGraph n).edgeSet) :
    e.val ∈ (outerCircuitUnrevealedAmbientGraph C).edgeSet ↔
      e ∉ outerCircuitSelectorReveal C := by
  rw [outerCircuitUnrevealedAmbientGraph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · intro he
    have heS := he.1
    rcases heS with ⟨heAmbient, hopen⟩
    have heq : (⟨e.val, heAmbient⟩ : (lemma4AmbientGraph n).edgeSet) = e := by
      apply Subtype.ext
      rfl
    simpa only [heq] using hopen
  · intro hopen
    refine ⟨⟨e.property, ?_⟩, ?_⟩
    · have heq : (⟨e.val, e.property⟩ : (lemma4AmbientGraph n).edgeSet) = e := by
        apply Subtype.ext
        rfl
      simpa only [heq] using hopen
    · intro hdiag
      exact (lemma4AmbientGraph n).not_isDiag_of_mem_edgeSet e.property
        (Sym2.mem_diagSet.mp hdiag)

theorem outerCircuitResidual_removedEdges_eq_reveal {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    subgraphRemovedEdges ((outerCircuitResidualGraph C).map
      (outerCircuitResidualEmbedding C)) (lemma4AmbientGraph n) =
        outerCircuitSelectorReveal C := by
  rw [outerCircuitResidualGraph_map_eq_unrevealed]
  ext e
  rw [mem_subgraphRemovedEdges]
  constructor
  · intro hnot
    by_contra hopen
    exact hnot ((outerCircuitUnrevealedAmbientGraph_edge_mem C e).2 hopen)
  · intro hopen hmem
    exact ((outerCircuitUnrevealedAmbientGraph_edge_mem C e).1 hmem) hopen

def outerCircuitResidualBoundaryVertex {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (x : OuterCircuitHostVertex n) : Prop :=
  ∃ p : OuterCircuitPolygonCode n,
    outerCircuitMaximumCandidate C = some (.inl p) ∧
    ∃ j : Fin (p.1.val + 3),
      x.val = (outerCircuitCodePolygon p).vertex
        (j.val : ZMod (p.1.val + 3))

theorem outerCircuitPolygon_no_boundary_graph_adjacency {m : ℕ}
    (P : FKC.LatticePolygon m) (δ : FKC.PositiveMesh)
    (x : FKC.LatticeVertex)
    (hx : ∀ i : Fin (m + 3), x ≠ P.vertex (i.val : ZMod (m + 3))) :
    ∀ y, ¬ (FKC.latticeCellBoundaryGraph (P.interiorCellBases δ)).Adj x y := by
  intro y hadj
  obtain ⟨_, e, heq, hfaces⟩ :=
    (FKC.latticeCellBoundaryGraph_adj_iff (P.interiorCellBases δ) x y).mp hadj
  have he : e ∈ FKC.latticeCellBoundaryBonds (P.interiorCellBases δ) :=
    (FKC.mem_latticeCellBoundaryBonds _ _).mpr hfaces
  obtain ⟨i, rfl⟩ :=
    (FKC.LatticePolygon.mem_latticeCellBoundaryBonds_interiorCellBases_iff_boundaryBond
      P δ e).mp he
  rw [P.boundaryBond_toSym2] at heq
  rcases Sym2.eq_iff.mp heq with ⟨hxi, _⟩ | ⟨_, hxi⟩
  · have hnot : x ≠ P.vertex i := by
      simpa using hx ⟨i.val, i.val_lt⟩
    exact hnot hxi.symm
  · have hnot : x ≠ P.vertex (i + 1) := by
      simpa using hx ⟨(i + 1).val, (i + 1).val_lt⟩
    exact hnot hxi.symm

theorem outerCircuitFourCellStar_all_of_center_mem
    (F : Finset FKC.LatticeVertex) (x : FKC.LatticeVertex)
    (hstar :
      ((x ∈ F) ↔ ((x.1 - 1, x.2) ∈ F)) ∧
      ((x ∈ F) ↔ ((x.1, x.2 - 1) ∈ F)) ∧
      (((x.1 - 1, x.2) ∈ F) ↔ ((x.1 - 1, x.2 - 1) ∈ F)) ∧
      (((x.1, x.2 - 1) ∈ F) ↔ ((x.1 - 1, x.2 - 1) ∈ F)))
    (hx : x ∈ F) {y : FKC.LatticeVertex}
    (hy : y ∈ outerCircuitFourCellStar x) : y ∈ F := by
  simp only [outerCircuitFourCellStar, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact hx
  · exact hstar.1.mp hx
  · exact hstar.2.1.mp hx
  · exact hstar.2.2.1.mp (hstar.1.mp hx)

end
end PottsContinuity.OuterCircuit
