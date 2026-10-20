-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleDualBottomCollar.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleBottomCollar
public import PottsContinuity.FKC.FiniteFK.RectangleDualConfiguration
public import PottsContinuity.FKC.FiniteFK.EdgeRestriction

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

abbrev rectangleDualBottomCollarInnerGraph (n : ℕ) :=
  rectangleDualGraph (-(n : ℤ), 0) (2*n) n
abbrev rectangleDualBottomCollarOuterGraph (n : ℕ) :=
  rectangleDualGraph (-(n : ℤ), -1) (2*n) (n+1)
abbrev rectangleDualBottomCollarInnerVertex (n : ℕ) :=
  RectangleDualVertex (-(n : ℤ), 0) (2*n) n
abbrev rectangleDualBottomCollarOuterVertex (n : ℕ) :=
  RectangleDualVertex (-(n : ℤ), -1) (2*n) (n+1)

theorem rectangleDualBottomCollarVertexSubset (n : ℕ) :
    rectangleDualExpanded (-(n : ℤ), 0) (2*n) n ⊆
      rectangleDualExpanded (-(n : ℤ), -1) (2*n) (n+1) := by
  intro z hz
  rw [rectangleDualExpanded, mem_latticeRectangle] at hz ⊢
  rcases hz with ⟨⟨hx1,hx2⟩,⟨hy1,hy2⟩⟩
  exact ⟨⟨hx1,hx2⟩,⟨by omega,by omega⟩⟩

def rectangleDualBottomCollarVertexEmbedding (n : ℕ) :
    rectangleDualBottomCollarInnerVertex n ↪ rectangleDualBottomCollarOuterVertex n :=
  ⟨fun v => ⟨v.val, rectangleDualBottomCollarVertexSubset n v.property⟩,
    fun x y h => by cases x; cases y; simp_all⟩

@[simp] theorem rectangleDualBottomCollarVertexEmbedding_val (n : ℕ)
    (v : rectangleDualBottomCollarInnerVertex n) :
    (rectangleDualBottomCollarVertexEmbedding n v).val = v.val := rfl

theorem rectangleBottomCollar_primalMap_le (n : ℕ) :
    (rectangleBottomCollarInnerGraph n).map (rectangleBottomCollarEmbedding n) ≤
      rectangleBottomCollarOuterGraph n := by
  intro u v huv
  rcases (SimpleGraph.map_adj (rectangleBottomCollarEmbedding n)
      (rectangleBottomCollarInnerGraph n) u v).mp huv with
    ⟨x, y, hxy, rfl, rfl⟩
  have hsquare : squareLattice.Adj x.val y.val :=
    (rectangleGraph_adj_iff _ _ _ _ _).mp hxy
  exact (rectangleGraph_adj_iff _ _ _ _ _).mpr hsquare

def rectangleDualBottomCollarPrimalEdgeEmbedding (n : ℕ) :
    rectanglePrimalEdgeCarrier (-(n:ℤ),0) (2*n) n ↪
      rectanglePrimalEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1) :=
  rectangleEdgeEmbedding (rectangleBottomCollar_subset n)

theorem rectangleDualBottomCollar_primalBond_eq (n : ℕ)
    (e : rectanglePrimalEdgeCarrier (-(n:ℤ),0) (2*n) n) :
    rectanglePrimalEdgeBond (-(n:ℤ),-1) (2*n) (n+1)
      (rectangleDualBottomCollarPrimalEdgeEmbedding n e) =
    rectanglePrimalEdgeBond (-(n:ℤ),0) (2*n) n e := by
  apply LatticeBond.toSym2_injective
  rw [rectanglePrimalEdgeBond_toSym2_public, rectanglePrimalEdgeBond_toSym2_public]
  exact rectangleEdgeEmbedding_original (rectangleBottomCollar_subset n) e

def rectangleDualBottomCollarDualEdgeEmbedding (n : ℕ) :
    RectangleDualEdgeCarrier (-(n:ℤ),0) (2*n) n ↪
      RectangleDualEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1) := by
  let eI := rectanglePrimalDualEdgeEquiv (-(n:ℤ),0) (2*n) n
  let eO := rectanglePrimalDualEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1)
  exact ⟨fun d => eO (rectangleDualBottomCollarPrimalEdgeEmbedding n (eI.symm d)), by
    intro d d' h
    apply eI.symm.injective
    apply (rectangleDualBottomCollarPrimalEdgeEmbedding n).injective
    exact eO.injective h⟩

@[simp] theorem rectangleDualBottomCollarDualEdgeEmbedding_primalEdge (n : ℕ)
    (e : RectangleDualEdgeCarrier (-(n:ℤ),0) (2*n) n) :
    (rectangleDualBottomCollarDualEdgeEmbedding n e).primalEdge =
      rectangleDualBottomCollarPrimalEdgeEmbedding n e.primalEdge := rfl

theorem rectangleDualBottomCollarDualEdgeEmbedding_pair (n : ℕ)
    (e : RectangleDualEdgeCarrier (-(n:ℤ),0) (2*n) n) :
    rectangleDualCarrierPair (-(n:ℤ),-1) (2*n) (n+1)
        (rectangleDualBottomCollarDualEdgeEmbedding n e) =
      Sym2.map (rectangleDualBottomCollarVertexEmbedding n)
        (rectangleDualCarrierPair (-(n:ℤ),0) (2*n) n e) := by
  apply Sym2.eq_iff.mpr
  left
  constructor
  · apply Subtype.ext
    simp only [rectangleDualBottomCollarVertexEmbedding_val]
    calc
      (rectangleDualEdgeSource _ _ _ (rectangleDualBottomCollarDualEdgeEmbedding n e)).val =
          (rectanglePrimalEdgeBond _ _ _
            (rectangleDualBottomCollarPrimalEdgeEmbedding n e.primalEdge)).faceBase false :=
        rectangleDualEdgeSource_faceBase _ _ _ _
      _ = (rectanglePrimalEdgeBond _ _ _ e.primalEdge).faceBase false := by
        rw [rectangleDualBottomCollar_primalBond_eq]
      _ = (rectangleDualEdgeSource _ _ _ e).val :=
        (rectangleDualEdgeSource_faceBase _ _ _ _).symm
  · apply Subtype.ext
    simp only [rectangleDualBottomCollarVertexEmbedding_val]
    calc
      (rectangleDualEdgeTarget _ _ _ (rectangleDualBottomCollarDualEdgeEmbedding n e)).val =
          (rectanglePrimalEdgeBond _ _ _
            (rectangleDualBottomCollarPrimalEdgeEmbedding n e.primalEdge)).faceBase true :=
        rectangleDualEdgeTarget_faceBase _ _ _ _
      _ = (rectanglePrimalEdgeBond _ _ _ e.primalEdge).faceBase true := by
        rw [rectangleDualBottomCollar_primalBond_eq]
      _ = (rectangleDualEdgeTarget _ _ _ e).val :=
        (rectangleDualEdgeTarget_faceBase _ _ _ _).symm

def rectangleDualBottomCollarInnerPrimalEdges (n : ℕ) :
    Finset (rectanglePrimalEdgeCarrier (-(n : ℤ), -1) (2*n) (n+1)) := by
  classical
  exact Finset.univ.filter fun e => e.val ∈
    ((rectangleBottomCollarInnerGraph n).map (rectangleBottomCollarEmbedding n)).edgeSet

@[simp] theorem mem_rectangleDualBottomCollarInnerPrimalEdges (n : ℕ)
    (e : rectanglePrimalEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1)) :
    e ∈ rectangleDualBottomCollarInnerPrimalEdges n ↔
      e.val ∈ ((rectangleBottomCollarInnerGraph n).map
        (rectangleBottomCollarEmbedding n)).edgeSet := by
  simp [rectangleDualBottomCollarInnerPrimalEdges]

theorem rectangleDualBottomCollarInnerPrimalEdges_mem_iff (n : ℕ)
    (e : rectanglePrimalEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1)) :
    e ∈ rectangleDualBottomCollarInnerPrimalEdges n ↔
      ∃ f : rectanglePrimalEdgeCarrier (-(n:ℤ),0) (2*n) n,
        e.val = (rectangleBottomCollarEmbedding n).sym2Map f.val := by
  classical
  rw [mem_rectangleDualBottomCollarInnerPrimalEdges]
  constructor
  · intro he
    rw [SimpleGraph.edgeSet_map, Set.mem_image] at he
    rcases he with ⟨f, hf, hfe⟩
    exact ⟨⟨f, hf⟩, hfe.symm⟩
  · rintro ⟨f, he⟩
    rw [SimpleGraph.edgeSet_map, Set.mem_image]
    exact ⟨f.val, f.property, he.symm⟩

theorem rectangleDualBottomCollarInnerPrimalEdges_mem_iff_embedding (n : ℕ)
    (e : rectanglePrimalEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1)) :
    e ∈ rectangleDualBottomCollarInnerPrimalEdges n ↔
      ∃ f : rectanglePrimalEdgeCarrier (-(n:ℤ),0) (2*n) n,
        rectangleDualBottomCollarPrimalEdgeEmbedding n f = e := by
  rw [rectangleDualBottomCollarInnerPrimalEdges_mem_iff]
  constructor
  · rintro ⟨f, h⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    exact h.symm
  · rintro ⟨f, h⟩
    refine ⟨f, ?_⟩
    exact (congrArg Subtype.val h).symm

theorem rectanglePrimalDualEdgeEquiv_apply_primalEdge {a : LatticeVertex} {w h : ℕ}
    (e : RectangleDualEdgeCarrier a w h) :
    rectanglePrimalDualEdgeEquiv a w h e.primalEdge = e := by
  cases e with
  | mk p cb hcb =>
    subst cb
    rfl

theorem rectangleDualBottomCollarDualEdgeEmbedding_mem (n : ℕ)
    (e : RectangleDualEdgeCarrier (-(n:ℤ),0) (2*n) n) :
    (rectangleDualBottomCollarDualEdgeEmbedding n e).primalEdge ∈
      rectangleDualBottomCollarInnerPrimalEdges n := by
  rw [rectangleDualBottomCollarDualEdgeEmbedding_primalEdge]
  exact rectangleDualBottomCollarInnerPrimalEdges_mem_iff_embedding n _ |>.mpr ⟨e.primalEdge, rfl⟩

theorem rectangleDualBottomCollarDualEdge_mem_iff (n : ℕ)
    (e : RectangleDualEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1)) :
    e.primalEdge ∈ rectangleDualBottomCollarInnerPrimalEdges n ↔
      ∃ f : RectangleDualEdgeCarrier (-(n:ℤ),0) (2*n) n,
        rectangleDualBottomCollarDualEdgeEmbedding n f = e := by
  constructor
  · intro h
    rcases (rectangleDualBottomCollarInnerPrimalEdges_mem_iff_embedding n e.primalEdge).mp h
      with ⟨f, hf⟩
    let dI := (rectanglePrimalDualEdgeEquiv (-(n:ℤ),0) (2*n) n) f
    refine ⟨dI, ?_⟩
    calc
      rectangleDualBottomCollarDualEdgeEmbedding n dI =
          rectanglePrimalDualEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1)
            (rectangleDualBottomCollarPrimalEdgeEmbedding n f) := rfl
      _ = rectanglePrimalDualEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) e.primalEdge :=
        congrArg (rectanglePrimalDualEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1)) hf
      _ = e := rectanglePrimalDualEdgeEquiv_apply_primalEdge e
  · rintro ⟨f, rfl⟩
    exact rectangleDualBottomCollarDualEdgeEmbedding_mem n f

def rectangleDualBottomCollarRemovedDualEdges (n : ℕ) :
    Configuration (rectangleDualBottomCollarOuterGraph n) :=
  rectangleDualConfiguration (-(n : ℤ), -1) (2*n) (n+1)
    (rectangleDualBottomCollarInnerPrimalEdges n)

theorem rectangleDualBottomCollar_dualConfiguration_mem (n : ℕ)
    (e : RectangleDualEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1)) :
    rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) e ∈
      rectangleDualBottomCollarRemovedDualEdges n ↔
      e.primalEdge ∉ rectangleDualBottomCollarInnerPrimalEdges n := by
  exact mem_rectangleDualConfiguration _ _ _ _ e

theorem rectangleDualBottomCollar_pair_mem_open_iff (n : ℕ)
    (e : RectangleDualEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1)) :
    rectangleDualCarrierPair (-(n:ℤ),-1) (2*n) (n+1) e ∈
      openEdges (rectangleDualBottomCollarOuterGraph n)
        (rectangleDualBottomCollarRemovedDualEdges n) ↔
      e.primalEdge ∉ rectangleDualBottomCollarInnerPrimalEdges n := by
  have hval : (rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) e).val =
      rectangleDualCarrierPair (-(n:ℤ),-1) (2*n) (n+1) e := rfl
  calc
    rectangleDualCarrierPair (-(n:ℤ),-1) (2*n) (n+1) e ∈
        openEdges (rectangleDualBottomCollarOuterGraph n)
          (rectangleDualBottomCollarRemovedDualEdges n) ↔
      (rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) e).val ∈
        openEdges (rectangleDualBottomCollarOuterGraph n)
          (rectangleDualBottomCollarRemovedDualEdges n) := by rw [hval]
    _ ↔ rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) e ∈
        rectangleDualBottomCollarRemovedDualEdges n :=
      coe_mem_openEdges_iff _ _ _
    _ ↔ e.primalEdge ∉ rectangleDualBottomCollarInnerPrimalEdges n :=
      rectangleDualBottomCollar_dualConfiguration_mem n e

def rectangleDualBottomCollarPrimalEdgeAsGraphEdge (n : ℕ)
    (e : rectanglePrimalEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1)) :
    (rectangleBottomCollarOuterGraph n).edgeSet :=
  ⟨e.val, e.property⟩

theorem rectangleDualBottomCollar_removedDual_mem_iff (n : ℕ)
    (e : RectangleDualEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1)) :
    rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) e ∈
      rectangleDualBottomCollarRemovedDualEdges n ↔
      rectangleDualBottomCollarPrimalEdgeAsGraphEdge n e.primalEdge ∈
        rectangleBottomCollarRemoved n := by
  rw [rectangleDualBottomCollar_dualConfiguration_mem]
  rw [rectangleBottomCollarRemoved, mem_subgraphRemovedEdges]
  rw [mem_rectangleDualBottomCollarInnerPrimalEdges]
  rfl

def rectangleDualBottomCollarRemainingGraph (n : ℕ) :
    SimpleGraph (rectangleDualBottomCollarOuterVertex n) :=
  edgeRestriction (rectangleDualBottomCollarOuterGraph n)
    (rectangleDualBottomCollarRemovedDualEdges n)

theorem rectangleDualBottomCollar_remainingGraph_eq_map_inner (n : ℕ) :
    rectangleDualBottomCollarRemainingGraph n =
      (rectangleDualBottomCollarInnerGraph n).map
        (rectangleDualBottomCollarVertexEmbedding n) := by
  ext u v
  rw [rectangleDualBottomCollarRemainingGraph, edgeRestriction,
    SimpleGraph.deleteEdges_adj, SimpleGraph.map_adj]
  constructor
  · rintro ⟨hout, hnot⟩
    obtain ⟨e, hp⟩ := (rectangleDualGraph_adj_iff _ _ _ _ _).mp hout
    have hclosed : rectangleDualCarrierPair _ _ _ e ∉
        openEdges (rectangleDualBottomCollarOuterGraph n)
          (rectangleDualBottomCollarRemovedDualEdges n) := by
      simpa [hp] using hnot
    have heinner : e.primalEdge ∈ rectangleDualBottomCollarInnerPrimalEdges n := by
      by_contra hbad
      exact hclosed ((rectangleDualBottomCollar_pair_mem_open_iff n e).mpr hbad)
    obtain ⟨d, hd⟩ :=
      (rectangleDualBottomCollarDualEdge_mem_iff n e).mp heinner
    have hpair := rectangleDualBottomCollarDualEdgeEmbedding_pair n d
    have hpair' : s(u,v) = Sym2.map (rectangleDualBottomCollarVertexEmbedding n)
        (rectangleDualCarrierPair _ _ _ d) := by
      calc
        s(u,v) = rectangleDualCarrierPair _ _ _ e := hp
        _ = rectangleDualCarrierPair _ _ _ (rectangleDualBottomCollarDualEdgeEmbedding n d) := by
          rw [hd]
        _ = Sym2.map (rectangleDualBottomCollarVertexEmbedding n)
            (rectangleDualCarrierPair _ _ _ d) := hpair
    have hpair'' : s(u,v) = s(
        rectangleDualBottomCollarVertexEmbedding n (rectangleDualEdgeSource _ _ _ d),
        rectangleDualBottomCollarVertexEmbedding n (rectangleDualEdgeTarget _ _ _ d)) := by
      simpa [rectangleDualCarrierPair] using hpair'
    rcases Sym2.eq_iff.mp hpair'' with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · exact ⟨rectangleDualEdgeSource _ _ _ d,
        rectangleDualEdgeTarget _ _ _ d,
        (rectangleDualGraph_adj_iff _ _ _ _ _).mpr ⟨d,rfl⟩,
        hu.symm,hv.symm⟩
    · exact ⟨rectangleDualEdgeTarget _ _ _ d,
        rectangleDualEdgeSource _ _ _ d,
        ((rectangleDualGraph_adj_iff _ _ _ _ _).mpr ⟨d,rfl⟩).symm,
        hu.symm,hv.symm⟩
  · rintro ⟨x,y,hinner,hxu,hyv⟩
    obtain ⟨d, hp⟩ := (rectangleDualGraph_adj_iff _ _ _ _ _).mp hinner
    have hpair : s(u,v) = rectangleDualCarrierPair _ _ _
        (rectangleDualBottomCollarDualEdgeEmbedding n d) := by
      calc
        s(u,v) = s(rectangleDualBottomCollarVertexEmbedding n x,
            rectangleDualBottomCollarVertexEmbedding n y) := by rw [hxu,hyv]
        _ = Sym2.map (rectangleDualBottomCollarVertexEmbedding n) (s(x,y)) := rfl
        _ = Sym2.map (rectangleDualBottomCollarVertexEmbedding n)
            (rectangleDualCarrierPair _ _ _ d) := congrArg _ hp
        _ = rectangleDualCarrierPair _ _ _
            (rectangleDualBottomCollarDualEdgeEmbedding n d) :=
              (rectangleDualBottomCollarDualEdgeEmbedding_pair n d).symm
    have hout : (rectangleDualBottomCollarOuterGraph n).Adj u v :=
      (rectangleDualGraph_adj_iff _ _ _ _ _).mpr
        ⟨rectangleDualBottomCollarDualEdgeEmbedding n d, hpair⟩
    refine ⟨hout, ?_⟩
    intro hopen
    have hopen' : rectangleDualCarrierPair _ _ _
        (rectangleDualBottomCollarDualEdgeEmbedding n d) ∈
          openEdges (rectangleDualBottomCollarOuterGraph n)
            (rectangleDualBottomCollarRemovedDualEdges n) := by
      simpa [hpair] using hopen
    have hnotinner := (rectangleDualBottomCollar_pair_mem_open_iff n
      (rectangleDualBottomCollarDualEdgeEmbedding n d)).mp hopen'
    exact hnotinner (rectangleDualBottomCollarDualEdgeEmbedding_mem n d)

def rectangleDualBottomCollarInnerThreeSides (n : ℕ) :
    Set (rectangleDualBottomCollarInnerVertex n) :=
  {v | v.val.1 = -(n:ℤ)-1 ∨ v.val.1 = n ∨ v.val.2 = n}

theorem rectangleDualBottomCollar_boundary_mem (n : ℕ)
    (v : rectangleDualBottomCollarInnerVertex n) :
    v.val ∈ rectangleDualBoundary (-(n:ℤ),-1) (2*n) (n+1) ↔
      v ∈ rectangleDualBottomCollarInnerThreeSides n := by
  have hprop := v.property
  change v.val ∈ latticeRectangle (-(n : ℤ)-1, -1) (2*n+1) (n+1) at hprop
  rw [mem_latticeRectangle] at hprop
  have hvcoord : -(n : ℤ)-1 ≤ v.val.1 ∧ v.val.1 ≤ n ∧
      -1 ≤ v.val.2 ∧ v.val.2 ≤ n := by
    rcases hprop with ⟨⟨hx1,hx2⟩,⟨hy1,hy2⟩⟩
    omega
  constructor
  · intro h
    have hmem := Finset.mem_filter.mp h
    have hnot : v.val ∉ rectangleDualInterior (-(n:ℤ),-1) (2*n) (n+1) := hmem.2
    simp only [rectangleDualBottomCollarInnerThreeSides, Set.mem_ofPred_eq]
    simp only [rectangleDualInterior, Finset.mem_filter, rectangleDualExpanded,
      mem_latticeRectangle] at hnot
    omega
  · intro h
    have hvouter : v.val ∈ rectangleDualExpanded (-(n:ℤ),-1) (2*n) (n+1) :=
      rectangleDualBottomCollarVertexSubset n v.property
    refine Finset.mem_filter.mpr ⟨hvouter, ?_⟩
    intro hi
    simp only [rectangleDualInterior, Finset.mem_filter, rectangleDualExpanded,
      mem_latticeRectangle] at hi
    simp only [rectangleDualBottomCollarInnerThreeSides, Set.mem_ofPred_eq] at h
    omega

@[simp] theorem rectangleDualBottomCollar_outerBoundaryCondition_pullback
    (n : ℕ) (u v : rectangleDualBottomCollarInnerVertex n) :
    (rectangleDualBoundaryCondition (-(n:ℤ),-1) (2*n) (n+1)).partition.r
      (rectangleDualBottomCollarVertexEmbedding n u)
      (rectangleDualBottomCollarVertexEmbedding n v) ↔
      u = v ∨ u ∈ rectangleDualBottomCollarInnerThreeSides n ∧
        v ∈ rectangleDualBottomCollarInnerThreeSides n := by
  rw [rectangleDualBoundaryCondition_rel]
  constructor
  · rintro (h | ⟨hu,hv⟩)
    · left
      apply (rectangleDualBottomCollarVertexEmbedding n).injective
      exact h
    · exact Or.inr ⟨(rectangleDualBottomCollar_boundary_mem n u).mp hu,
        (rectangleDualBottomCollar_boundary_mem n v).mp hv⟩
  · rintro (h | ⟨hu,hv⟩)
    · left
      exact congrArg (rectangleDualBottomCollarVertexEmbedding n) h
    · exact Or.inr ⟨(rectangleDualBottomCollar_boundary_mem n u).mpr hu,
        (rectangleDualBottomCollar_boundary_mem n v).mpr hv⟩

end
end PottsContinuity.FKC.FiniteFK
