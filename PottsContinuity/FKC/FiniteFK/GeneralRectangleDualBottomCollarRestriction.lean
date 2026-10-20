-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleDualBottomCollarRestriction.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCollar
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleBottomCollar
public import PottsContinuity.FKC.FiniteFK.RectangleDualConfiguration
public import PottsContinuity.FKC.FiniteFK.EdgeRestriction

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

local instance generalRectangleDualBottomCollarRestrictionOuterEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (generalRectangleDualBottomCollarOuterGraph a w h).edgeSet :=
  Classical.decEq _

/-- Outer primal edges whose underlying unordered pair is an image edge of the
inner rectangle. This is the literal edge carrier used by the collar removal. -/
def generalRectangleDualBottomCollarInnerPrimalEdges (a : LatticeVertex) (w h : ℕ) :
    Finset (rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 1)) := by
  classical
  exact Finset.univ.filter fun e => e.val ∈
    ((rectangleGraph a w h).map
      (rectangleArbitraryBottomCollarEmbedding a w h)).edgeSet

@[simp] theorem mem_generalRectangleDualBottomCollarInnerPrimalEdges
    (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 1)) :
    e ∈ generalRectangleDualBottomCollarInnerPrimalEdges a w h ↔
      e.val ∈ ((rectangleGraph a w h).map
        (rectangleArbitraryBottomCollarEmbedding a w h)).edgeSet := by
  simp [generalRectangleDualBottomCollarInnerPrimalEdges]

theorem generalRectangleDualBottomCollarInnerPrimalEdges_mem_iff
    (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 1)) :
    e ∈ generalRectangleDualBottomCollarInnerPrimalEdges a w h ↔
      ∃ f : rectanglePrimalEdgeCarrier a w h,
        e.val = (rectangleArbitraryBottomCollarEmbedding a w h).sym2Map f.val := by
  classical
  rw [mem_generalRectangleDualBottomCollarInnerPrimalEdges]
  constructor
  · intro he
    rw [SimpleGraph.edgeSet_map, Set.mem_image] at he
    rcases he with ⟨f, hf, hfe⟩
    exact ⟨⟨f, hf⟩, hfe.symm⟩
  · rintro ⟨f, he⟩
    rw [SimpleGraph.edgeSet_map, Set.mem_image]
    exact ⟨f.val, f.property, he.symm⟩

theorem generalRectangleDualBottomCollarInnerPrimalEdges_mem_iff_embedding
    (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 1)) :
    e ∈ generalRectangleDualBottomCollarInnerPrimalEdges a w h ↔
      ∃ f : rectanglePrimalEdgeCarrier a w h,
        generalRectangleDualBottomCollar_primalEdgeEmbedding a w h f = e := by
  rw [generalRectangleDualBottomCollarInnerPrimalEdges_mem_iff]
  constructor
  · rintro ⟨f, he⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    exact he.symm
  · rintro ⟨f, he⟩
    refine ⟨f, ?_⟩
    exact (congrArg Subtype.val he).symm

theorem rectanglePrimalDualEdgeEquiv_apply_primalEdge_general
    {a : LatticeVertex} {w h : ℕ}
    (e : RectangleDualEdgeCarrier a w h) :
    rectanglePrimalDualEdgeEquiv a w h e.primalEdge = e := by
  cases e with
  | mk p cb hcb => subst cb; rfl

theorem generalRectangleDualBottomCollar_dualEdgeEmbedding_mem
    (a : LatticeVertex) (w h : ℕ) (e : RectangleDualEdgeCarrier a w h) :
    (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h e).primalEdge ∈
      generalRectangleDualBottomCollarInnerPrimalEdges a w h := by
  rw [generalRectangleDualBottomCollar_dualEdgeEmbedding_primalEdge]
  exact (generalRectangleDualBottomCollarInnerPrimalEdges_mem_iff_embedding a w h _).mpr
    ⟨e.primalEdge, rfl⟩

theorem generalRectangleDualBottomCollar_dualEdge_mem_iff
    (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier (a.1, a.2 - 1) w (h + 1)) :
    e.primalEdge ∈ generalRectangleDualBottomCollarInnerPrimalEdges a w h ↔
      ∃ f : RectangleDualEdgeCarrier a w h,
        generalRectangleDualBottomCollar_dualEdgeEmbedding a w h f = e := by
  constructor
  · intro he
    rcases (generalRectangleDualBottomCollarInnerPrimalEdges_mem_iff_embedding a w h e.primalEdge).mp he
      with ⟨f, hf⟩
    let dI := (rectanglePrimalDualEdgeEquiv a w h) f
    refine ⟨dI, ?_⟩
    calc
      generalRectangleDualBottomCollar_dualEdgeEmbedding a w h dI =
          rectanglePrimalDualEdgeEquiv (a.1, a.2 - 1) w (h + 1)
            (generalRectangleDualBottomCollar_primalEdgeEmbedding a w h f) := rfl
      _ = rectanglePrimalDualEdgeEquiv (a.1, a.2 - 1) w (h + 1) e.primalEdge :=
        congrArg (rectanglePrimalDualEdgeEquiv (a.1, a.2 - 1) w (h + 1)) hf
      _ = e := rectanglePrimalDualEdgeEquiv_apply_primalEdge_general e
  · rintro ⟨f, rfl⟩
    exact generalRectangleDualBottomCollar_dualEdgeEmbedding_mem a w h f

/-- The literal dual configuration whose open edges are the complement of the
inner original-primal-edge range. -/
def generalRectangleDualBottomCollarRemovedDualEdges (a : LatticeVertex) (w h : ℕ) :
    Configuration (generalRectangleDualBottomCollarOuterGraph a w h) :=
  rectangleDualConfiguration (a.1, a.2 - 1) w (h + 1)
    (generalRectangleDualBottomCollarInnerPrimalEdges a w h)

theorem generalRectangleDualBottomCollar_dualConfiguration_mem
    (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier (a.1, a.2 - 1) w (h + 1)) :
    rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1) e ∈
      generalRectangleDualBottomCollarRemovedDualEdges a w h ↔
      e.primalEdge ∉ generalRectangleDualBottomCollarInnerPrimalEdges a w h := by
  exact mem_rectangleDualConfiguration _ _ _ _ e

theorem generalRectangleDualBottomCollar_pair_mem_open_iff
    (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier (a.1, a.2 - 1) w (h + 1)) :
    rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 1) e ∈
      openEdges (generalRectangleDualBottomCollarOuterGraph a w h)
        (generalRectangleDualBottomCollarRemovedDualEdges a w h) ↔
      e.primalEdge ∉ generalRectangleDualBottomCollarInnerPrimalEdges a w h := by
  have hval : (rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1) e).val =
      rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 1) e := rfl
  calc
    rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 1) e ∈
        openEdges (generalRectangleDualBottomCollarOuterGraph a w h)
          (generalRectangleDualBottomCollarRemovedDualEdges a w h) ↔
      (rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1) e).val ∈
        openEdges (generalRectangleDualBottomCollarOuterGraph a w h)
          (generalRectangleDualBottomCollarRemovedDualEdges a w h) := by rw [hval]
    _ ↔ rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1) e ∈
        generalRectangleDualBottomCollarRemovedDualEdges a w h := coe_mem_openEdges_iff _ _ _
    _ ↔ e.primalEdge ∉ generalRectangleDualBottomCollarInnerPrimalEdges a w h :=
      generalRectangleDualBottomCollar_dualConfiguration_mem a w h e

def generalRectangleDualBottomCollarPrimalEdgeAsGraphEdge (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 1)) :
    (rectangleArbitraryBottomCollarOuterGraph a w h).edgeSet :=
  ⟨e.val, e.property⟩

theorem generalRectangleDualBottomCollar_removedDual_mem_iff
    (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier (a.1, a.2 - 1) w (h + 1)) :
    rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1) e ∈
      generalRectangleDualBottomCollarRemovedDualEdges a w h ↔
      generalRectangleDualBottomCollarPrimalEdgeAsGraphEdge a w h e.primalEdge ∈
        rectangleArbitraryBottomCollarRemoved a w h := by
  rw [generalRectangleDualBottomCollar_dualConfiguration_mem]
  rw [rectangleArbitraryBottomCollarRemoved, mem_subgraphRemovedEdges]
  rw [mem_generalRectangleDualBottomCollarInnerPrimalEdges]
  rfl

def generalRectangleDualBottomCollarRemainingGraph (a : LatticeVertex) (w h : ℕ) :
    SimpleGraph (generalRectangleDualBottomCollarOuterVertex a w h) :=
  edgeRestriction (generalRectangleDualBottomCollarOuterGraph a w h)
    (generalRectangleDualBottomCollarRemovedDualEdges a w h)

/-- Removing the dual edges corresponding to the removed primal collar leaves
exactly the mapped inner dual graph, including all its vertices. -/
theorem generalRectangleDualBottomCollar_remainingGraph_eq_map_inner
    (a : LatticeVertex) (w h : ℕ) :
    generalRectangleDualBottomCollarRemainingGraph a w h =
      (generalRectangleDualBottomCollarInnerGraph a w h).map
        (generalRectangleDualBottomCollar_vertexEmbedding a w h) := by
  ext u v
  rw [generalRectangleDualBottomCollarRemainingGraph, edgeRestriction,
    SimpleGraph.deleteEdges_adj, SimpleGraph.map_adj]
  constructor
  · rintro ⟨hout, hnot⟩
    obtain ⟨e, hp⟩ := (rectangleDualGraph_adj_iff _ _ _ _ _).mp hout
    have hclosed : rectangleDualCarrierPair _ _ _ e ∉
        openEdges (generalRectangleDualBottomCollarOuterGraph a w h)
          (generalRectangleDualBottomCollarRemovedDualEdges a w h) := by
      simpa [hp] using hnot
    have heinner : e.primalEdge ∈ generalRectangleDualBottomCollarInnerPrimalEdges a w h := by
      by_contra hbad
      exact hclosed ((generalRectangleDualBottomCollar_pair_mem_open_iff a w h e).mpr hbad)
    obtain ⟨d, hd⟩ := (generalRectangleDualBottomCollar_dualEdge_mem_iff a w h e).mp heinner
    have hpair := generalRectangleDualBottomCollar_dualEdgeEmbedding_pair a w h d
    have hpair' : s(u, v) = Sym2.map (generalRectangleDualBottomCollar_vertexEmbedding a w h)
        (rectangleDualCarrierPair a w h d) := by
      calc
        s(u, v) = rectangleDualCarrierPair _ _ _ e := hp
        _ = rectangleDualCarrierPair _ _ _
            (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h d) := by rw [hd]
        _ = Sym2.map (generalRectangleDualBottomCollar_vertexEmbedding a w h)
            (rectangleDualCarrierPair a w h d) := hpair
    have hpair'' : s(u, v) = s(
        generalRectangleDualBottomCollar_vertexEmbedding a w h (rectangleDualEdgeSource a w h d),
        generalRectangleDualBottomCollar_vertexEmbedding a w h (rectangleDualEdgeTarget a w h d)) := by
      simpa [rectangleDualCarrierPair] using hpair'
    rcases Sym2.eq_iff.mp hpair'' with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact ⟨rectangleDualEdgeSource a w h d, rectangleDualEdgeTarget a w h d,
        (rectangleDualGraph_adj_iff _ _ _ _ _).mpr ⟨d, rfl⟩, hu.symm, hv.symm⟩
    · exact ⟨rectangleDualEdgeTarget a w h d, rectangleDualEdgeSource a w h d,
        ((rectangleDualGraph_adj_iff _ _ _ _ _).mpr ⟨d, rfl⟩).symm, hu.symm, hv.symm⟩
  · rintro ⟨x, y, hinner, hxu, hyv⟩
    obtain ⟨d, hp⟩ := (rectangleDualGraph_adj_iff _ _ _ _ _).mp hinner
    have hpair : s(u, v) = rectangleDualCarrierPair _ _ _
        (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h d) := by
      calc
        s(u, v) = s(generalRectangleDualBottomCollar_vertexEmbedding a w h x,
            generalRectangleDualBottomCollar_vertexEmbedding a w h y) := by rw [hxu, hyv]
        _ = Sym2.map (generalRectangleDualBottomCollar_vertexEmbedding a w h) (s(x, y)) := rfl
        _ = Sym2.map (generalRectangleDualBottomCollar_vertexEmbedding a w h)
            (rectangleDualCarrierPair a w h d) := congrArg _ hp
        _ = rectangleDualCarrierPair _ _ _
            (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h d) :=
              (generalRectangleDualBottomCollar_dualEdgeEmbedding_pair a w h d).symm
    have hout : (generalRectangleDualBottomCollarOuterGraph a w h).Adj u v :=
      (rectangleDualGraph_adj_iff _ _ _ _ _).mpr
        ⟨generalRectangleDualBottomCollar_dualEdgeEmbedding a w h d, hpair⟩
    refine ⟨hout, ?_⟩
    intro hopen
    have hopen' : rectangleDualCarrierPair _ _ _
        (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h d) ∈
          openEdges (generalRectangleDualBottomCollarOuterGraph a w h)
            (generalRectangleDualBottomCollarRemovedDualEdges a w h) := by
      simpa [hpair] using hopen
    have hnotinner := (generalRectangleDualBottomCollar_pair_mem_open_iff a w h
      (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h d)).mp hopen'
    exact hnotinner (generalRectangleDualBottomCollar_dualEdgeEmbedding_mem a w h d)

end
end PottsContinuity.FKC.FiniteFK
