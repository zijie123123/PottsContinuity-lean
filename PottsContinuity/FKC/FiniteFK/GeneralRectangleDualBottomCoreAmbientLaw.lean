-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleDualBottomCoreAmbientLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreLaw
public import PottsContinuity.FKC.FiniteFK.EmbeddedMarginalLaw
public import PottsContinuity.FKC.FiniteFK.Marginal

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

local instance generalDualCoreAmbientEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph (a.1 - 1, a.2) (w + 1) h).edgeSet := Classical.decEq _
local instance generalDualCoreAmbientCoreEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (generalRectangleDualBottomCoreGraph a w h).edgeSet := Classical.decEq _
local instance generalDualCoreAmbientMappedEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq ((generalRectangleDualBottomCoreGraph a w h).map
      (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding).edgeSet := Classical.decEq _

/-- The missing ambient primal-grid edges all have endpoints on the three
wired sides corresponding to the retained true-dual boundary. -/
theorem generalRectangleDualBottomCoreAmbient_removed_edges_wired
    (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex (a.1 - 1, a.2) (w + 1) h)
    (hadj : (rectangleGraph (a.1 - 1, a.2) (w + 1) h).Adj u v)
    (he : (⟨s(u, v), (rectangleGraph (a.1 - 1, a.2) (w + 1) h).mem_edgeSet.mpr hadj⟩ :
      (rectangleGraph (a.1 - 1, a.2) (w + 1) h).edgeSet) ∈
      subgraphRemovedEdges
        ((generalRectangleDualBottomCoreGraph a w h).map
          (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding)
        (rectangleGraph (a.1 - 1, a.2) (w + 1) h)) :
    (BoundaryCondition.wired {x : RectangleVertex (a.1 - 1, a.2) (w + 1) h |
      x.1.1 = a.1 - 1 ∨ x.1.1 = a.1 + (w : ℤ) ∨ x.1.2 = a.2 + (h : ℤ)}).partition.r u v := by
  classical
  let e := generalRectangleDualBottomCoreVertexEquiv a w h
  let f := e.toEmbedding
  let G := generalRectangleDualBottomCoreGraph a w h
  let H := rectangleGraph (a.1 - 1, a.2) (w + 1) h
  let x : generalRectangleDualBottomCoreVertex a w h := e.symm u
  let y : generalRectangleDualBottomCoreVertex a w h := e.symm v
  have hnot : ¬ G.Adj x y := by
    intro hG
    have hmap : (G.map f).Adj (f x) (f y) :=
      (SimpleGraph.map_adj f G (f x) (f y)).2 ⟨x, y, hG, rfl, rfl⟩
    have hmapMem : s(f x, f y) ∈ (G.map f).edgeSet := (G.map f).mem_edgeSet.mpr hmap
    have hremoved := (mem_subgraphRemovedEdges (G := G.map f) (H := H)
      (⟨s(u, v), H.mem_edgeSet.mpr hadj⟩ : H.edgeSet)).mp he
    have hfx : f x = u := by simp [f, x, e]
    have hfy : f y = v := by simp [f, y, e]
    rw [hfx, hfy] at hmapMem
    exact hremoved hmapMem
  have hEx : e x = u := Equiv.apply_symm_apply e u
  have hEy : e y = v := Equiv.apply_symm_apply e v
  have hadj' : H.Adj (e x) (e y) := by rw [hEx, hEy]; exact hadj
  have hends := generalRectangleDualBottomCore_extraEdge_endpoints_wired
    a w h x y hadj' hnot
  have hcoordx : x.1.1 = u.1 := by
    change (e x).1 = u.1
    exact congrArg Subtype.val hEx
  have hcoordy : y.1.1 = v.1 := by
    change (e y).1 = v.1
    exact congrArg Subtype.val hEy
  rw [BoundaryCondition.wired_rel]
  exact Or.inr ⟨by
      simpa [hcoordx] using hends.1,
    by
      simpa [hcoordy] using hends.2⟩

/-- The wired boundary of the ordinary rectangle pulls back under the literal
core equivalence to the three sides of the retained true-dual core. -/
theorem generalRectangleDualBottomCoreAmbient_boundary_pullback
    (a : LatticeVertex) (w h : ℕ) :
    (isolatedExtensionPullbackBoundary
      (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding
      (BoundaryCondition.wired {x : RectangleVertex (a.1 - 1, a.2) (w + 1) h |
        x.1.1 = a.1 - 1 ∨ x.1.1 = a.1 + (w : ℤ) ∨ x.1.2 = a.2 + (h : ℤ)})).partition =
      (BoundaryCondition.wired
        {u : generalRectangleDualBottomCoreVertex a w h |
          (generalRectangleDualBottomCoreInclusion a w h u) ∈
            generalRectangleDualBottomCollarInnerThreeSides a w h}).partition := by
  apply Setoid.ext
  intro u v
  change (Setoid.comap (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding
      (BoundaryCondition.wired _).partition).r u v ↔ _
  rw [Setoid.comap_rel, BoundaryCondition.wired_rel, BoundaryCondition.wired_rel]
  simp only [generalRectangleDualBottomCoreVertexEquiv,
    generalRectangleDualBottomCoreInclusion,
    generalRectangleDualBottomCollarInnerThreeSides]
  constructor
  · rintro (heq | ⟨hu, hv⟩)
    · exact Or.inl ((generalRectangleDualBottomCoreVertexEquiv a w h).injective heq)
    · exact Or.inr ⟨hu, hv⟩
  · rintro (hEq | ⟨hu, hv⟩)
    · exact Or.inl (congrArg (generalRectangleDualBottomCoreVertexEquiv a w h) hEq)
    · exact Or.inr ⟨hu, hv⟩

/-- The ordinary rectangle FK law, wired on the left, right, and top, restricts
exactly to the FK law on the retained true-dual core. -/
theorem generalRectangleDualBottomCoreAmbient_law_restrict
    (a : LatticeVertex) (w h : ℕ) (q : ClusterWeight) :
    (law (rectangleGraph (a.1 - 1, a.2) (w + 1) h) q
      (BoundaryCondition.wired {x : RectangleVertex (a.1 - 1, a.2) (w + 1) h |
        x.1.1 = a.1 - 1 ∨ x.1.1 = a.1 + (w : ℤ) ∨ x.1.2 = a.2 + (h : ℤ)})).map
        (embeddedConfigurationRestriction
          (generalRectangleDualBottomCoreGraph a w h)
          (rectangleGraph (a.1 - 1, a.2) (w + 1) h)
          (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding
          (by
            intro u v huv
            rcases (SimpleGraph.map_adj _ _ _ _).mp huv with
              ⟨u₀, v₀, hG, rfl, rfl⟩
            exact generalRectangleDualBottomCoreGraph_le_rectangle a w h hG)) =
      law (generalRectangleDualBottomCoreGraph a w h) q
        (BoundaryCondition.wired
          {u : generalRectangleDualBottomCoreVertex a w h |
            (generalRectangleDualBottomCoreInclusion a w h u) ∈
              generalRectangleDualBottomCollarInnerThreeSides a w h}) := by
  classical
  let G := generalRectangleDualBottomCoreGraph a w h
  let H := rectangleGraph (a.1 - 1, a.2) (w + 1) h
  let f := (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding
  let ξ := BoundaryCondition.wired {x : RectangleVertex (a.1 - 1, a.2) (w + 1) h |
    x.1.1 = a.1 - 1 ∨ x.1.1 = a.1 + (w : ℤ) ∨ x.1.2 = a.2 + (h : ℤ)}
  let η := BoundaryCondition.wired
    {u : generalRectangleDualBottomCoreVertex a w h |
      (generalRectangleDualBottomCoreInclusion a w h u) ∈
        generalRectangleDualBottomCollarInnerThreeSides a w h}
  have hGH : G.map f ≤ H := by
    intro x y hxy
    rcases (SimpleGraph.map_adj f G _ _).mp hxy with ⟨u, v, huv, rfl, rfl⟩
    exact generalRectangleDualBottomCoreGraph_le_rectangle a w h huv
  have hξ : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition = η.partition := by
    intro K
    have hfreeze : (frozenBoundary ξ K.val).partition = ξ.partition := by
      apply Setoid.ext
      intro x y
      change (componentSetoid H ξ K.val).r x y ↔ ξ.partition.r x y
      constructor
      · intro hxy
        exact (componentSetoid_le H ξ K.val ξ.partition
          (by
            apply reachableSetoid_le_of_adj (openGraph H K.val) ξ.partition
            intro z z' hz
            rw [openGraph_adj] at hz
            rcases hz with ⟨e₀, heK, heval⟩
            have hmem : s(z, z') ∈ H.edgeSet := by
              rw [← heval]
              exact e₀.property
            have hadj : H.Adj z z' := H.mem_edgeSet.mp hmem
            have heR₀ : e₀ ∈ subgraphRemovedEdges (G.map f) H := K.property heK
            have heR : (⟨s(z, z'), hmem⟩ : H.edgeSet) ∈
                subgraphRemovedEdges (G.map f) H := by
              have heq : (⟨s(z, z'), hmem⟩ : H.edgeSet) = e₀ := by
                apply Subtype.ext
                exact heval.symm
              simpa [heq] using heR₀
            exact generalRectangleDualBottomCoreAmbient_removed_edges_wired
              a w h z z' hadj heR)
          le_rfl hxy)
      · intro hxy
        exact boundary_component H ξ K.val hxy
    change Setoid.comap f (frozenBoundary ξ K.val).partition = η.partition
    rw [hfreeze]
    exact generalRectangleDualBottomCoreAmbient_boundary_pullback a w h
  exact law_embeddedConfigurationRestriction_eq_of_frozen_partition
    G H f hGH q ξ η hξ

end
end PottsContinuity.FKC.FiniteFK
