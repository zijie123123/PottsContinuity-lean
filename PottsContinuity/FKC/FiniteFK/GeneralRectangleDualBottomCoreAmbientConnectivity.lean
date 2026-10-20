-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleDualBottomCoreAmbientConnectivity.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreConnectivity
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreAmbientLaw

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

local instance ambientConnVertexDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (RectangleVertex (a.1 - 1, a.2) (w + 1) h) := Classical.decEq _
local instance ambientConnEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph (a.1 - 1, a.2) (w + 1) h).edgeSet := Classical.decEq _
local instance ambientConnCoreEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (generalRectangleDualBottomCoreGraph a w h).edgeSet := Classical.decEq _
local instance ambientConnMappedEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq ((generalRectangleDualBottomCoreGraph a w h).map
      (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding).edgeSet := Classical.decEq _

 theorem ambientConn_map_le (a : LatticeVertex) (w h : ℕ) :
    (generalRectangleDualBottomCoreGraph a w h).map
      (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding ≤
      rectangleGraph (a.1 - 1, a.2) (w + 1) h := by
  intro x y hxy
  obtain ⟨u, v, huv, rfl, rfl⟩ :=
    (SimpleGraph.map_adj _ _ _ _).mp hxy
  exact generalRectangleDualBottomCoreGraph_le_rectangle a w h huv

def generalRectangleDualBottomCoreConfigurationRestrictionAmbient (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph (a.1 - 1, a.2) (w + 1) h)) :
    Configuration (generalRectangleDualBottomCoreGraph a w h) :=
  embeddedConfigurationRestriction (generalRectangleDualBottomCoreGraph a w h)
    (rectangleGraph (a.1 - 1, a.2) (w + 1) h)
    (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding
    (ambientConn_map_le a w h) A

def generalRectangleDualBottomCoreAmbientBoundary (a : LatticeVertex) (w h : ℕ) :
    Set (RectangleVertex (a.1 - 1, a.2) (w + 1) h) :=
  {x | x.1.1 = a.1 - 1 ∨ x.1.1 = a.1 + (w : ℤ) ∨ x.1.2 = a.2 + (h : ℤ)}

private theorem ambientConn_countP_pos_of_mem
    {V : Type*} [DecidableEq V] {l : List V} {z : V} (hz : z ∈ l) :
    0 < l.countP (fun t => decide (t = z)) := by
  rw [List.countP_eq_length_filter]
  have hz' : z ∈ List.filter (fun t => decide (t = z)) l :=
    List.mem_filter.mpr ⟨hz, by simp⟩
  exact List.length_pos_of_mem hz'

private theorem ambientConn_firstBoundaryPrefix
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {B : Set V} {x y : V}
    (p : G.Walk x y) (hy : y ∈ B) :
    ∃ z, z ∈ B ∧ ∃ q : G.Walk x z,
      (∀ t ∈ q.support, t ∈ B → t = z) ∧
      q.support.countP (fun t => decide (t = z)) = 1 := by
  classical
  induction p with
  | nil =>
      exact ⟨_, hy, SimpleGraph.Walk.nil, by simp, by simp⟩
  | @cons x y z hadj tail ih =>
      by_cases hx : x ∈ B
      · exact ⟨x, hx, SimpleGraph.Walk.nil, by simp, by simp⟩
      · obtain ⟨t, ht, q, huniq, hcount⟩ := ih hy
        refine ⟨t, ht, SimpleGraph.Walk.cons hadj q, ?_, ?_⟩
        · intro s hs hsB
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact (hx hsB).elim
          · exact huniq s hs hsB
        · simp only [SimpleGraph.Walk.support_cons, List.countP_cons]
          have hxt : x ≠ t := by
            intro hEq
            subst t
            exact hx ht
          simp [hxt, hcount]

private theorem ambientConn_restriction_open_adj
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph (a.1 - 1, a.2) (w + 1) h))
    {x y : RectangleVertex (a.1 - 1, a.2) (w + 1) h}
    (hxy : (openGraph (rectangleGraph (a.1 - 1, a.2) (w + 1) h) A).Adj x y)
    (hnotBoth : ¬ (x ∈ generalRectangleDualBottomCoreAmbientBoundary a w h ∧ y ∈ generalRectangleDualBottomCoreAmbientBoundary a w h)) :
    (openGraph (generalRectangleDualBottomCoreGraph a w h)
      (generalRectangleDualBottomCoreConfigurationRestrictionAmbient a w h A)).Adj
      ((generalRectangleDualBottomCoreVertexEquiv a w h).symm x)
      ((generalRectangleDualBottomCoreVertexEquiv a w h).symm y) := by
  classical
  let G := generalRectangleDualBottomCoreGraph a w h
  let H := rectangleGraph (a.1 - 1, a.2) (w + 1) h
  let e := generalRectangleDualBottomCoreVertexEquiv a w h
  let f := e.toEmbedding
  let M := G.map f
  let R := generalRectangleDualBottomCoreConfigurationRestrictionAmbient a w h A
  have hadj : H.Adj x y := openGraph_le H A hxy
  rw [openGraph_adj] at hxy
  rcases hxy with ⟨eH, heA, heval⟩
  have heH : eH ∈ subgraphRemovedEdges M H ∨ eH.val ∈ M.edgeSet := by
    by_cases hm : eH.val ∈ M.edgeSet
    · exact Or.inr hm
    · exact Or.inl ((mem_subgraphRemovedEdges (G := M) (H := H) eH).2 hm)
  have hmapAdj : M.Adj x y := by
    rcases heH with hrem | hmap
    · have heq : (⟨s(x, y), H.mem_edgeSet.mpr hadj⟩ : H.edgeSet) = eH := by
        apply Subtype.ext
        exact heval.symm
      have hrem' : (⟨s(x, y), H.mem_edgeSet.mpr hadj⟩ : H.edgeSet) ∈
          subgraphRemovedEdges M H := by simpa [heq] using hrem
      have hedges := generalRectangleDualBottomCoreAmbient_removed_edges_wired
        a w h x y hadj hrem'
      rcases hedges with hdiag | hSides
      · exact (hadj.ne hdiag).elim
      · exact (hnotBoth (by simpa [generalRectangleDualBottomCoreAmbientBoundary] using hSides)).elim
    · have hmap' : s(x, y) ∈ M.edgeSet := by rw [← heval]; exact hmap
      exact M.mem_edgeSet.mp hmap'
  obtain ⟨u₀, v₀, hG, hfu, hfv⟩ := (SimpleGraph.map_adj f G x y).mp hmapAdj
  have hu₀ : u₀ = e.symm x := by
    apply e.injective
    simpa [f] using hfu
  have hv₀ : v₀ = e.symm y := by
    apply e.injective
    simpa [f] using hfv
  subst u₀
  subst v₀
  let eG : G.edgeSet := ⟨s(e.symm x, e.symm y), G.mem_edgeSet.mpr hG⟩
  have hstate : eG ∈ R := by
    change eG ∈ embeddedConfigurationRestriction G H f
      (ambientConn_map_le a w h) A
    rw [mem_embeddedConfigurationRestriction]
    have hmap : embeddedEdgeEmbedding G H f
        (ambientConn_map_le a w h) eG = eH := by
      apply Subtype.ext
      rw [embeddedEdgeEmbedding_coe, Function.Embedding.sym2Map_apply, Sym2.map_mk]
      simp [f, e, heval]
    exact hmap ▸ heA
  rw [openGraph_adj]
  exact ⟨eG, hstate, rfl⟩

private theorem ambientConn_lift_core_open_adj
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph (a.1 - 1, a.2) (w + 1) h))
    {u v : generalRectangleDualBottomCoreVertex a w h}
    (huv : (openGraph (generalRectangleDualBottomCoreGraph a w h)
      (generalRectangleDualBottomCoreConfigurationRestrictionAmbient a w h A)).Adj u v) :
    (openGraph (rectangleGraph (a.1 - 1, a.2) (w + 1) h) A).Adj
      (generalRectangleDualBottomCoreVertexEquiv a w h u)
      (generalRectangleDualBottomCoreVertexEquiv a w h v) := by
  classical
  let G := generalRectangleDualBottomCoreGraph a w h
  let H := rectangleGraph (a.1 - 1, a.2) (w + 1) h
  let e := generalRectangleDualBottomCoreVertexEquiv a w h
  let f := e.toEmbedding
  rw [openGraph_adj] at huv ⊢
  rcases huv with ⟨eG, heR, heval⟩
  refine ⟨embeddedEdgeEmbedding G H f
      (ambientConn_map_le a w h) eG,
    (mem_embeddedConfigurationRestriction G H f
      (ambientConn_map_le a w h) A eG).mp heR,
    ?_⟩
  rw [embeddedEdgeEmbedding_coe]
  change Sym2.map f eG.val = s(f u, f v)
  rw [heval, Sym2.map_mk]

private theorem ambientConn_lift_prefix
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph (a.1 - 1, a.2) (w + 1) h))
    {x z : RectangleVertex (a.1 - 1, a.2) (w + 1) h}
    (q : (openGraph (rectangleGraph (a.1 - 1, a.2) (w + 1) h) A).Walk x z)
    (hz : z ∈ generalRectangleDualBottomCoreAmbientBoundary a w h)
    (huniq : ∀ t ∈ q.support, t ∈ generalRectangleDualBottomCoreAmbientBoundary a w h → t = z)
    (hcount : q.support.countP (fun t => decide (t = z)) = 1) :
    Nonempty ((openGraph (generalRectangleDualBottomCoreGraph a w h)
      (generalRectangleDualBottomCoreConfigurationRestrictionAmbient a w h A)).Walk
      ((generalRectangleDualBottomCoreVertexEquiv a w h).symm x)
      ((generalRectangleDualBottomCoreVertexEquiv a w h).symm z)) := by
  induction q with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons x y z hadj tail ih =>
      have hnotBoth : ¬ (x ∈ generalRectangleDualBottomCoreAmbientBoundary a w h ∧ y ∈ generalRectangleDualBottomCoreAmbientBoundary a w h) := by
        intro hxy
        have hxz := huniq x (by simp) hxy.1
        have hyz := huniq y (by simp [SimpleGraph.Walk.support_cons]) hxy.2
        subst x
        subst y
        have htailMem : z ∈ tail.support := tail.start_mem_support
        have hcountTail : 0 < tail.support.countP (fun t => decide (t = z)) :=
          ambientConn_countP_pos_of_mem htailMem
        have hcountFull := hcount
        simp only [SimpleGraph.Walk.support_cons, List.countP_cons] at hcountFull
        simp at hcountFull
        exact hcountFull z.1.1 z.1.2 z.2 htailMem rfl
      have htailUniq : ∀ t ∈ tail.support, t ∈ generalRectangleDualBottomCoreAmbientBoundary a w h → t = z := by
        intro t ht htB
        exact huniq t (by simp [SimpleGraph.Walk.support_cons, ht]) htB
      have htailMem : z ∈ tail.support := tail.end_mem_support
      have htailPos : 0 < tail.support.countP (fun t => decide (t = z)) :=
        ambientConn_countP_pos_of_mem htailMem
      have hxz : x ≠ z := by
        intro hxz
        subst x
        simp only [SimpleGraph.Walk.support_cons, List.countP_cons] at hcount
        simp at hcount
        exact hcount z.1.1 z.1.2 z.2 htailMem rfl
      have htailCount : tail.support.countP (fun t => decide (t = z)) = 1 := by
        simpa [SimpleGraph.Walk.support_cons, List.countP_cons, hxz] using hcount
      rcases ih hz htailUniq htailCount with ⟨tailCore⟩
      have hstep := ambientConn_restriction_open_adj a w h A hadj hnotBoth
      exact ⟨SimpleGraph.Walk.cons hstep tailCore⟩

private theorem ambientConn_lift_core_walk
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph (a.1 - 1, a.2) (w + 1) h))
    {u v : generalRectangleDualBottomCoreVertex a w h}
    (p : (openGraph (generalRectangleDualBottomCoreGraph a w h)
      (generalRectangleDualBottomCoreConfigurationRestrictionAmbient a w h A)).Walk u v) :
    Nonempty ((openGraph (rectangleGraph (a.1 - 1, a.2) (w + 1) h) A).Walk
      (generalRectangleDualBottomCoreVertexEquiv a w h u)
      (generalRectangleDualBottomCoreVertexEquiv a w h v)) := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons u v z hadj tail ih =>
      rcases ih with ⟨tailOuter⟩
      exact ⟨SimpleGraph.Walk.cons
        (ambientConn_lift_core_open_adj a w h A hadj) tailOuter⟩

/-- For every configuration of the ordinary rectangle, connection to its
three wired sides is exactly connection in the restricted true-dual core. -/
theorem generalRectangleDualBottomCoreAmbient_connected_to_boundary_iff
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph (a.1 - 1, a.2) (w + 1) h))
    (x : RectangleVertex (a.1 - 1, a.2) (w + 1) h) :
    (∃ z : RectangleVertex (a.1 - 1, a.2) (w + 1) h,
      z ∈ generalRectangleDualBottomCoreAmbientBoundary a w h ∧
      ActualConnected (rectangleGraph (a.1 - 1, a.2) (w + 1) h) A x z) ↔
    (∃ u : generalRectangleDualBottomCoreVertex a w h,
      generalRectangleDualBottomCoreVertexEquiv a w h u ∈ generalRectangleDualBottomCoreAmbientBoundary a w h ∧
      ActualConnected (generalRectangleDualBottomCoreGraph a w h)
        (generalRectangleDualBottomCoreConfigurationRestrictionAmbient a w h A)
        ((generalRectangleDualBottomCoreVertexEquiv a w h).symm x) u) := by
  constructor
  · rintro ⟨z, hz, hconn⟩
    rcases (actualConnected_iff_walk _ _ _ _).mp hconn with ⟨p⟩
    obtain ⟨z₀, hz₀, q, huniq, hcount⟩ := ambientConn_firstBoundaryPrefix p hz
    have hcorewalk := ambientConn_lift_prefix a w h A q hz₀ huniq hcount
    refine ⟨(generalRectangleDualBottomCoreVertexEquiv a w h).symm z₀, ?_, ?_⟩
    · simpa using hz₀
    · exact (actualConnected_iff_walk _ _ _ _).mpr hcorewalk
  · rintro ⟨u, hu, hconn⟩
    rcases (actualConnected_iff_walk _ _ _ _).mp hconn with ⟨p⟩
    have houter := ambientConn_lift_core_walk a w h A p
    have hx : (generalRectangleDualBottomCoreVertexEquiv a w h)
        ((generalRectangleDualBottomCoreVertexEquiv a w h).symm x) = x :=
      (generalRectangleDualBottomCoreVertexEquiv a w h).apply_symm_apply x
    have hconn' : ActualConnected (rectangleGraph (a.1 - 1, a.2) (w + 1) h) A x
        (generalRectangleDualBottomCoreVertexEquiv a w h u) := by
      apply (actualConnected_iff_walk _ _ _ _).mpr
      simpa [hx] using houter
    exact ⟨generalRectangleDualBottomCoreVertexEquiv a w h u, hu, hconn'⟩

end
end PottsContinuity.FKC.FiniteFK
