-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleBottomCollar.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleBottomCollar

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

abbrev rectangleArbitraryBottomCollarInnerGraph (a : LatticeVertex) (w h : ℕ) :=
  rectangleGraph a w h

abbrev rectangleArbitraryBottomCollarOuterGraph (a : LatticeVertex) (w h : ℕ) :=
  rectangleGraph (a.1, a.2 - 1) w (h + 1)

abbrev rectangleArbitraryBottomCollarInnerVertex (a : LatticeVertex) (w h : ℕ) :=
  RectangleVertex a w h

abbrev rectangleArbitraryBottomCollarOuterVertex (a : LatticeVertex) (w h : ℕ) :=
  RectangleVertex (a.1, a.2 - 1) w (h + 1)

def rectangleArbitraryBottomCollarBottom (a : LatticeVertex) (w h : ℕ) :
    Set (rectangleArbitraryBottomCollarInnerVertex a w h) :=
  {v | v.val.2 = a.2}

theorem rectangleArbitraryBottomCollar_subset (a : LatticeVertex) (w h : ℕ) :
    latticeRectangle a w h ⊆ latticeRectangle (a.1, a.2 - 1) w (h + 1) := by
  intro z hz
  rw [mem_latticeRectangle] at hz ⊢
  rcases hz with ⟨⟨hx1,hx2⟩,⟨hy1,hy2⟩⟩
  exact ⟨⟨hx1,hx2⟩,⟨by omega, by omega⟩⟩

def rectangleArbitraryBottomCollarEmbedding (a : LatticeVertex) (w h : ℕ) :
    rectangleArbitraryBottomCollarInnerVertex a w h ↪
      rectangleArbitraryBottomCollarOuterVertex a w h :=
  rectangleVertexEmbedding (rectangleArbitraryBottomCollar_subset a w h)

@[simp] theorem rectangleArbitraryBottomCollarEmbedding_val (a : LatticeVertex)
    (w h : ℕ) (v : rectangleArbitraryBottomCollarInnerVertex a w h) :
    (rectangleArbitraryBottomCollarEmbedding a w h v).val = v.val := rfl

local instance rectangleArbitraryBottomCollarOuterEdgeDecidableEq (a : LatticeVertex)
    (w h : ℕ) : DecidableEq (rectangleArbitraryBottomCollarOuterGraph a w h).edgeSet :=
  Classical.decEq _

def rectangleArbitraryBottomCollarRemoved (a : LatticeVertex) (w h : ℕ) :
    Configuration (rectangleArbitraryBottomCollarOuterGraph a w h) :=
  subgraphRemovedEdges
    ((rectangleArbitraryBottomCollarInnerGraph a w h).map
      (rectangleArbitraryBottomCollarEmbedding a w h))
    (rectangleArbitraryBottomCollarOuterGraph a w h)

def rectangleArbitraryBottomCollarState (a : LatticeVertex) (w h : ℕ) :
    RemovedConfiguration (rectangleArbitraryBottomCollarOuterGraph a w h)
      (rectangleArbitraryBottomCollarRemoved a w h) :=
  ⟨rectangleArbitraryBottomCollarRemoved a w h, Finset.Subset.rfl⟩

def rectangleArbitraryBottomCollarExteriorOrBottom (a : LatticeVertex) (w h : ℕ) :
    Set (rectangleArbitraryBottomCollarOuterVertex a w h) :=
  (Set.range (rectangleArbitraryBottomCollarEmbedding a w h))ᶜ ∪
    (rectangleArbitraryBottomCollarEmbedding a w h) ''
      rectangleArbitraryBottomCollarBottom a w h

theorem rectangleArbitraryBottomCollar_removed_edge_endpoints (a : LatticeVertex)
    (w h : ℕ) :
    ∀ ⦃e : (rectangleArbitraryBottomCollarOuterGraph a w h).edgeSet⦄,
      e ∈ (rectangleArbitraryBottomCollarState a w h).val →
      ∀ ⦃x : rectangleArbitraryBottomCollarOuterVertex a w h⦄, x ∈ e.1 →
        x ∈ rectangleArbitraryBottomCollarExteriorOrBottom a w h := by
  classical
  intro e he x hx
  have heR : e ∈ subgraphRemovedEdges
      ((rectangleArbitraryBottomCollarInnerGraph a w h).map
        (rectangleArbitraryBottomCollarEmbedding a w h))
      (rectangleArbitraryBottomCollarOuterGraph a w h) := by
    simpa [rectangleArbitraryBottomCollarState, rectangleArbitraryBottomCollarRemoved] using he
  have henot : e.val ∉ ((rectangleArbitraryBottomCollarInnerGraph a w h).map
      (rectangleArbitraryBottomCollarEmbedding a w h)).edgeSet :=
    (mem_subgraphRemovedEdges _).mp heR
  obtain ⟨ab,hab⟩ := Sym2.mk_surjective e.val
  rcases ab with ⟨a',b'⟩
  have heval : e.val = s(a',b') := hab.symm
  have habAdj : (rectangleArbitraryBottomCollarOuterGraph a w h).Adj a' b' := by
    apply (rectangleArbitraryBottomCollarOuterGraph a w h).mem_edgeSet.mp
    rw [← heval]
    exact e.property
  have hxAB : x = a' ∨ x = b' := by
    rw [heval] at hx
    exact (Sym2.mem_iff').mp hx
  have hnotboth : ¬ (a' ∈ Set.range (rectangleArbitraryBottomCollarEmbedding a w h) ∧
      b' ∈ Set.range (rectangleArbitraryBottomCollarEmbedding a w h)) := by
    rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    have hadj : (rectangleArbitraryBottomCollarOuterGraph a w h).Adj
        ((rectangleArbitraryBottomCollarEmbedding a w h) u)
        ((rectangleArbitraryBottomCollarEmbedding a w h) v) := by
      simpa [hu,hv] using habAdj
    have hsq : squareLattice.Adj u.val v.val := by
      change squareLattice.Adj ((rectangleArbitraryBottomCollarEmbedding a w h u).val)
        ((rectangleArbitraryBottomCollarEmbedding a w h v).val)
      exact (rectangleGraph_adj_iff _ _ _ _ _).mp hadj
    have hinner : (rectangleArbitraryBottomCollarInnerGraph a w h).Adj u v :=
      (rectangleGraph_adj_iff _ _ _ _ _).2 hsq
    have hmap : ((rectangleArbitraryBottomCollarInnerGraph a w h).map
        (rectangleArbitraryBottomCollarEmbedding a w h)).Adj a' b' :=
      (SimpleGraph.map_adj _ _ _ _).2 ⟨u,v,hinner,hu,hv⟩
    have hmem : s(a',b') ∈ ((rectangleArbitraryBottomCollarInnerGraph a w h).map
        (rectangleArbitraryBottomCollarEmbedding a w h)).edgeSet :=
      (SimpleGraph.mem_edgeSet _).2 hmap
    exact henot (heval ▸ hmem)
  have hinside_endpoint (u : rectangleArbitraryBottomCollarInnerVertex a w h)
      (z y : rectangleArbitraryBottomCollarOuterVertex a w h)
      (hzu : (rectangleArbitraryBottomCollarEmbedding a w h) u = z)
      (hynot : y ∉ Set.range (rectangleArbitraryBottomCollarEmbedding a w h))
      (hadj : (rectangleArbitraryBottomCollarOuterGraph a w h).Adj z y) :
      u ∈ rectangleArbitraryBottomCollarBottom a w h := by
    have hsquare : squareLattice.Adj z.val y.val :=
      (rectangleGraph_adj_iff _ _ _ _ _).mp hadj
    have huz := u.property
    rw [mem_latticeRectangle] at huz
    have hyy := y.property
    rw [mem_latticeRectangle] at hyy
    have hyinner : (a.2 ≤ y.val.2 ∧ y.val.2 ≤ a.2 + (h : ℤ)) →
        y ∈ Set.range (rectangleArbitraryBottomCollarEmbedding a w h) := by
      intro hy
      refine ⟨⟨y.val, ?_⟩, ?_⟩
      · rw [mem_latticeRectangle]
        exact ⟨⟨hyy.1.1,hyy.1.2⟩, by simpa using hy⟩
      · apply Subtype.ext
        rfl
    have hy_not : ¬ (a.2 ≤ y.val.2 ∧ y.val.2 ≤ a.2 + (h : ℤ)) := fun hy => hynot (hyinner hy)
    have hval : z.val = u.val := by
      have hh := congrArg (fun t : rectangleArbitraryBottomCollarOuterVertex a w h => t.val) hzu
      change u.val = z.val at hh
      exact hh.symm
    rw [hval] at hsquare
    rw [squareLattice_adj_iff] at hsquare
    rcases hsquare with ⟨_, hxy⟩ | ⟨_, hxy | hxy⟩
    · exact False.elim (hy_not (by omega))
    · exact False.elim (hy_not (by omega))
    · change u.val.2 = a.2
      omega
  rcases hxAB with hxa | hxb
  · rw [hxa]
    by_cases ha : a' ∈ Set.range (rectangleArbitraryBottomCollarEmbedding a w h)
    · obtain ⟨u,hu⟩ := ha
      have hb : b' ∉ Set.range (rectangleArbitraryBottomCollarEmbedding a w h) := fun hb =>
        hnotboth ⟨⟨u,hu⟩,hb⟩
      right
      refine ⟨u, hinside_endpoint u a' b' hu hb ?_, hu⟩
      simpa [hu] using habAdj
    · exact Or.inl ha
  · rw [hxb]
    by_cases hb : b' ∈ Set.range (rectangleArbitraryBottomCollarEmbedding a w h)
    · obtain ⟨u,hu⟩ := hb
      have ha : a' ∉ Set.range (rectangleArbitraryBottomCollarEmbedding a w h) := fun ha =>
        hnotboth ⟨ha,⟨u,hu⟩⟩
      right
      refine ⟨u, hinside_endpoint u b' a' hu ha ?_, hu⟩
      simpa [hu] using habAdj.symm
    · exact Or.inl hb

end
end PottsContinuity.FKC.FiniteFK
