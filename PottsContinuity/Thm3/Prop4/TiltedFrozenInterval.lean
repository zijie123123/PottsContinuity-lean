module

public import PottsContinuity.Thm3.Prop4.TiltedInterval

/-!
# The exact top-only law between two closed tilted cuts

A genuine frozen state of every non-inner edge is used. Closed cuts prove
that its open edges have no endpoint in the surviving interval; this support
property is derived rather than assumed as a conditional-law interface.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

noncomputable section

local instance frozenIntervalEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _
local instance frozenIntervalEdgeDecidableEq (n M : ℕ) (t : ℝ) :
    DecidableEq (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- Closed cuts at lo-1 and hi force every open neighbour of a retained
interval vertex to stay in the same interval. -/
theorem open_edge_preserves_tiltedInterval (n M : ℕ) (t : ℝ) (lo hi : ℤ)
    (A : PD.FK.Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))))
    (hL : Disjoint A (tiltedWindowCutEdges n M t (lo-1)))
    (hR : Disjoint A (tiltedWindowCutEdges n M t hi))
    (u v : (tiltedWindow n M t : Set (ℤ × ℤ)))
    (huv : (PD.FK.openGraph _ A).Adj u v) (hu : lo ≤ u.val.1 ∧ u.val.1 ≤ hi) :
    lo ≤ v.val.1 ∧ v.val.1 ≤ hi := by
  constructor
  · by_contra h
    obtain ⟨e,he,hecut⟩ := open_edge_crossing_mem_tiltedCut n M t (lo-1) A v u huv.symm
      (by omega) (by omega)
    exact (Finset.disjoint_left.mp hL) he hecut
  · by_contra h
    obtain ⟨e,he,hecut⟩ := open_edge_crossing_mem_tiltedCut n M t hi A u v huv hu.2
      (lt_of_not_ge h)
    exact (Finset.disjoint_left.mp hR) he hecut

/-- No open removed edge has an endpoint in the selected interval. Both
internal edges and the two boundary-crossing possibilities are ruled out. -/
theorem tiltedInterval_removed_open_endpoints_outside (n M : ℕ) (t : ℝ) (lo hi : ℤ)
    (K : PD.FK.RemovedConfiguration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))
      (PD.FK.subgraphRemovedEdges
        ((squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ))).map
          (tiltedIntervalEmbedding n M t lo hi))
        (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))))
    (hL : Disjoint K.val (tiltedWindowCutEdges n M t (lo-1)))
    (hR : Disjoint K.val (tiltedWindowCutEdges n M t hi)) :
    ∀ ⦃e⦄, e ∈ K.val → ∀ ⦃v : (tiltedWindow n M t : Set (ℤ × ℤ))⦄,
      v ∈ e.val → v ∉ Set.range (tiltedIntervalEmbedding n M t lo hi) := by
  intro e he v hv hvrange
  have hvbound := (mem_tiltedIntervalEmbedding_range n M t lo hi v).mp hvrange
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective e.val
  have heval : e.val = s(a,b) := hab.symm
  have hadj : (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).Adj a b := by
    apply (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).mem_edgeSet.mp
    rw [← heval]
    exact e.property
  have hopen : (PD.FK.openGraph _ K.val).Adj a b := (PD.FK.openGraph_adj _ K.val a b).mpr ⟨e,he,heval⟩
  have hvab : v = a ∨ v = b := by rw [heval] at hv; exact Sym2.mem_iff'.mp hv
  have hbds : (lo ≤ a.val.1 ∧ a.val.1 ≤ hi) ∧ (lo ≤ b.val.1 ∧ b.val.1 ≤ hi) := by
    rcases hvab with h | h
    · rw [h] at hvbound
      exact ⟨hvbound,open_edge_preserves_tiltedInterval n M t lo hi K.val hL hR a b hopen hvbound⟩
    · rw [h] at hvbound
      exact ⟨open_edge_preserves_tiltedInterval n M t lo hi K.val hL hR b a hopen.symm hvbound,hvbound⟩
  let x : (tiltedInterval n M t lo hi : Set (ℤ × ℤ)) :=
    ⟨a.val,(mem_tiltedInterval _ _ _ _ _ _).mpr ⟨a.property,hbds.1⟩⟩
  let y : (tiltedInterval n M t lo hi : Set (ℤ × ℤ)) :=
    ⟨b.val,(mem_tiltedInterval _ _ _ _ _ _).mpr ⟨b.property,hbds.2⟩⟩
  have hxy : (squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ))).Adj x y := hadj
  have hmapAdj : ((squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ))).map
      (tiltedIntervalEmbedding n M t lo hi)).Adj a b :=
    (SimpleGraph.map_adj _ _ _ _).mpr ⟨x,y,hxy,rfl,rfl⟩
  have hnot := (PD.FK.mem_subgraphRemovedEdges e).mp (K.property he)
  apply hnot
  rw [heval]
  exact ((squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ))).map
    (tiltedIntervalEmbedding n M t lo hi)).mem_edgeSet.mpr hmapAdj

/-- A genuine exact exterior state with two closed cuts leaves the actual
top-only FK law on the surviving induced interval. -/
theorem law_filter_frozen_map_tiltedInterval_eq_top (θ : PD.FK.Parameters)
    (n M : ℕ) (t : ℝ) (lo hi : ℤ) (i : Fin 2)
    (hinside : ∀ z ∈ tiltedInterval n M t lo hi, z ∉ vertexBoundary (box M))
    (K : PD.FK.RemovedConfiguration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))
      (PD.FK.subgraphRemovedEdges
        ((squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ))).map
          (tiltedIntervalEmbedding n M t lo hi))
        (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))))
    (hL : Disjoint K.val (tiltedWindowCutEdges n M t (lo-1)))
    (hR : Disjoint K.val (tiltedWindowCutEdges n M t hi)) :
    ((PD.FK.law _ θ (tiltedWindowBoundary n M t i)).filter
      (PD.FK.frozenStateEvent _ K) (PD.FK.frozenStateEvent_support θ _ _ K)).map
        (PD.FK.embeddedConfigurationRestriction
          (squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ)))
          (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))
          (tiltedIntervalEmbedding n M t lo hi) (tiltedInterval_map_le n M t lo hi)) =
      PD.FK.law _ θ (tiltedIntervalTopBoundary n M t lo hi) := by
  rw [PD.FK.law_filter_frozen_map_embeddedRestriction]
  apply PD.FK.law_eq_of_boundary_partition_eq
  exact tiltedInterval_frozen_partition_eq_top n M t lo hi i K.val hinside
    (tiltedInterval_removed_open_endpoints_outside n M t lo hi K hL hR)

end

end PottsContinuity.Thm3.Prop4
