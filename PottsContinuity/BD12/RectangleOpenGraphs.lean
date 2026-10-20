module

public import PottsContinuity.BD12.InfiniteRectangleEvents
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Open-graph bridges for finite restrictions of whole-plane states. -/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK PD.RCInfinite

noncomputable section

theorem embeddedRestriction_openGraph_adj {V : Type*} [Finite V]
    (G : SimpleGraph V) (j : G.edgeSet ↪ PD.squareLattice.edgeSet)
    (ω : LatticeConfiguration) (u v : V) :
    (openGraph G (embeddedRestriction G j ω)).Adj u v ↔
      ∃ e : G.edgeSet, e.val = s(u, v) ∧ ω (j e) = true := by
  rw [openGraph_adj]
  change (∃ e : G.edgeSet, e ∈ embeddedRestriction G j ω ∧ e.val = s(u, v)) ↔ _
  simp only [mem_embeddedRestriction, and_comm]

/-- The finite restricted open graph is exactly the whole-plane open graph
induced on the same vertex set, including every isolated vertex. -/
theorem embeddedRestriction_domainGraph (S : Finset LatticeVertex)
    (ω : LatticeConfiguration) :
    openGraph (PD.squareLattice.induce (S : Set LatticeVertex)) (embeddedRestriction (PD.squareLattice.induce (S : Set LatticeVertex)) (frozenEdgeEmbedding S) ω) =
      (PD.rcInfiniteOpenGraph ω).induce (S : Set LatticeVertex) := by
  ext u v
  rw [embeddedRestriction_openGraph_adj]
  change (∃ e : (PD.squareLattice.induce (S : Set LatticeVertex)).edgeSet, e.val = s(u, v) ∧
      ω (frozenEdgeEmbedding S e) = true) ↔
    (PD.rcInfiniteOpenGraph ω).Adj u.val v.val
  rw [rcInfiniteOpenGraph_adj]
  constructor
  · rintro ⟨e, he, hopen⟩
    have heq : (frozenEdgeEmbedding S e).val = s(u.val, v.val) := by
      change Sym2.map Subtype.val e.val = _
      rw [he]
      rfl
    have hedge : s(u.val, v.val) ∈ PD.squareLattice.edgeSet :=
      heq ▸ (frozenEdgeEmbedding S e).property
    refine ⟨hedge, ?_⟩
    have heq' : frozenEdgeEmbedding S e = ⟨s(u.val, v.val), hedge⟩ :=
      Subtype.ext heq
    exact heq' ▸ hopen
  · rintro ⟨he, hopen⟩
    have hadj : (PD.squareLattice.induce (S : Set LatticeVertex)).Adj u v := PD.squareLattice.mem_edgeSet.mp he
    let e : (PD.squareLattice.induce (S : Set LatticeVertex)).edgeSet := ⟨s(u, v), hadj⟩
    refine ⟨e, rfl, ?_⟩
    exact hopen

/-- A map allowed to contract edges transports reachability. This permits
removing excursions into degree-one boundary ports without adding open edges. -/
theorem reachable_map_of_eq_or_adj {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : ∀ {u v}, G.Adj u v → f u = f v ∨ H.Adj (f u) (f v))
    {u v : V} (huv : G.Reachable u v) : H.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact .rfl
  | @cons u v w huv p ih =>
    rcases hf huv with h | h
    · exact h ▸ ih
    · exact h.reachable.trans ih

end
end PottsContinuity.BD12
