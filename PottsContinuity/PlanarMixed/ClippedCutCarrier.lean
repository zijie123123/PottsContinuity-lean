module

public import PottsContinuity.PlanarMixed.CanonicalCutCarrier

/-! Exact clipping of an active reference band to a source graph. Source
bonds absent in the reference are retained in the exposed complement. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK
noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
local instance clippedCutCarrierEdgeDecidableEq (S : SimpleGraph W) :
    DecidableEq S.edgeSet := Classical.decEq _

omit [Finite W] in
/-- The active band has the same adjacency when read through a source
inclusion which contains every band vertex. No ambient-edge inclusion is needed. -/
theorem clipped_active_adj_iff (G : SimpleGraph V) (r : V → ℤ)
    (hstep : RankedBandEdges G r) (f : W ↪ V) (k : rankedBandVertices r ↪ W)
    (hk : ∀ v, f (k v) = v.val) (u v : W) :
    ((edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)).map k).Adj u v ↔
      G.Adj (f u) (f v) ∧
        ¬ ((r (f u) ≤ 1 ∧ r (f v) ≤ 1) ∨ (3 ≤ r (f u) ∧ 3 ≤ r (f v))) := by
  constructor
  · intro h
    obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
    obtain ⟨hG,hn⟩ := (edgeRestriction_adj_exists_not_mem _ _ a b).mp hab
    rw [hk a,hk b]
    refine ⟨hG,?_⟩
    intro hout
    apply hn
    apply (mem_bandArcBonds_pair G r a b hG).mpr
    have ha := a.property
    have hb := b.property
    rcases hout with hl | hr
    · exact Or.inl ⟨by change 1 ≤ r a.val ∧ r a.val ≤ 3 at ha; omega,
        by change 1 ≤ r b.val ∧ r b.val ≤ 3 at hb; omega⟩
    · exact Or.inr ⟨by change 1 ≤ r a.val ∧ r a.val ≤ 3 at ha; omega,
        by change 1 ≤ r b.val ∧ r b.val ≤ 3 at hb; omega⟩
  · rintro ⟨hG,hout⟩
    have hb : (1 ≤ r (f u) ∧ r (f u) ≤ 3) ∧ (1 ≤ r (f v) ∧ r (f v) ≤ 3) := by
      rcases hstep (f u) (f v) hG with hl | hm | hr
      · exact (hout (Or.inl hl)).elim
      · exact hm
      · exact (hout (Or.inr hr)).elim
    let a : rankedBandVertices r := ⟨f u,hb.1⟩
    let b : rankedBandVertices r := ⟨f v,hb.2⟩
    have ha : k a = u := f.injective (hk a)
    have hb' : k b = v := f.injective (hk b)
    apply (SimpleGraph.map_adj _ _ _ _).mpr
    refine ⟨a,b,?_,ha,hb'⟩
    apply (edgeRestriction_adj_exists_not_mem _ _ a b).mpr
    refine ⟨hG,?_⟩
    intro he
    rcases (mem_bandArcBonds_pair G r a b hG).mp he with hl | hr
    · exact hout (Or.inl ⟨hl.1.le,hl.2.le⟩)
    · exact hout (Or.inr ⟨hr.1.ge,hr.2.ge⟩)

/-- Clipping a reference band reveals every missing-reference source bond,
as well as both closed exteriors. This includes deleted slit bonds. -/
theorem clipped_active_complement (G : SimpleGraph V) (S : SimpleGraph W)
    (r : V → ℤ) (hstep : RankedBandEdges G r)
    (f : W ↪ V) (k : rankedBandVertices r ↪ W) (hk : ∀ v, f (k v) = v.val) :
    subgraphRemovedEdges
      ((edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)).map k) S =
      subgraphRemovedEdges (G.comap f) S ∪ outerCutReveal S (r ∘ f) := by
  classical
  apply Finset.ext
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv := S.mem_edgeSet.mp he
    rw [Finset.mem_union,mem_subgraphRemovedEdges,mem_subgraphRemovedEdges,
      mem_outerCutReveal_pair S (r ∘ f) u v huv]
    change (¬ ((edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)).map k).Adj u v) ↔
      (¬ G.Adj (f u) (f v)) ∨
        ((r (f u) ≤ 1 ∧ r (f v) ≤ 1) ∨ (3 ≤ r (f u) ∧ 3 ≤ r (f v)))
    rw [clipped_active_adj_iff G r hstep f k hk u v]
    tauto

end
end PottsContinuity.PlanarMixed
