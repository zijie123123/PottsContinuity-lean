module

public import PottsContinuity.PlanarMixed.SquareCrosscutData
public import PottsContinuity.Exploration.FiniteStoppingSetDMP

/-! Canonical bond carriers for the two one-sided cut exteriors and for
prewired bonds inside the two marked arcs. All original vertices are retained.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section
variable {V : Type*} [Finite V]

/-- Exactly the graph bonds with both endpoints in S. -/
def internalBonds (G : SimpleGraph V) (S : Set V) : Configuration G := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  exact Finset.univ.filter (fun e => ∀ v ∈ e.val, v ∈ S)

theorem mem_internalBonds_pair (G : SimpleGraph V) (S : Set V)
    (u v : V) (huv : G.Adj u v) :
    (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ internalBonds G S ↔ u ∈ S ∧ v ∈ S := by
  classical
  simp only [internalBonds, Finset.mem_filter, Finset.mem_univ, true_and,
    Sym2.forall_mem_pair]

/-- The complete left and right closed-region reveals for a ranked band. -/
def outerCutReveal (G : SimpleGraph V) (r : V → ℤ) : Configuration G := by
  classical
  exact internalBonds G {v | r v ≤ 1} ∪ internalBonds G {v | 3 ≤ r v}

/-- All sampled band bonds internal to either MINIMAL separately wired arc. -/
def bandArcBonds (G : SimpleGraph V) (r : V → ℤ) :
    Configuration (rankedBandGraph G r) := by
  classical
  exact internalBonds (rankedBandGraph G r) (rankedBandFirstArc r) ∪
    internalBonds (rankedBandGraph G r) (rankedBandSecondArc r)

theorem mem_outerCutReveal_pair (G : SimpleGraph V) (r : V → ℤ)
    (u v : V) (huv : G.Adj u v) :
    (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ outerCutReveal G r ↔
      (r u ≤ 1 ∧ r v ≤ 1) ∨ (3 ≤ r u ∧ 3 ≤ r v) := by
  classical
  rw [outerCutReveal, Finset.mem_union,
    mem_internalBonds_pair G {v | r v ≤ 1} u v huv,
    mem_internalBonds_pair G {v | 3 ≤ r v} u v huv]
  rfl

theorem mem_bandArcBonds_pair (G : SimpleGraph V) (r : V → ℤ)
    (u v : rankedBandVertices r) (huv : (rankedBandGraph G r).Adj u v) :
    (⟨s(u,v), (rankedBandGraph G r).mem_edgeSet.mpr huv⟩ :
      (rankedBandGraph G r).edgeSet) ∈ bandArcBonds G r ↔
      (r u.val = 1 ∧ r v.val = 1) ∨ (r u.val = 3 ∧ r v.val = 3) := by
  classical
  rw [bandArcBonds, Finset.mem_union,
    mem_internalBonds_pair (rankedBandGraph G r) (rankedBandFirstArc r) u v huv,
    mem_internalBonds_pair (rankedBandGraph G r) (rankedBandSecondArc r) u v huv]
  rfl

end
end PottsContinuity.PlanarMixed
