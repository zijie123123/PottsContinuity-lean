module

public import PottsContinuity.PlanarMixed.RankedBandPaths
public import PottsContinuity.Thm3.RSW.FiniteOmegaComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.CompletePartialOrder
-- The local separation proof generalizes PlanarMixed.RankedBand from squares
-- to arbitrary finite reference graphs with two separately wired sets.

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK BD12 PlanarMixed
noncomputable section

 theorem bandOuter_disjoint {V : Type*} (r : V → ℤ) :
    Disjoint {v | r v ≤ 1} {v | 3 ≤ r v} := by
  apply Set.disjoint_left.mpr
  intro v h1 h3
  change r v ≤ 1 at h1
  change 3 ≤ r v at h3
  omega

def bandOuterBoundary {V : Type*} [Finite V] (r : V → ℤ) :=
  twoBlockBoundary {v | r v ≤ 1} {v | 3 ≤ r v} (bandOuter_disjoint r)

private theorem band_exterior_edge {V : Type*} [Finite V]
    (G : SimpleGraph V) (r : V → ℤ) (hstep : RankedBandEdges G r)
    {u v : V}
    (huv : (openGraph G (subgraphRemovedEdges ((rankedBandGraph G r).map
      (rankedBandEmbedding r)) G)).Adj u v) :
    (bandOuterBoundary r).partition.r u v := by
  have hG := openGraph_le G _ huv
  rcases hstep u v hG with hleft | hband | hright
  · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inr (Or.inl hleft))
  · obtain ⟨e, he, heq⟩ := (openGraph_adj G _ u v).mp huv
    have hnot := (mem_subgraphRemovedEdges e).mp he
    apply False.elim
    apply hnot
    rw [heq]
    apply ((rankedBandGraph G r).map (rankedBandEmbedding r)).mem_edgeSet.mpr
    exact (SimpleGraph.map_adj _ _ _ _).mpr
      ⟨⟨u, hband.1⟩, ⟨v, hband.2⟩, hG, rfl, rfl⟩
  · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inr (Or.inr hright))

private theorem band_outer_pullback {V : Type*} [Finite V] (r : V → ℤ) :
    Setoid.comap (rankedBandEmbedding r) (bandOuterBoundary r).partition ≤
      (rankedBandBoundary r).partition := by
  intro u v huv
  change (bandOuterBoundary r).partition.r u.val v.val at huv
  rcases (twoBlockBoundary_partition_rel _ _ (bandOuter_disjoint r) u.val v.val).mp huv
    with h | hleft | hright
  · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inl (Subtype.ext h))
  · change r u.val ≤ 1 ∧ r v.val ≤ 1 at hleft
    have hu : 1 ≤ r u.val ∧ r u.val ≤ 3 := u.property
    have hv : 1 ≤ r v.val ∧ r v.val ≤ 3 := v.property
    exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
      (Or.inr (Or.inl ⟨by change r u.val = 1; omega, by change r v.val = 1; omega⟩))
  · change 3 ≤ r u.val ∧ 3 ≤ r v.val at hright
    have hu : 1 ≤ r u.val ∧ r u.val ≤ 3 := u.property
    have hv : 1 ≤ r v.val ∧ r v.val ≤ 3 := v.property
    exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
      (Or.inr (Or.inr ⟨by change r u.val = 3; omega, by change r v.val = 3; omega⟩))

/-- Every exterior state induces at most the separate marked-level wiring. -/
theorem rankedBand_exterior_partition_le
    {V : Type*} [Finite V] (G : SimpleGraph V) (r : V → ℤ)
    (hstep : RankedBandEdges G r) (L R : Set V) (hdis : Disjoint L R)
    (hleft : ∀ v ∈ L, r v ≤ 1) (hright : ∀ v ∈ R, 3 ≤ r v) :
    ∀ K : RemovedConfiguration G
      (subgraphRemovedEdges ((rankedBandGraph G r).map (rankedBandEmbedding r)) G),
      (isolatedExtensionPullbackBoundary (rankedBandEmbedding r)
        (frozenBoundary (twoBlockBoundary L R hdis) K.val)).partition ≤
          (rankedBandBoundary r).partition := by
  apply embedded_exterior_partition_le_of_separation _ G _ _ _ (bandOuterBoundary r).partition
  · intro u v huv
    rcases (twoBlockBoundary_partition_rel _ _ _ u v).mp huv with h | hL | hR
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inl h)
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
        (Or.inr (Or.inl ⟨hleft u hL.1, hleft v hL.2⟩))
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
        (Or.inr (Or.inr ⟨hright u hR.1, hright v hR.2⟩))
  · exact fun _ _ huv => band_exterior_edge G r hstep huv
  · exact band_outer_pullback r

end
end PottsContinuity.RSW
