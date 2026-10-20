-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverLayerBlocks.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBranchRootComparison
public import PottsContinuity.FKC.FiniteFK.DisjointBlockEventAvoidance
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

local instance coverLayerStripEdgeFintype (n : ℕ) :
    Fintype (ParafermionicStripGraph n).edgeSet := Fintype.ofFinite _
local instance coverLayerStripEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicStripGraph n).edgeSet := Classical.decEq _
local instance coverLayerMappedEdgeFintype (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)) :
    Fintype ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk)).edgeSet :=
  Fintype.ofFinite _
local instance coverLayerAmbientEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance coverLayerAmbientEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

/-- The actual ambient edges in the image of one finite cover strip. -/
def parafermionicCoverLayerBlock (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)) :
    Configuration (ParafermionicAmbientGraph n) :=
  Finset.univ \ subgraphRemovedEdges
    ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
    (ParafermionicAmbientGraph n)

@[simp] theorem mem_parafermionicCoverLayerBlock (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    e ∈ parafermionicCoverLayerBlock n k hk ↔
      e.val ∈ ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk)).edgeSet := by
  classical
  simp [parafermionicCoverLayerBlock, mem_subgraphRemovedEdges]

theorem parafermionicCoverLayerBlock_disjoint (n : ℕ) (k j : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (hj : -((n ^ 5 : ℕ) : ℤ) ≤ j ∧ j ≤ ((n ^ 5 : ℕ) : ℤ)) (hkj : k ≠ j) :
    Disjoint (parafermionicCoverLayerBlock n k hk)
      (parafermionicCoverLayerBlock n j hj) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hek hej
  have hmemK := (mem_parafermionicCoverLayerBlock n k hk e).mp hek
  have hmemJ := (mem_parafermionicCoverLayerBlock n j hj e).mp hej
  obtain ⟨ab, hab⟩ := Sym2.mk_surjective e.val
  rcases ab with ⟨a,b⟩
  have heval : e.val = s(a,b) := hab.symm
  have hadjK : ((ParafermionicStripGraph n).map
      (parafermionicCoverStripEmbedding n k hk)).Adj a b := by
    apply (((ParafermionicStripGraph n).map
      (parafermionicCoverStripEmbedding n k hk)).mem_edgeSet).mp
    rw [← heval]
    exact hmemK
  have hadjJ : ((ParafermionicStripGraph n).map
      (parafermionicCoverStripEmbedding n j hj)).Adj a b := by
    apply (((ParafermionicStripGraph n).map
      (parafermionicCoverStripEmbedding n j hj)).mem_edgeSet).mp
    rw [← heval]
    exact hmemJ
  rcases (SimpleGraph.map_adj (parafermionicCoverStripEmbedding n k hk)
      (ParafermionicStripGraph n) a b).mp hadjK with ⟨u, v, huv, hua, hvb⟩
  rcases (SimpleGraph.map_adj (parafermionicCoverStripEmbedding n j hj)
      (ParafermionicStripGraph n) a b).mp hadjJ with ⟨u', v', huv', hua', hvb'⟩
  have hvertex : parafermionicCoverStripEmbedding n k hk u =
      parafermionicCoverStripEmbedding n j hj u' := hua.trans hua'.symm
  have hsheet : (parafermionicCoverStripEmbedding n k hk u).val.2 =
      (parafermionicCoverStripEmbedding n j hj u').val.2 :=
    congrArg (fun z : ParafermionicAmbientVertex n => z.1.2) hvertex
  have : k = j := by
    simpa [parafermionicCoverStripEmbedding, parafermionicCoverRectangleLift] using hsheet
  exact hkj this

def parafermionicCoverLayerBranchRootEvent (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (hn : 1 ≤ n) : Set (Configuration (ParafermionicAmbientGraph n)) :=
  {A | parafermionicCoverStripDualRestriction n k hk A ∈
    parafermionicCoverBranchRootEvent n hn}

theorem parafermionicCoverLayerBranchRootEvent_local (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (hn : 1 ≤ n) (A B : Configuration (ParafermionicAmbientGraph n))
    (hAB : A ∩ parafermionicCoverLayerBlock n k hk =
      B ∩ parafermionicCoverLayerBlock n k hk) :
    (A ∈ parafermionicCoverLayerBranchRootEvent n k hk hn ↔
      B ∈ parafermionicCoverLayerBranchRootEvent n k hk hn) := by
  classical
  let G := ParafermionicStripGraph n
  let H := ParafermionicAmbientGraph n
  let f := parafermionicCoverStripEmbedding n k hk
  have hrest : embeddedConfigurationRestriction G H f
      (parafermionicCoverStrip_map_le n k hk) A =
    embeddedConfigurationRestriction G H f
      (parafermionicCoverStrip_map_le n k hk) B := by
    apply Finset.ext
    intro e
    rw [mem_embeddedConfigurationRestriction, mem_embeddedConfigurationRestriction]
    have hemap : embeddedEdgeEmbedding G H f
        (parafermionicCoverStrip_map_le n k hk) e ∈
        parafermionicCoverLayerBlock n k hk := by
      apply (mem_parafermionicCoverLayerBlock n k hk
        (embeddedEdgeEmbedding G H f (parafermionicCoverStrip_map_le n k hk) e)).2
      rw [embeddedEdgeEmbedding_coe]
      exact (isolatedExtensionEdgeEquiv G f e).property
    have hmem := congrArg
      (fun C : Configuration H => embeddedEdgeEmbedding G H f
        (parafermionicCoverStrip_map_le n k hk) e ∈ C) hAB
    simpa [Finset.mem_inter, hemap] using hmem
  change (parafermionicCoverStripDualRestriction n k hk A ∈
      parafermionicCoverBranchRootEvent n hn ↔
    parafermionicCoverStripDualRestriction n k hk B ∈
      parafermionicCoverBranchRootEvent n hn)
  dsimp [parafermionicCoverStripDualRestriction]
  rw [hrest]

theorem univ_sdiff_parafermionicCoverLayerBlock (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)) :
    Finset.univ \ parafermionicCoverLayerBlock n k hk =
      subgraphRemovedEdges
        ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
        (ParafermionicAmbientGraph n) := by
  classical
  simp [parafermionicCoverLayerBlock]

end
end PottsContinuity.FKC.FiniteFK
