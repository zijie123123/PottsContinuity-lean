-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverOpenWalkFilling.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverFiniteOpenPrimalAvoidance
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingSimplicity
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalkFillingPropagation
public import PottsContinuity.FKC.Medial.ParafermionicCoverFiniteFaceEnclosure
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open SimpleGraph

/-- For any common finite enclosure of the actual refined pairing cycle and
all faces visited by a finite open walk, the same named filling has matching
endpoint membership. -/
theorem parafermionicCoverOpenWalkFilling_endpoint_iff
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {a : ParafermionicCoverFinitePort n × Bool}
    (q : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk a a)
    (hq : q.IsCycle)
    {u v : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v)
    (N : ℕ) (hN : 1 ≤ N)
    (hR : ∀ z ∈ (parafermionicCoverRefinedPairingWalk n hn A q).support,
      z ∈ parafermionicCoverBoxVertices N)
    (hP : ∀ z ∈ (parafermionicCoverRefinedPrimalSubstitute
      (w.map (parafermionicCoverBoxOpenWalkHom n A))).support,
      z ∈ parafermionicCoverFiniteOrdinaryFaces N) :
    let R := parafermionicCoverRefinedPairingWalk n hn A q
    let C := R.induce (parafermionicCoverBoxVertices N) hR
    let hC : C.IsCycle := by
      have hcycle : R.IsCycle :=
        parafermionicCoverRefinedPairingWalk_isCycle n hn A q hq
      have hmap : (R.induce (parafermionicCoverBoxVertices N) hR).map
          (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
            (parafermionicCoverBoxVertices N)).toHom = R := by
        simpa [R, parafermionicCoverBoxGraph] using
          (SimpleGraph.Walk.map_induce R hR)
      have hmapped : ((R.induce (parafermionicCoverBoxVertices N) hR).map
          (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
            (parafermionicCoverBoxVertices N)).toHom).IsCycle := by
        simpa [hmap] using hcycle
      exact (SimpleGraph.Walk.isCycle_map_iff_of_injective
        (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
          (parafermionicCoverBoxVertices N)).injective).mp hmapped
    (∃ i : ParafermionicCoverFiniteFaceTopIndex N,
      i.1 = parafermionicCoverRefinedCoarseCenter (parafermionicCoverBoxOpenWalkHom n A u) ∧ i ∈ parafermionicCoverSimpleCycleFillingSet hN C hC) ↔
    (∃ i : ParafermionicCoverFiniteFaceTopIndex N,
      i.1 = parafermionicCoverRefinedCoarseCenter (parafermionicCoverBoxOpenWalkHom n A v) ∧ i ∈ parafermionicCoverSimpleCycleFillingSet hN C hC) := by
  dsimp only
  let R := parafermionicCoverRefinedPairingWalk n hn A q
  let P := parafermionicCoverRefinedPrimalSubstitute
    (w.map (parafermionicCoverBoxOpenWalkHom n A))
  have hRcycle : R.IsCycle := parafermionicCoverRefinedPairingWalk_isCycle n hn A q hq
  have hmap : (R.induce (parafermionicCoverBoxVertices N) hR).map
      (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
        (parafermionicCoverBoxVertices N)).toHom = R := by
    simpa [R, parafermionicCoverBoxGraph] using
      (SimpleGraph.Walk.map_induce R hR)
  have hCcycle : (R.induce (parafermionicCoverBoxVertices N) hR).IsCycle := by
    have hmapped : ((R.induce (parafermionicCoverBoxVertices N) hR).map
        (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
          (parafermionicCoverBoxVertices N)).toHom).IsCycle := by
      simpa [hmap] using hRcycle
    exact (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
        (parafermionicCoverBoxVertices N)).injective).mp hmapped
  have hbase : ∀ z ∈ P.support,
      ∃ i : ParafermionicCoverFiniteFaceTopIndex N, i.1 = z := by
    intro z hz
    exact ⟨⟨z, hP z hz⟩, rfl⟩
  have havoidFull := parafermionicCoverBoxOpenWalk_refinement_avoidsPairingWalk
    n hn A w q
  have havoid : ∀ z ∈ P.support, ∀ x ∈
      (R.induce (parafermionicCoverBoxVertices N) hR).support, z ≠ x.1 := by
    intro z hz x hx heq
    have hxR : x.1 ∈ R.support := by
      have hxmap : x.1 ∈
          ((R.induce (parafermionicCoverBoxVertices N) hR).map
            (SimpleGraph.Embedding.induce (G := parafermionicCoverGraph)
              (parafermionicCoverBoxVertices N)).toHom).support := by
        rw [SimpleGraph.Walk.support_map]
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      simpa [hmap] using hxmap
    have hznot : z ∉ R.support := havoidFull z hz
    exact hznot (heq ▸ hxR)
  exact parafermionicCoverSimpleCycleFillingSet_mem_iff_along_walk
    hN (R.induce (parafermionicCoverBoxVertices N) hR) hCcycle P hbase havoid

/-- One finite box simultaneously contains a refined pairing cycle and every
face visited by the corresponding refined primal walk, together with arbitrary
extra nonbranch face bases. -/
theorem parafermionicCoverOpenWalkFilling_exists_common_box
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {a : ParafermionicCoverFinitePort n × Bool}
    (q : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk a a)
    {u v : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v)
    (extraF : List ParafermionicCoverVertex)
    (hextra : ∀ f ∈ extraF, f.1 ≠ (0,-1)) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ z ∈ (parafermionicCoverRefinedPairingWalk n hn A q).support,
        z ∈ parafermionicCoverBoxVertices N) ∧
      (∀ f ∈ (parafermionicCoverRefinedPrimalSubstitute
        (w.map (parafermionicCoverBoxOpenWalkHom n A))).support ++ extraF,
        f ∈ parafermionicCoverFiniteOrdinaryFaces N) := by
  let R := parafermionicCoverRefinedPairingWalk n hn A q
  let P := parafermionicCoverRefinedPrimalSubstitute
    (w.map (parafermionicCoverBoxOpenWalkHom n A))
  have hnonbranch : ∀ z ∈ P.support, z.1 ≠ (0,-1) := by
    intro z hz hbranch
    have hmod := parafermionicCoverRefinedPrimalSubstitute_support_modulus
      (w.map (parafermionicCoverBoxOpenWalkHom n A)) hz
    rcases z with ⟨⟨x,y⟩,k⟩
    change (x,y) = (0,-1) at hbranch
    simp only [Prod.mk.injEq] at hbranch
    rcases hbranch with ⟨rfl,rfl⟩
    norm_num at hmod
  have hordinary : ∀ f ∈ P.support ++ extraF, f.1 ≠ (0,-1) := by
    intro f hf
    rcases List.mem_append.mp hf with hP | hF
    · exact hnonbranch f hP
    · exact hextra f hF
  obtain ⟨N,hN,hbox,hfaces⟩ := parafermionicCoverFiniteFaceLists_enclosed_in_box
    R.support (P.support ++ extraF) hordinary
  exact ⟨N,hN,hbox,by simpa [P] using hfaces⟩

end PottsContinuity.FKC.FiniteFK
