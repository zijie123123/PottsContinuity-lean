-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitScreenActualClosedGraph.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitScreenCrossingPruning
public import PottsContinuity.FKC.FiniteFK.SlitBoxConfigurationDualState

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

/-- The finite-configuration closed-dual graph on a literal finite face-base
carrier. Each edge is witnessed by an actual slit-box edge absent from A. -/
def slitScreenActualConfigurationClosedDualGraph (m : ℕ)
    (A : Configuration (slitBoxGraph (16 * m))) (F : Finset LatticeVertex) :
    SimpleGraph LatticeVertex where
  Adj u v := ∃ d : LatticeBond, ∃ e : (slitBoxGraph (16 * m)).edgeSet,
    latticeBondEdge (primalBondOfDual d) = slitBoxEdgeEmbedding (16 * m) e ∧
      e ∉ A ∧
      (u = d.source ∧ v = d.target ∨ u = d.target ∧ v = d.source) ∧
      u ∈ F ∧ v ∈ F
  symm := ⟨by
    intro u v h
    rcases h with ⟨d, e, he, hnot, huv, huF, hvF⟩
    rcases huv with huv | huv
    · exact ⟨d, e, he, hnot, Or.inr ⟨huv.2, huv.1⟩, hvF, huF⟩
    · exact ⟨d, e, he, hnot, Or.inl ⟨huv.2, huv.1⟩, hvF, huF⟩
  ⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨d, e, _, _, huv, _, _⟩
    rcases huv with huv | huv
    · exact d.source_ne_target (huv.1.symm.trans huv.2)
    · exact d.source_ne_target (huv.2.symm.trans huv.1)
  ⟩

/-- The finite graph above is exactly the actual whole-plane closed-dual graph
of the slit-box extension, restricted to the same finite face bases and to dual
bonds crossing an edge of the slit graph. -/
theorem slitScreenActualConfigurationClosedDualGraph_eq_restricted
    (m : ℕ) (A : Configuration (slitBoxGraph (16 * m)))
    (F : Finset LatticeVertex) :
    slitScreenActualConfigurationClosedDualGraph m A F =
      slitScreenSlitRestrictedGraph (slitBoxConfigurationExtension (16 * m) A) m F := by
  ext u v
  constructor
  · rintro ⟨d, e, he, hnot, hdir, huF, hvF⟩
    refine ⟨d, ?_, hdir, huF, hvF, ?_⟩
    · exact (slitBoxConfigurationBondState_false_iff (16 * m) A
        (primalBondOfDual d) e he).2 hnot
    · apply (slitScreenPrimalBondInSlit_iff_edgeImage (16 * m)
        (primalBondOfDual d)).2
      exact ⟨e, he.symm⟩
  · rintro ⟨d, hclosed, hdir, huF, hvF, hslit⟩
    obtain ⟨e, he⟩ := (slitScreenPrimalBondInSlit_iff_edgeImage
      (16 * m) (primalBondOfDual d)).1 hslit
    have hnot := (slitBoxConfigurationBondState_false_iff (16 * m) A
      (primalBondOfDual d) e he.symm).1 hclosed
    exact ⟨d, e, he.symm, hnot, hdir, huF, hvF⟩

/-- For a finite slit-box configuration, bottom-to-top connectivity in the
actual closed-dual right screen equals connectivity using only actual slit
edges in the closed-dual extension. -/
theorem slitScreenRightFiniteConfigurationCrossing_iff_slitRestricted
    (m : ℕ) (hm : 1 ≤ m) (A : Configuration (slitBoxGraph (16 * m))) :
    (∃ x ∈ slitScreenBottomTerminals m (slitScreenRightFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenRightFaceBases m),
      (slitScreenClosedDualInducedGraph
        (slitBoxConfigurationExtension (16 * m) A)
        (slitScreenRightFaceBases m)).Reachable x y) ↔
    (∃ x ∈ slitScreenBottomTerminals m (slitScreenRightFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenRightFaceBases m),
      (slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenRightFaceBases m)).Reachable x y) := by
  have hgraph := slitScreenActualConfigurationClosedDualGraph_eq_restricted
    m A (slitScreenRightFaceBases m)
  have h := slitScreenRightCrossing_iff_slitRestricted
    (slitBoxConfigurationExtension (16 * m) A) m hm
  rw [← hgraph] at h
  exact h

/-- The analogous finite-configuration equivalence for the left tall screen. -/
theorem slitScreenLeftFiniteConfigurationCrossing_iff_slitRestricted
    (m : ℕ) (hm : 1 ≤ m) (A : Configuration (slitBoxGraph (16 * m))) :
    (∃ x ∈ slitScreenBottomTerminals m (slitScreenLeftFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenLeftFaceBases m),
      (slitScreenClosedDualInducedGraph
        (slitBoxConfigurationExtension (16 * m) A)
        (slitScreenLeftFaceBases m)).Reachable x y) ↔
    (∃ x ∈ slitScreenBottomTerminals m (slitScreenLeftFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenLeftFaceBases m),
      (slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenLeftFaceBases m)).Reachable x y) := by
  have hgraph := slitScreenActualConfigurationClosedDualGraph_eq_restricted
    m A (slitScreenLeftFaceBases m)
  have h := slitScreenLeftCrossing_iff_slitRestricted
    (slitBoxConfigurationExtension (16 * m) A) m hm
  rw [← hgraph] at h
  exact h

end PottsContinuity.FKC.FiniteFK
