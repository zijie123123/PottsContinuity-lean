-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitScreenLocalSupport.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitScreenActualClosedGraph

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

/-- The finite slit-edge support of a face carrier: original edges crossed by a
normalized dual bond whose two face bases lie in F. -/
noncomputable def slitScreenActualClosedGraphSupport (m : ℕ) (F : Finset LatticeVertex) :
    Finset (slitBoxGraph (16 * m)).edgeSet := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ d : LatticeBond,
      d.source ∈ F ∧ d.target ∈ F ∧
        latticeBondEdge (primalBondOfDual d) = slitBoxEdgeEmbedding (16 * m) e

/-- Agreement on the actual slit edges seen by a finite face carrier makes the
corresponding finite-configuration closed-dual graphs identical. -/
theorem slitScreenActualConfigurationClosedDualGraph_eq_of_agree_on_support
    (m : ℕ) (F : Finset LatticeVertex)
    (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : ∀ e ∈ slitScreenActualClosedGraphSupport m F,
      (e ∈ A ↔ e ∈ B)) :
    slitScreenActualConfigurationClosedDualGraph m A F =
      slitScreenActualConfigurationClosedDualGraph m B F := by
  classical
  ext u v
  constructor
  · rintro ⟨d, e, he, hnotA, hdir, huF, hvF⟩
    have hdsource : d.source ∈ F := by
      rcases hdir with h | h
      · rw [← h.1]; exact huF
      · rw [← h.2]; exact hvF
    have hdtarget : d.target ∈ F := by
      rcases hdir with h | h
      · rw [← h.2]; exact hvF
      · rw [← h.1]; exact huF
    have hsupport : e ∈ slitScreenActualClosedGraphSupport m F := by
      simp only [slitScreenActualClosedGraphSupport, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨d, hdsource, hdtarget, he⟩
    have hnotB : e ∉ B := by
      intro heB
      exact hnotA ((hagree e hsupport).mpr heB)
    exact ⟨d, e, he, hnotB, hdir, huF, hvF⟩
  · rintro ⟨d, e, he, hnotB, hdir, huF, hvF⟩
    have hdsource : d.source ∈ F := by
      rcases hdir with h | h
      · rw [← h.1]; exact huF
      · rw [← h.2]; exact hvF
    have hdtarget : d.target ∈ F := by
      rcases hdir with h | h
      · rw [← h.2]; exact hvF
      · rw [← h.1]; exact huF
    have hsupport : e ∈ slitScreenActualClosedGraphSupport m F := by
      simp only [slitScreenActualClosedGraphSupport, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨d, hdsource, hdtarget, he⟩
    have hnotA : e ∉ A := by
      intro heA
      exact hnotB ((hagree e hsupport).mp heA)
    exact ⟨d, e, he, hnotA, hdir, huF, hvF⟩

/-- Reachability between any fixed endpoint sets depends only on the original
configuration's restriction to the carrier support. -/
theorem slitScreenActualReachability_iff_of_agree_on_support
    (m : ℕ) (F : Finset LatticeVertex)
    (A B : Configuration (slitBoxGraph (16 * m)))
    (S T : Set LatticeVertex)
    (hagree : ∀ e ∈ slitScreenActualClosedGraphSupport m F,
      (e ∈ A ↔ e ∈ B)) :
    (∃ x ∈ S, ∃ y ∈ T,
      (slitScreenActualConfigurationClosedDualGraph m A F).Reachable x y) ↔
    (∃ x ∈ S, ∃ y ∈ T,
      (slitScreenActualConfigurationClosedDualGraph m B F).Reachable x y) := by
  rw [slitScreenActualConfigurationClosedDualGraph_eq_of_agree_on_support
    m F A B hagree]

end PottsContinuity.FKC.FiniteFK
