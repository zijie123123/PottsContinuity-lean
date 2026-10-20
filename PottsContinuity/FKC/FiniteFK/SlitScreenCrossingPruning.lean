-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitScreenCrossingPruning.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.PortCrossingBoundaryPruning
public import PottsContinuity.FKC.FiniteFK.SlitScreenDualEdgeClassification

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

/-- The actual whole-plane closed-dual graph with both endpoints restricted to
an explicit finite face-base carrier, represented on the ambient vertex type. -/
def slitScreenClosedDualInducedGraph (ω : LatticeConfiguration)
    (F : Finset LatticeVertex) : SimpleGraph LatticeVertex where
  Adj u v := (wholePlaneClosedDualGraph ω).Adj u v ∧ u ∈ F ∧ v ∈ F
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  ⟩
  loopless := ⟨by
    intro u h
    exact (wholePlaneClosedDualGraph ω).irrefl h.1
  ⟩

/-- Restrict the same closed-dual bonds to those crossing an edge of the actual
slit graph. This retains the ambient carrier and only changes the edge set. -/
def slitScreenSlitRestrictedGraph (ω : LatticeConfiguration) (m : ℕ)
    (F : Finset LatticeVertex) : SimpleGraph LatticeVertex where
  Adj u v := ∃ d : LatticeBond,
    latticeConfigurationBondState ω (primalBondOfDual d) = false ∧
      (u = d.source ∧ v = d.target ∨ u = d.target ∧ v = d.source) ∧
      u ∈ F ∧ v ∈ F ∧
      slitScreenPrimalBondInSlit (16 * m) (primalBondOfDual d)
  symm := ⟨by
    intro u v h
    rcases h with ⟨d, hc, huv, huF, hvF, hs⟩
    rcases huv with huv | huv
    · exact ⟨d, hc, Or.inr ⟨huv.2, huv.1⟩, hvF, huF, hs⟩
    · exact ⟨d, hc, Or.inl ⟨huv.2, huv.1⟩, hvF, huF, hs⟩
  ⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨d, hc, huv, _, _, _⟩
    exact (wholePlaneClosedDualGraph ω).irrefl
      ((wholePlaneClosedDualGraph_adj_iff_dualBond ω u u).mpr ⟨d, hc, huv⟩)
  ⟩

def slitScreenBottomTerminals (m : ℕ) (F : Finset LatticeVertex) :
    Set LatticeVertex := {v | v ∈ F ∧ v.2 = -(16 * (m : ℤ)) - 1}

def slitScreenTopTerminals (m : ℕ) (F : Finset LatticeVertex) :
    Set LatticeVertex := {v | v ∈ F ∧ v.2 = 16 * (m : ℤ)}

private theorem slitScreenGraph_edge_iff_dualBond
    (ω : LatticeConfiguration) (F : Finset LatticeVertex) (u v : LatticeVertex) :
    (slitScreenClosedDualInducedGraph ω F).Adj u v ↔
      ∃ d : LatticeBond,
        latticeConfigurationBondState ω (primalBondOfDual d) = false ∧
          (u = d.source ∧ v = d.target ∨ u = d.target ∧ v = d.source) ∧
          u ∈ F ∧ v ∈ F := by
  constructor
  · rintro ⟨h, hu, hv⟩
    rcases (wholePlaneClosedDualGraph_adj_iff_dualBond ω u v).mp h with
      ⟨d, hc, huv⟩
    exact ⟨d, hc, huv, hu, hv⟩
  · rintro ⟨d, hc, huv, hu, hv⟩
    exact ⟨(wholePlaneClosedDualGraph_adj_iff_dualBond ω u v).mpr
      ⟨d, hc, huv⟩, hu, hv⟩

private theorem slitScreenSlitRestricted_le_induced
    (ω : LatticeConfiguration) (m : ℕ) (F : Finset LatticeVertex) :
    slitScreenSlitRestrictedGraph ω m F ≤ slitScreenClosedDualInducedGraph ω F := by
  intro u v h
  rcases h with ⟨d, hc, huv, hu, hv, _⟩
  exact (slitScreenGraph_edge_iff_dualBond ω F u v).mpr ⟨d, hc, huv, hu, hv⟩

private theorem slitScreenBoundary_edges_internal
    (m : ℕ) (F : Finset LatticeVertex) (d : LatticeBond)
    (hs : d.source ∈ F) (ht : d.target ∈ F)
    (hbd : d.axis = .horizontal ∧
      (d.base.2 = -(16 * (m : ℤ)) - 1 ∨ d.base.2 = 16 * (m : ℤ))) :
    d.source ∈ slitScreenBottomTerminals m F ∧
      d.target ∈ slitScreenBottomTerminals m F ∨
    d.source ∈ slitScreenTopTerminals m F ∧
      d.target ∈ slitScreenTopTerminals m F := by
  rcases d with ⟨⟨x, y⟩, ax⟩
  rcases hbd with ⟨hax, hy⟩
  cases ax
  · simp only [LatticeBond.source, LatticeBond.target, slitScreenBottomTerminals,
      slitScreenTopTerminals] at hs ht ⊢
    rcases hy with hy | hy
    · exact Or.inl ⟨⟨hs, by simpa using hy⟩, ⟨ht, by simpa using hy⟩⟩
    · exact Or.inr ⟨⟨hs, by simpa using hy⟩, ⟨ht, by simpa using hy⟩⟩
  · simp at hax

private theorem slitScreen_crossing_iff_of_classification
    (ω : LatticeConfiguration) (m : ℕ) (F : Finset LatticeVertex)
    (hclass : ∀ (d : LatticeBond), d.source ∈ F → d.target ∈ F →
      (slitScreenPrimalBondInSlit (16 * m) (primalBondOfDual d) ↔
        ¬ (d.axis = .horizontal ∧
          (d.base.2 = -(16 * (m : ℤ)) - 1 ∨ d.base.2 = 16 * (m : ℤ))))) :
    (∃ x ∈ slitScreenBottomTerminals m F, ∃ y ∈ slitScreenTopTerminals m F,
      (slitScreenClosedDualInducedGraph ω F).Reachable x y) ↔
    (∃ x ∈ slitScreenBottomTerminals m F, ∃ y ∈ slitScreenTopTerminals m F,
      (slitScreenSlitRestrictedGraph ω m F).Reachable x y) := by
  apply reachable_between_sets_iff_of_retain_edges
    (slitScreenSlitRestricted_le_induced ω m F)
  intro u v huv hnotBottom hnotTop
  rcases (slitScreenGraph_edge_iff_dualBond ω F u v).mp huv with
    ⟨d, hc, hdir, huF, hvF⟩
  have hs : d.source ∈ F := by
    rcases hdir with h | h
    · rw [← h.1]
      exact huF
    · rw [← h.2]
      exact hvF
  have ht : d.target ∈ F := by
    rcases hdir with h | h
    · rw [← h.2]
      exact hvF
    · rw [← h.1]
      exact huF
  have hclassified' := hclass d hs ht
  have hkept : slitScreenPrimalBondInSlit (16 * m) (primalBondOfDual d) := by
    apply hclassified'.mpr
    intro hbd
    have hedge := slitScreenBoundary_edges_internal m F d hs ht hbd
    rcases hdir with hdir | hdir
    · rcases hedge with hbottom | htop
      · exact hnotBottom ⟨by rw [hdir.1]; exact hbottom.1,
          by rw [hdir.2]; exact hbottom.2⟩
      · exact hnotTop ⟨by rw [hdir.1]; exact htop.1,
          by rw [hdir.2]; exact htop.2⟩
    · rcases hedge with hbottom | htop
      · exact hnotBottom ⟨by rw [hdir.1]; exact hbottom.2,
          by rw [hdir.2]; exact hbottom.1⟩
      · exact hnotTop ⟨by rw [hdir.1]; exact htop.2,
          by rw [hdir.2]; exact htop.1⟩
  exact ⟨d, hc, hdir, huF, hvF, hkept⟩

/-- For the actual right tall screen, deleting closed-dual edges whose crossed
primal bond is outside the slit graph preserves bottom-to-top connectivity. -/
theorem slitScreenRightCrossing_iff_slitRestricted
    (ω : LatticeConfiguration) (m : ℕ) (hm : 1 ≤ m) :
    (∃ x ∈ slitScreenBottomTerminals m (slitScreenRightFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenRightFaceBases m),
      (slitScreenClosedDualInducedGraph ω (slitScreenRightFaceBases m)).Reachable x y) ↔
    (∃ x ∈ slitScreenBottomTerminals m (slitScreenRightFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenRightFaceBases m),
      (slitScreenSlitRestrictedGraph ω m (slitScreenRightFaceBases m)).Reachable x y) := by
  exact slitScreen_crossing_iff_of_classification ω m (slitScreenRightFaceBases m)
    (fun d hs ht => slitScreenRightFaceBond_primalBondInSlit_iff m hm d hs ht)

/-- The same deterministic crossing invariance for the actual left tall screen. -/
theorem slitScreenLeftCrossing_iff_slitRestricted
    (ω : LatticeConfiguration) (m : ℕ) (hm : 1 ≤ m) :
    (∃ x ∈ slitScreenBottomTerminals m (slitScreenLeftFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenLeftFaceBases m),
      (slitScreenClosedDualInducedGraph ω (slitScreenLeftFaceBases m)).Reachable x y) ↔
    (∃ x ∈ slitScreenBottomTerminals m (slitScreenLeftFaceBases m),
      ∃ y ∈ slitScreenTopTerminals m (slitScreenLeftFaceBases m),
      (slitScreenSlitRestrictedGraph ω m (slitScreenLeftFaceBases m)).Reachable x y) := by
  exact slitScreen_crossing_iff_of_classification ω m (slitScreenLeftFaceBases m)
    (fun d hs ht => slitScreenLeftFaceBond_primalBondInSlit_iff m hm d hs ht)

end PottsContinuity.FKC.FiniteFK
