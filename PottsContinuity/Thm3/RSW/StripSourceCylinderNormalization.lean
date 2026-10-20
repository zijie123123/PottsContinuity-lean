module

public import PottsContinuity.Thm3.RSW.StripNormalizedPatternRead

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology FKC.Medial
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Original edges required open by the literal source cylinder, translated
physically to the normalized strip without changing their states. -/
def stripNormalizedOpenPattern (n : ℕ) (A : Finset (stripGraph n).edgeSet)
    (ξ : StripConfiguration n) : Finset FKC.squareLattice.edgeSet := by
  classical
  exact (A.filter (fun e => ξ e=true)).image (stripNormalizedEmbedding n).mapEdgeSet

/-- Original edges required closed by the same literal source cylinder. -/
def stripNormalizedClosedPattern (n : ℕ) (A : Finset (stripGraph n).edgeSet)
    (ξ : StripConfiguration n) : Finset FKC.squareLattice.edgeSet := by
  classical
  exact (A.filter (fun e => ξ e=false)).image (stripNormalizedEmbedding n).mapEdgeSet

/-- Every source pattern is eventually supported by one fixed normalized
central window, including both its open and closed requirements. -/
theorem stripNormalizedPattern_exists_support (n : ℕ) (A : Finset (stripGraph n).edgeSet)
    (ξ : StripConfiguration n) :
    ∃ K : ℕ,
      (∀ e ∈ stripNormalizedOpenPattern n A ξ,
        e ∈ Set.range (horizontalStripRectangleOriginalEdge K (2*n))) ∧
      (∀ e ∈ stripNormalizedClosedPattern n A ξ,
        e ∈ Set.range (horizontalStripRectangleOriginalEdge K (2*n))) := by
  classical
  obtain ⟨K,hK⟩ := (eventually_stripWindow_finset_edge_lift n A).exists
  have hs : ∀ e ∈ A, (stripNormalizedEmbedding n).mapEdgeSet e ∈
      Set.range (horizontalStripRectangleOriginalEdge K (2*n)) := by
    intro e he
    obtain ⟨f,hf⟩ := hK e he
    exact ⟨configurationIsoEdgeEquiv (stripWindowCutIso n K) f,
      stripNormalizedEmbedding_window_edge n K e f hf⟩
  refine ⟨K,?_,?_⟩
  all_goals
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact hs f (Finset.mem_filter.mp hf).1

/-- The literal source finite cylinder is exactly the normalized full
open/closed pattern on every window containing its original bonds. -/
theorem stripWindowCylinder_normalized_pattern_iff (n M : ℕ)
    (A : Finset (stripGraph n).edgeSet) (ξ : StripConfiguration n)
    (hsupp : ∀ e ∈ A, ∃ f : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet,
      Sym2.map Subtype.val f.val = Sym2.map Subtype.val e.val)
    (C : Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)))) :
    stripWindowCylinder n M A ξ ((boolConfigurationEquiv _).symm C) ↔
      configurationIso (stripWindowCutIso n M) C ∈
        stripRectanglePatternEvent M (2*n)
          (stripNormalizedOpenPattern n A ξ) (stripNormalizedClosedPattern n A ξ) := by
  classical
  let E := (configurationIso (stripWindowCutIso n M) C).image
    (horizontalStripRectangleOriginalEdge M (2*n))
  have hstate : ∀ e ∈ A,
      (∃ f : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet,
        Sym2.map Subtype.val f.val = Sym2.map Subtype.val e.val ∧
        (boolConfigurationEquiv _).symm C f = ξ e) ↔
        ((stripNormalizedEmbedding n).mapEdgeSet e ∈ E ↔ ξ e=true) := by
    intro e he
    obtain ⟨f,hf⟩ := hsupp e he
    have hopen := stripNormalizedEmbedding_open_iff n M e f hf C
    have hu : ∀ g : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet,
        Sym2.map Subtype.val g.val = Sym2.map Subtype.val e.val → g=f := by
      intro g hg
      apply (stripWindowPlaneEmbedding n M).mapEdgeSet.injective
      exact Subtype.ext (hg.trans hf.symm)
    have hread : (boolConfigurationEquiv _).symm C f = ξ e ↔
        (f ∈ C ↔ ξ e=true) := by
      simp only [boolConfigurationEquiv, Equiv.coe_fn_symm_mk]
      cases ξ e <;> simp
    constructor
    · rintro ⟨g,hg,hgstate⟩
      rw [hu g hg] at hgstate
      exact hopen.trans (hread.mp hgstate)
    · intro h
      exact ⟨f,hf,hread.mpr (hopen.symm.trans h)⟩
  have hforall : stripWindowCylinder n M A ξ ((boolConfigurationEquiv _).symm C) ↔
      ∀ e ∈ A, ((stripNormalizedEmbedding n).mapEdgeSet e ∈ E ↔ ξ e=true) := by
    unfold stripWindowCylinder
    exact forall_congr' fun e => forall_congr' fun he => hstate e he
  rw [hforall]
  change (∀ e ∈ A, ((stripNormalizedEmbedding n).mapEdgeSet e ∈ E ↔ ξ e=true)) ↔
    stripNormalizedOpenPattern n A ξ ⊆ E ∧ Disjoint (stripNormalizedClosedPattern n A ξ) E
  constructor
  · intro h
    constructor
    · intro e he
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      exact (h f (Finset.mem_filter.mp hf).1).mpr (Finset.mem_filter.mp hf).2
    · apply Finset.disjoint_left.mpr
      intro e he heE
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      have htrue := (h f (Finset.mem_filter.mp hf).1).mp heE
      have hfalse := (Finset.mem_filter.mp hf).2
      simp only [hfalse, Bool.false_eq_true] at htrue
  · rintro ⟨ho,hc⟩ e he
    constructor
    · intro heE
      cases hξ : ξ e
      · have hf : (stripNormalizedEmbedding n).mapEdgeSet e ∈ stripNormalizedClosedPattern n A ξ :=
          Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hξ⟩,rfl⟩
        exact False.elim (Finset.disjoint_left.mp hc hf heE)
      · rfl
    · intro hξ
      exact ho (Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hξ⟩,rfl⟩)

/-- Exact probability identity for the original finite source-cylinder read. -/
theorem stripWindowCylinderProbability_normalized_pattern
    (θ : Parameters) (n M : ℕ) (i : Fin 2)
    (A : Finset (stripGraph n).edgeSet) (ξ : StripConfiguration n)
    (hsupp : ∀ e ∈ A, ∃ f : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet,
      Sym2.map Subtype.val f.val = Sym2.map Subtype.val e.val) :
    stripWindowCylinderProbability θ n i M A ξ =
      (measure (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) θ (stripWindowBoundary n M i)
        ((configurationIso (stripWindowCutIso n M)) ⁻¹'
          stripRectanglePatternEvent M (2*n)
            (stripNormalizedOpenPattern n A ξ) (stripNormalizedClosedPattern n A ξ))).toReal := by
  have hset : finiteBoolEvent (stripWindow n M) (stripWindowCylinder n M A ξ) =
      (configurationIso (stripWindowCutIso n M)) ⁻¹'
        stripRectanglePatternEvent M (2*n)
          (stripNormalizedOpenPattern n A ξ) (stripNormalizedClosedPattern n A ξ) := by
    ext C
    exact stripWindowCylinder_normalized_pattern_iff n M A ξ hsupp C
  unfold stripWindowCylinderProbability finiteBoundaryEventProbability
  rw [hset]

end
end PottsContinuity.RSW
