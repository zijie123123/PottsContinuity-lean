module

public import PottsContinuity.Thm4.ExtremalConnectionMass
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSideBoundary

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Full actual exterior-neighbor boundary restricted to interior sheets. -/
def coverSideBoundary (n : ℕ) : Finset (ParafermionicAmbientVertex n) :=
  (coverExteriorBoundary n).filter fun v =>
    -((n ^ 5 : ℕ) : ℤ) < v.val.2 ∧ v.val.2 < ((n ^ 5 : ℕ) : ℤ)

theorem coverSideBoundary_image (n : ℕ) :
    (coverSideBoundary n).image Subtype.val =
      PottsContinuity.FKC.parafermionicCoverExteriorNeighborBoundary n := by
  classical
  ext v
  simp only [Finset.mem_image, coverSideBoundary, coverExteriorBoundary,
    PottsContinuity.FKC.parafermionicCoverExteriorNeighborBoundary,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, ⟨⟨w, hw, hout⟩, hk⟩, rfl⟩
    refine ⟨u.property, hk.1, hk.2, w, ?_, hout⟩
    rwa [fkc_coverGraph_eq] at hw
  · rintro ⟨hv, hlo, hhi, w, hw, hout⟩
    refine ⟨⟨v, hv⟩, ⟨⟨w, ?_, hout⟩, hlo, hhi⟩, rfl⟩
    rwa [fkc_coverGraph_eq]

theorem coverSideBoundary_card_le (n : ℕ) (hn : 1 ≤ n) :
    (coverSideBoundary n).card ≤ 36 * n^6 := by
  classical
  have hc : ((coverSideBoundary n).image Subtype.val).card = (coverSideBoundary n).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  rw [coverSideBoundary_image n] at hc
  rw [← hc]
  exact PottsContinuity.FKC.parafermionicCoverExteriorNeighborBoundary_card_le n hn

/-- Full boundary connection mass is bounded by its interior-sheet part plus
the two full extremal-sheet masses. Adapted from FKC ParafermionicCoverBoundarySums. -/
theorem cover_boundary_connection_sum_le_side_add_extremal
    (q : Set.Icc (1 : ℝ) 4) (n : ℕ) :
    (∑ v ∈ coverExteriorBoundary n, coverOriginConnectionProbability n ⟨q, q.2.1⟩ v) ≤
      (∑ v ∈ coverSideBoundary n, coverOriginConnectionProbability n ⟨q, q.2.1⟩ v) +
        coverExtremalConnectionMass n q := by
  classical
  let I := coverSideBoundary n
  let E : Finset (ParafermionicAmbientVertex n) :=
    PottsContinuity.FKC.FiniteFK.parafermionicCoverExtremalSheetVertices n
  let f := coverOriginConnectionProbability n ⟨q, q.2.1⟩
  have hsubset : coverExteriorBoundary n ⊆ I ∪ E := by
    intro v hv
    by_cases hi : -((n ^ 5 : ℕ) : ℤ) < v.val.2 ∧ v.val.2 < ((n ^ 5 : ℕ) : ℤ)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hi⟩)
    · apply Finset.mem_union_right
      apply (PottsContinuity.FKC.FiniteFK.mem_parafermionicCoverExtremalSheetVertices n v).mpr
      have hb := (parafermionicCoverBoxVertices_mem n v.val).mp v.property
      omega
  have hsum : (∑ v ∈ coverExteriorBoundary n, f v) ≤ ∑ v ∈ I ∪ E, f v :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => ENNReal.toReal_nonneg)
  have hunion : (∑ v ∈ I ∪ E, f v) ≤ (∑ v ∈ I, f v) + ∑ v ∈ E, f v := by
    rw [← Finset.sum_sdiff (s₁ := I) (s₂ := I ∪ E) Finset.subset_union_left,
      Finset.union_sdiff_left]
    have hdiff : (∑ v ∈ E \ I, f v) ≤ ∑ v ∈ E, f v :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun _ _ _ => ENNReal.toReal_nonneg)
    linarith
  exact hsum.trans hunion

end
end PottsContinuity.Thm4
