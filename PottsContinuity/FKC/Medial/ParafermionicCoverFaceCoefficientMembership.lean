-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFaceCoefficientMembership.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceOrientedBoundary

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

/-- A selected positive dart has exactly its unique actual finite-face owner. -/
theorem parafermionicCoverFacePositiveDartCount_eq_indicator_of_dart
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (i : ParafermionicCoverFiniteFaceTopIndex n)
    (u v : ParafermionicCoverBoxVertex n)
    (hiv : (u.1, v.1) ∈ parafermionicCoverFiniteFaceDarts i.1) :
    parafermionicCoverFacePositiveDartCount S u v =
      if i ∈ S then 1 else 0 := by
  classical
  by_cases hi : i ∈ S
  · have hfilter :
        S.filter (fun j =>
          (u.1, v.1) ∈ parafermionicCoverFiniteFaceDarts j.1) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hj, hjdart⟩
        have hface := parafermionicCoverFiniteFaceDart_unique
          n i.2 j.2 hiv hjdart
        have hji : j = i := Subtype.ext hface.symm
        exact hji
      · intro hji
        subst j
        exact ⟨hi, hiv⟩
    rw [parafermionicCoverFacePositiveDartCount, hfilter]
    simp [hi]
  · have hfilter :
        S.filter (fun j =>
          (u.1, v.1) ∈ parafermionicCoverFiniteFaceDarts j.1) = ∅ := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hj, hjdart⟩
        have hface := parafermionicCoverFiniteFaceDart_unique
          n i.2 j.2 hiv hjdart
        have hji : j = i := Subtype.ext hface.symm
        exact (hi (hji ▸ hj)).elim
      · intro hj
        simp at hj
    rw [parafermionicCoverFacePositiveDartCount, hfilter]
    simp [hi]

/-- For two actual owners of opposite darts, the oriented coefficient is the
indicator difference of their selected-face memberships. -/
theorem parafermionicCoverFaceBoundaryCoefficient_eq_owner_indicator_sub
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (u v : ParafermionicCoverBoxVertex n)
    (hforward : (u.1, v.1) ∈ parafermionicCoverFiniteFaceDarts i.1)
    (hbackward : (v.1, u.1) ∈ parafermionicCoverFiniteFaceDarts j.1) :
    parafermionicCoverFaceBoundaryCoefficient S u v =
      (if i ∈ S then (1 : ℤ) else 0) - (if j ∈ S then 1 else 0) := by
  rw [parafermionicCoverFaceBoundaryCoefficient,
    parafermionicCoverFacePositiveDartCount_eq_indicator_of_dart S i u v hforward,
    parafermionicCoverFacePositiveDartCount_eq_indicator_of_dart S j v u hbackward]
  simp

/-- Under the two actual dart-owner witnesses, zero coefficient is exactly
agreement of the selected memberships of those owners. -/
theorem parafermionicCoverFaceBoundaryCoefficient_eq_zero_iff_owner_mem_iff
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (u v : ParafermionicCoverBoxVertex n)
    (hforward : (u.1, v.1) ∈ parafermionicCoverFiniteFaceDarts i.1)
    (hbackward : (v.1, u.1) ∈ parafermionicCoverFiniteFaceDarts j.1) :
    parafermionicCoverFaceBoundaryCoefficient S u v = 0 ↔
      (i ∈ S ↔ j ∈ S) := by
  rw [parafermionicCoverFaceBoundaryCoefficient_eq_owner_indicator_sub
    S i j u v hforward hbackward]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]

end PottsContinuity.FKC.Medial
