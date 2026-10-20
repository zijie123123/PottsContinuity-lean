module

public import PottsContinuity.Thm4.SideBoundary
public import PottsContinuity.PD.FK.Events
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSideConnectionPositive

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The literal positive vertical side vertex, retained on sheet zero. -/
def coverPositiveVerticalVertex (n : ℕ) (hn : 1 ≤ n) : ParafermionicAmbientVertex n :=
  ⟨(((0 : ℤ), (n : ℤ)), (0 : ℤ)),
    (Finset.mem_filter.mp
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverSideBoundary_positiveVertical_mem n hn)).1⟩

theorem coverPositiveVerticalVertex_mem (n : ℕ) (hn : 1 ≤ n) :
    coverPositiveVerticalVertex n hn ∈ coverSideBoundary n := by
  classical
  have h := PottsContinuity.FKC.FiniteFK.parafermionicCoverSideBoundary_positiveVertical_mem n hn
  rw [← coverSideBoundary_image n] at h
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp h
  have heq' : v = coverPositiveVerticalVertex n hn := Subtype.ext heq
  rwa [← heq']

/-- Positivity for the fixed vertical side vertex holds for every real q>=1.
It uses nonemptiness of the actual event and full support of the finite law. -/
theorem coverPositiveVerticalVertex_probability_pos (n : ℕ) (hn : 1 ≤ n)
    (q : Set.Ici (1 : ℝ)) :
    0 < coverOriginConnectionProbability n q (coverPositiveVerticalVertex n hn) := by
  let q₁ : PottsContinuity.FKC.ClusterWeight := ⟨1, by norm_num⟩
  have h := PottsContinuity.FKC.FiniteFK.parafermionicCoverSideBoundary_positiveVertical_connectionWeight
    n hn q₁
  change 0 < PottsContinuity.FKC.FiniteFK.parafermionicCoverBoxOriginConnectionWeight
    n q₁ (coverPositiveVerticalVertex n hn).val at h
  rw [fkc_coverOriginConnectionWeight_eq] at h
  have hpos := (ENNReal.toReal_pos_iff.mp h).1
  have hne := (measure_pos_iff (ParafermionicAmbientGraph n)
    (selfDualParameters ⟨q₁, q₁.2.1⟩)
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
    {A | ActualConnected (ParafermionicAmbientGraph n) A (parafermionicCoverBoxOrigin n)
      (coverPositiveVerticalVertex n hn)}).mp hpos
  apply ENNReal.toReal_pos
  · exact ne_of_gt ((measure_pos_iff (ParafermionicAmbientGraph n) (selfDualParameters q)
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) _).mpr hne)
  · exact measure_ne_top _ _

end
end PottsContinuity.Thm4
