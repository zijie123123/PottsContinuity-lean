module

public import PottsContinuity.Thm3.Push.DirectPrefixSystem
public import PottsContinuity.Thm3.Push.StripCaseTwoUniformArmBounds
public import PottsContinuity.Thm3.Push.StripCaseOneArmPreparation
public import PottsContinuity.Thm3.Push.StripSourceCaseSplit
public import PottsContinuity.Thm3.StripDual.PrimalVertical

@[expose] public section

namespace PottsContinuity.Push
open RSW PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance directPrefixRoundedLocalEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The Case 2 source alternative supplies the rounded local bound at every
offset using a physical direct-prefix system. Actual arm bounds are proved. -/
theorem directPrefixSystem_rounded_local_of_left
    (q : Set.Ici (1:ℝ)) (n k : ℕ) (hn : 13 ≤ n) (hk : 1 ≤ k)
    (D : RoundedDirectPrefixSystem n hn)
    (hleft : (1/(36*(k:ℝ)))/3 ≤ (selfDualStripMeasure q n).real
      (stripSourceSquareEvent n 0 (sourceSquareSideArmEvent (2*n)
        (4*(((n+8)/9:ℕ):ℤ)) (5*(((n+8)/9:ℕ):ℤ)) 0 (9*(((n+8)/9:ℕ):ℤ)) 0))) :
    ∀ x : ℤ, stripLocalLower q k ≤
      (selfDualStripMeasure q n).real (stripLocalConnection n ((n+8)/9) x) := by
  have harms := selfDual_strip_rounded_case_two_arm_bounds_all_offsets_of_left q n k (by omega) hleft
  intro x
  simpa only [stripLocalLower] using
    strip_caseTwoCompleteSource_lower_of_prefixLocality_and_sourcePaths n ((n+8)/9)
      (by omega) ((rounded_source_both_rectangles_fit n (by omega) (by omega)).1)
      q D.selectPrefix D.locality D.search D.paths x (1/(36*(k:ℝ))) (by positivity)
      (harms x).1 (harms x).2

/-- Both source alternatives give the rounded local lower bound. Strip
self-dual reflection is discharged by the proved physical duality provider. -/
theorem directPrefixSystem_rounded_local_of_small_horizontal
    (q : Set.Ici (1:ℝ)) (n k : ℕ) (hn : 13 ≤ n) (hk : 1 ≤ k)
    (D : RoundedDirectPrefixSystem n hn)
    (hsmall : selfDualStripHorizontalProbability q k n < 1/2) :
    ∀ x : ℤ, stripLocalLower q k ≤
      (selfDualStripMeasure q n).real (stripLocalConnection n ((n+8)/9) x) := by
  have hvertical := StripDual.selfDual_strip_primal_vertical_lower_of_small_horizontal
    q k n hk (by omega) hsmall
  obtain ⟨hs,hns,_⟩ := strip_ceil_ninth_spacing n (by omega)
  have hfit := rounded_source_translated_rectangles_fit n (by omega : 11 ≤ n)
  rcases selfDual_strip_source_case_split_of_verticalLower q k n ((n+8)/9) hk hs hns
    (by omega) hvertical with htop | hleft
  · exact selfDual_strip_rounded_case_one_local_lower_all_offsets_of_top q n k (by omega) hk htop
  · exact directPrefixSystem_rounded_local_of_left q n k hn hk D hleft

end
end PottsContinuity.Push
