module

public import PottsContinuity.Thm3.RSW.StripVerticalSeed
public import PottsContinuity.Thm3.RSW.SelfDualSetup
public import PottsContinuity.Thm3.RSW.StripReflectedMarginalSeed
public import PottsContinuity.Thm3.StripDual.ReflectedMarginal

@[expose] public section

namespace PottsContinuity.StripDual

open PottsContinuity.RSW

theorem selfDual_strip_primal_vertical_lower_of_small_horizontal
    (q : Set.Ici (1:ℝ)) (k n : ℕ) (_hk : 1 ≤ k) (hn : 1 ≤ n)
    (hsmall : selfDualStripHorizontalProbability q k n < 1/2) :
    (1/2:ℝ) ≤ (selfDualStripMeasure q n).real
      (stripVerticalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) (2*n)) := by
  exact selfDual_stripCentral_vertical_lower_of_reflectedMarginal q k n hn
    (selfDual_strip_reflected_marginal q k n hn) hsmall

end PottsContinuity.StripDual
