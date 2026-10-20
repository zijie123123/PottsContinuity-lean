module

public import PottsContinuity.Thm3.Push.PushOfLocalConfinedSelectors
public import PottsContinuity.Thm3.RSW.Lemma4BandToSquareComposition
public import PottsContinuity.Thm3.RSW.AnnulusArmBound
public import PottsContinuity.Thm3.Prop4.StretchedSummability
public import PottsContinuity.Thm3.RSW.Prop3Geometry

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology
noncomputable section

section
variable (q : Set.Ici (1:ℝ))
    (hchoices : ∀ n : ℕ, ∀ hn : 13 ≤ n, Push.RoundedLocalConfinedPrefixSelectorExists n hn)
    (hbandToSquare : ∀ n : ℕ, 1 ≤ n →
      (measure (lemma4AmbientGraph n) (selfDualParameters q)
        (BoundaryCondition.free ∅) (lemma4BandConstructionEvent n)).toReal ≤
      (1+(q:ℝ)^2)^3*(annulusProbability (selfDualParameters q) 8 n)^2)
include hchoices

/-- The source lower bound of eq. (13) from the local confined prefix-selector
hypothesis `hchoices`. The outer-circuit and strip-duality inputs are proved. -/
theorem selfDual_lemma4_source_band_lower_of_localPrefixSelectors :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c*annulusProbability (selfDualParameters q) 8 (7*n) ≤
        (measure (lemma4AmbientGraph n) (selfDualParameters q)
          (frozenBoundaryCondition (box (56*n)) 0) (lemma4BandConstructionEvent n)).toReal :=
  selfDual_lemma4_source_band_lower_of_stripRSW q
    (Push.selfDual_stripRSW_of_localConfinedPrefixSelectors q hchoices)

include hbandToSquare

end
end
end PottsContinuity.RSW
