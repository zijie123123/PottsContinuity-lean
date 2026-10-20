module

public import PottsContinuity.Thm3.Touch.FiniteStripSymmetry
public import PottsContinuity.Thm3.RSW.FiniteBoundary

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open PottsContinuity
open PottsContinuity.Thm3.Prop4
open PottsContinuity.PD.FK
open PottsContinuity.RSW
open MeasureTheory

noncomputable section

local instance tiltedColumnConfigurationMeasurableSpace
    (n L : ℕ) (t : ℝ) : MeasurableSpace (Configuration (tiltedColumnGraph (2*n) L t)) :=
  configurationMeasurableSpace (tiltedColumnGraph (2*n) L t)

/-- The edge states after applying the finite point half-turn. -/
def tiltedColumnBooleanReflectionIso (n L : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ((tiltedColumnGraph (2*n) L t).edgeSet → Bool) ≃
      ((tiltedColumnGraph (2*n) L t).edgeSet → Bool) :=
  (boolConfigurationEquiv _).trans
    ((configurationIso (tiltedColumnReflectionIso (2*n) L t ht)).trans
      (boolConfigurationEquiv _).symm)

@[simp] theorem tiltedColumnBooleanReflectionIso_configuration
    (n L : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (ω : (tiltedColumnGraph (2*n) L t).edgeSet → Bool) :
    boolConfigurationEquiv _ (tiltedColumnBooleanReflectionIso n L t ht ω) =
      configurationIso (tiltedColumnReflectionIso (2*n) L t ht)
        (boolConfigurationEquiv _ ω) := by
  simp [tiltedColumnBooleanReflectionIso, Equiv.trans_apply]

end

end PottsContinuity.Thm3.Touch
