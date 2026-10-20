module

public import PottsContinuity.Thm3.RSW.FiniteDualScreen
public import PottsContinuity.Thm3.RSW.InducedAnnulusLaw

/-!
# The actual screened-annulus upper product in Lemma 4

This module defines the screened-annulus pair event of DCST eq.(16), for
simple-circuit screens with separation of the full inner boxes. Its localized
product bound is proved in `Thm3.RSW.OverlappingAnnulusScreens`
(`screenedAnnulusPair_probability_le_local_product_of_rightSeparation`) and
specialized in `Thm3.RSW.Lemma4ScreenUpper`. Constructing these screens from
horizontal and vertical dual crossings is not part of this module; the screened
bound is not used by the main theorems, whose band estimate for Lemma 4 is
`PlanarMixed.Lemma4Connectors.lemma4_band_to_square_bound`.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- The two actual source annuli, each shielded from the exterior of its
local finite set by a sampled closed-dual simple circuit. -/
def screenedAnnulusPairEvent (V U₁ U₂ : Finset (ℤ × ℤ))
    (z₁ z₂ : ℤ × ℤ) (n₁ n₂ : ℕ) :
    Set (Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :=
  {A | A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z₁ n₁) ∧
    A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z₂ n₂) ∧
    A ∈ dualCircuitScreenEvent V (vertexBoxRegion V z₁ (2*n₁)) (finiteVertexRegion U₁ V) ∧
    A ∈ dualCircuitScreenEvent V (vertexBoxRegion V z₂ (2*n₂)) (finiteVertexRegion U₂ V)}

end
end PottsContinuity.RSW
