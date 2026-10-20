module

public import PottsContinuity.Thm3.Push.IntervalArmStripWindowConnection

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- The product of the actual finite-window arm marginals gives the EXACT
finite-window local-event probability bound on the specified closed extension. -/
theorem stripWindow_intervalArm_connection_probability_ge_product
    (q : Set.Ici (1 : ℝ)) (n m s : ℕ) (hs : 1 ≤ s) (hscale : 7*s < 2*n) (x : ℤ)
    (hlo : -(m : ℤ) ≤ x) (hhi : x+2*(n : ℤ) ≤ (m : ℤ)) :
    ((measure (PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set LatticeVertex))
      (criticalParameters q) (RSW.stripWindowBoundary n m 0)
      {C | embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
        (intervalArmStripWindow_map_le n m x hlo hhi) C ∈
        intervalArmEvent (2*n) (4*(s : ℤ)) (5*(s : ℤ))}).toReal *
      (measure (PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set LatticeVertex))
        (criticalParameters q) (RSW.stripWindowBoundary n m 0)
        {C | embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
          (intervalArmStripWindow_map_le n m x hlo hhi) C ∈
          intervalArmEvent (2*n) (6*(s : ℤ)) (7*(s : ℤ))}).toReal) / (1+(q : ℝ)^2) ≤
      RSW.stripWindowEventProbability (RSW.selfDualParameters q) n m (RSW.stripLocalConnection n s x) := by
  apply le_trans (intervalArmPair_embedded_connection_probability_ge_product q (2*n) (by omega)
    (4*(s : ℤ)) (5*(s : ℤ)) (6*(s : ℤ)) (7*(s : ℤ))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) _
    (intervalArmStripWindowEmbedding n m x hlo hhi) (intervalArmStripWindow_map_le n m x hlo hhi)
    (RSW.stripWindowBoundary n m 0))
  exact intervalArmStripWindow_connection_probability_le_local (criticalParameters q) n m s x hlo hhi

end
end PottsContinuity.Push
