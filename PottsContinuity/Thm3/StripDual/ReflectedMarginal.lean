module

public import PottsContinuity.Thm3.RSW.StripReflectedMarginalFiniteRead
public import PottsContinuity.Thm3.RSW.StripCentralPrunedReflection

@[expose] public section

namespace PottsContinuity.StripDual

open PottsContinuity.RSW
open PottsContinuity.PD.FK
open MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

theorem selfDual_strip_reflected_marginal
    (q : Set.Ici (1 : ℝ)) (k n : ℕ) (hn : 1 ≤ n) :
    Measure.map (stripCentralDualConfiguration n k) (selfDualStripMeasure q n) =
      Measure.map (stripReflectedCentralDualConfiguration n k hn) (selfDualStripMeasure q n) := by
  let read := fun M
      (C : Configuration
        (PottsContinuity.DualityExt.rectangleSubgraphDualGraph
          (stripRectangleWithoutTop_map_le n M))) =>
    if hM : k*n+1 ≤ M then
      stripCentralPrunedDualRead n k M hn hM C
    else
      (∅ : Configuration (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)))
  have hsource : ∀ M : ℕ, k*n+1 ≤ M →
      ∀ C : Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))),
        read M (stripWindowPrunedDualConfiguration n M C) =
          stripCentralDualConfiguration n k (stripWindowOriginalRead n M C) := by
    intro M hM C
    simp only [read, dite_eq_left hM]
    exact stripCentralPrunedDualRead_source n k M hn hM C
  have hreflect : ∀ M : ℕ, k*n+1 ≤ M →
      ∀ C : Configuration (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)),
        read M (stripAsymmetricPrunedDualRead n M C) =
          stripReflectedCentralDualConfiguration n k hn (stripAsymmetricCenteredRead n M C) := by
    intro M hM C
    simp only [read, dite_eq_left hM]
    exact stripCentralPrunedDualRead_reflected n k M hn hM C
  exact selfDual_strip_reflected_marginal_of_finiteRead n k hn
    read hsource hreflect
    q

end

end PottsContinuity.StripDual
