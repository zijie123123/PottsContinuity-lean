module

public import PottsContinuity.Thm3.RSW.StripEventLimit

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory Filter Topology

/-- Product bounds involving actual finite-window arm marginals pass to the
strip using their limits. Non-strict bounds on the limiting marginals need not
already hold in any finite window. -/
theorem strip_local_product_lower_of_window_arm_limits
    (q : Set.Ici (1:ℝ)) (n s : ℕ) (x : ℤ)
    (A B : ℕ → ℝ) (a b : ℝ)
    (hA : Tendsto A atTop (𝓝 a)) (hB : Tendsto B atTop (𝓝 b))
    (hproduct : ∀ᶠ m : ℕ in atTop, A m * B m / (1+(q:ℝ)^2) ≤
      RSW.stripWindowEventProbability (RSW.selfDualParameters q) n m (RSW.stripLocalConnection n s x)) :
    a*b/(1+(q:ℝ)^2) ≤
      (RSW.selfDualStripMeasure q n).real (RSW.stripLocalConnection n s x) := by
  have htarget := RSW.stripWindowEventProbability_tendsto (RSW.selfDualParameters q) n
    (RSW.selfDualStripMeasure q n) (RSW.selfDualStripMeasure_isLimit q n)
    (RSW.stripLocalConnection n s x) (RSW.stripConfinedConnection_isClopen _ _ _ _)
  exact le_of_tendsto_of_tendsto ((hA.mul hB).div_const _) htarget hproduct

end PottsContinuity.Push
