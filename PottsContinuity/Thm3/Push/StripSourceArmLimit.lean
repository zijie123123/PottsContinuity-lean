module

public import PottsContinuity.Thm3.Push.StripSourceWindowStates
public import PottsContinuity.Thm3.Push.SourceSideArm
public import PottsContinuity.Thm3.Push.OpenStateEmbedding

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory Filter Topology
noncomputable section

/-- The first source Case 2 arm, read on the original translated strip bonds. -/
abbrev stripCaseTwoFirstArm (n s : ℕ) (x : ℤ) :=
  stripSourceSquareEvent n x (sourceCaseTwoFirstArm n s)

/-- The second source Case 2 arm, with its full R' confinement retained. -/
abbrev stripCaseTwoSecondArm (n s : ℕ) (x : ℤ) :=
  stripSourceSquareEvent n x (sourceCaseTwoSecondArm n s)

/-- Actual finite-window probabilities of every source cylinder converge to
its probability under the genuine strip limit, for independent FK parameters. -/
theorem stripSourceSquareEvent_window_probability_tendsto
    (θ : Parameters) (n : ℕ) (x : ℤ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (E : Set (Configuration (rectangleGraph (0,0) (2*n) (2*n)))) :
    Tendsto (fun m => RSW.stripWindowEventProbability θ n m (stripSourceSquareEvent n x E))
      atTop (𝓝 (μ.real (stripSourceSquareEvent n x E))) := by
  exact RSW.stripWindowEventProbability_tendsto θ n μ hμ _ (stripSourceSquareEvent_isClopen n x E)

/-- Every fixed translated source square is contained in all sufficiently
wide strip windows; the threshold is explicit and independent of the sample. -/
theorem eventually_stripWindow_contains_sourceSquare (n : ℕ) (x : ℤ) :
    ∀ᶠ m : ℕ in atTop, -(m:ℤ) ≤ x ∧ x+2*(n:ℤ) ≤ (m:ℤ) := by
  have hlo : -(x.natAbs:ℤ) ≤ x := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le x
  have hhi : x ≤ (x.natAbs:ℤ) := by
    rw [Int.natCast_natAbs]
    exact le_abs_self x
  filter_upwards [eventually_ge_atTop (x.natAbs+2*n)] with m hm
  constructor <;> omega

end
end PottsContinuity.Push
