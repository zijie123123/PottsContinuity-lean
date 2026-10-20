module

public import PottsContinuity.Thm4.SelfDualParameters
public import PottsContinuity.Foundations.EveryExhaustion

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm4Plane

open PottsContinuity

/-- At the explicit self-dual parameter, the free infinite-volume limit
exists with the frozen every-exhaustion definition. This assembles only the
parameter and measure-existence parts of Theorem 4. -/
theorem exists_self_dual_free_limit (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4) :
    ∃ (p : Set.Icc (0 : ℝ) 1)
      (μ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q) ∧
      IsRCInfiniteVolumeLimit p ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 0 μ := by
  let qI : Set.Ici (1 : ℝ) := ⟨q, hq.1⟩
  let qpos : Set.Ioi (0 : ℝ) := ⟨q, lt_of_lt_of_le one_pos hq.1⟩
  let θ := PottsContinuity.Thm4.selfDualParameters qI
  let p : Set.Icc (0 : ℝ) 1 :=
    ⟨θ.edgeProbability.val,
      ⟨θ.edgeProbability.property.1.le, θ.edgeProbability.property.2.le⟩⟩
  have hp : (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q) := by
    change θ.edgeProbability.val = Real.sqrt q / (1 + Real.sqrt q)
    exact PottsContinuity.Thm4.selfDualParameters_edgeParameter qI
  obtain ⟨μ, hμ⟩ :=
    Foundations.exists_isRCInfiniteVolumeLimit p qpos hq.1 0
  exact ⟨p, μ, hp, by simpa [qpos] using hμ⟩

end PottsContinuity.Thm4Plane
