module

public import PottsContinuity.BD12.WholePlaneDuality
public import PottsContinuity.PD.RCInfinite.ClusterEvents

/-! Explicit independent inputs to the reverse genuine-threshold assembly. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite

/-- Full planar non-coexistence: no translation-invariant probability measure that is
positively associated on measurable increasing events has, almost surely, a unique
infinite cluster both in the configuration and in its whole-plane dual. -/
def PlanarNonCoexistenceContract : Prop :=
  ∀ (μ : Measure LatticeConfiguration), IsProbabilityMeasure μ →
    (∀ a : LatticeVertex, μ.map (latticeConfigurationTranslate a) = μ) →
    (∀ A B : Set LatticeConfiguration,
      MeasurableSet A → MeasurableSet B → IsUpperSet A → IsUpperSet B →
        μ A * μ B ≤ μ (A ∩ B)) →
    (∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω ∧ ω ∈ infiniteClusterEvent) →
    (∀ᵐ ω ∂μ,
      atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω) ∧
      wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent) → False

/-- Dense coincidence: every interior open interval contains coincident free and wired
frozen limits. No threshold, percolation or duality conclusion is included. -/
def DenseCoincidenceContract (q : Set.Ici (1 : ℝ)) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 →
    ∃ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo a b ∧
      ∃ μ₀ μ₁ : Measure LatticeConfiguration,
        IsRCInfiniteVolumeLimit t
          ⟨(q : ℝ), (show (0 : ℝ) < q from lt_of_lt_of_le one_pos q.property)⟩ 0 μ₀ ∧
        IsRCInfiniteVolumeLimit t
          ⟨(q : ℝ), (show (0 : ℝ) < q from lt_of_lt_of_le one_pos q.property)⟩ 1 μ₁ ∧
        μ₀ = μ₁

end PottsContinuity.BD12
