module

public import PottsContinuity.PlanarTopology.HalfPlaneExitTranslation
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite Filter Topology
noncomputable section

theorem halfPlaneExitEvent_mono {S T : Set LatticeVertex} {L R : Set ℤ}
    (hST : S ⊆ T) (hLR : L ⊆ R) : halfPlaneExitEvent S L ⊆ halfPlaneExitEvent T R := by
  rintro ω ⟨y,hy,u,hu,hconn⟩
  exact ⟨y,hLR hy,u,hST hu,hconn⟩

/-- Expanding the lower exterior target heights exhausts the complete
first-exit event, on its original sampled induced domains. -/
theorem halfPlaneExitEvent_lower_target_probability_tendsto
    (μ : Measure LatticeConfiguration) (S : Set LatticeVertex) :
    Tendsto (fun n : ℤ => μ (halfPlaneExitEvent S {y : ℤ | y ≤ n}))
      atTop (𝓝 (μ (halfPlaneExitEvent S Set.univ))) := by
  let E := fun n : ℤ => halfPlaneExitEvent S {y : ℤ | y ≤ n}
  have hmono : Monotone E := by
    intro m n hmn
    apply halfPlaneExitEvent_mono Set.Subset.rfl
    intro y hy
    exact hy.trans hmn
  have hfull : (⋃ n, E n) = halfPlaneExitEvent S Set.univ := by
    ext ω
    constructor
    · intro hω
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hω
      exact halfPlaneExitEvent_mono Set.Subset.rfl (Set.subset_univ _) hn
    · rintro ⟨y,hy,u,hu,hconn⟩
      exact Set.mem_iUnion.mpr ⟨y,y,(by change y ≤ y; rfl),u,hu,hconn⟩
  simpa only [hfull,Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ) hmono

/-- Expanding the upper exterior target heights gives the same complete
first-exit probability. -/
theorem halfPlaneExitEvent_upper_target_probability_tendsto
    (μ : Measure LatticeConfiguration) (S : Set LatticeVertex) :
    Tendsto (fun n : ℤ => μ (halfPlaneExitEvent S {y : ℤ | -n ≤ y}))
      atTop (𝓝 (μ (halfPlaneExitEvent S Set.univ))) := by
  let E := fun n : ℤ => halfPlaneExitEvent S {y : ℤ | -n ≤ y}
  have hmono : Monotone E := by
    intro m n hmn
    apply halfPlaneExitEvent_mono Set.Subset.rfl
    intro y hy
    change -n ≤ y
    change -m ≤ y at hy
    omega
  have hfull : (⋃ n, E n) = halfPlaneExitEvent S Set.univ := by
    ext ω
    constructor
    · intro hω
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hω
      exact halfPlaneExitEvent_mono Set.Subset.rfl (Set.subset_univ _) hn
    · rintro ⟨y,hy,u,hu,hconn⟩
      exact Set.mem_iUnion.mpr ⟨-y,y,(by change - -y ≤ y; omega),u,hu,hconn⟩
  simpa only [hfull,Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ) hmono

theorem halfPlaneExitEvent_lower_target_real_probability_tendsto
    (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ] (S : Set LatticeVertex) :
    Tendsto (fun n : ℤ => μ.real (halfPlaneExitEvent S {y : ℤ | y ≤ n}))
      atTop (𝓝 (μ.real (halfPlaneExitEvent S Set.univ))) := by
  have hh := ENNReal.continuousAt_toReal (measure_ne_top μ (halfPlaneExitEvent S Set.univ))
  simpa only [Function.comp_def,Measure.real_def] using
    hh.tendsto.comp (halfPlaneExitEvent_lower_target_probability_tendsto μ S)

theorem halfPlaneExitEvent_upper_target_real_probability_tendsto
    (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ] (S : Set LatticeVertex) :
    Tendsto (fun n : ℤ => μ.real (halfPlaneExitEvent S {y : ℤ | -n ≤ y}))
      atTop (𝓝 (μ.real (halfPlaneExitEvent S Set.univ))) := by
  have hh := ENNReal.continuousAt_toReal (measure_ne_top μ (halfPlaneExitEvent S Set.univ))
  simpa only [Function.comp_def,Measure.real_def] using
    hh.tendsto.comp (halfPlaneExitEvent_upper_target_probability_tendsto μ S)

end
end PottsContinuity.PlanarTopology
