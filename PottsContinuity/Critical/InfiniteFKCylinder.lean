module

public import PottsContinuity.Critical.InfinitePath
public import PottsContinuity.PD.RCInfinite.FiniteEnergy
public import PottsContinuity.PD.RCInfinite.MeasurableBounds
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.PD.FK
namespace LatticeConfiguration

/-- The cylinder event that every edge in a finite set is closed. -/
def allClosed (F : Finset squareLattice.edgeSet) : Set LatticeConfiguration :=
  {ω | ∀ e ∈ F, ω e = false}

@[simp] theorem allClosed_empty : allClosed ∅ = Set.univ := by
  ext ω
  simp [allClosed]

@[simp] theorem allClosed_insert (e : squareLattice.edgeSet)
    (F : Finset squareLattice.edgeSet) :
    allClosed (insert e F) = {ω | ω e = false} ∩ allClosed F := by
  classical
  ext ω
  simp [allClosed]

end LatticeConfiguration
end PottsContinuity.PD.FK

namespace PottsContinuity.Critical

open MeasureTheory Filter Topology Set
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

/-- A finite all-open cylinder does not read an edge outside its support. -/
theorem allOpen_dependsOn_edge_compl (F : Finset LatticeEdge) (e : LatticeEdge)
    (he : e ∉ F) :
    DependsOn ({e}ᶜ) (LatticeConfiguration.allOpen F) := by
  intro ω η hω
  change (∀ f ∈ F, ω f = true) ↔ (∀ f ∈ F, η f = true)
  constructor <;> intro h f hf
  · have hfe : f ≠ e := by
      intro hEq
      subst f
      exact he hf
    have hfcomp : f ∈ ({e}ᶜ : Set LatticeEdge) := by simpa using hfe
    rw [← hω f hfcomp]
    exact h f hf
  · have hfe : f ≠ e := by
      intro hEq
      subst f
      exact he hf
    have hfcomp : f ∈ ({e}ᶜ : Set LatticeEdge) := by simpa using hfe
    rw [hω f hfcomp]
    exact h f hf

/-- The finite-energy lower bound on a closed coordinate implies the sharp
`p` upper bound on an open coordinate for any supported cylinder. -/
theorem limit_cylinder_open_upper (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (e : LatticeEdge)
    {B : Set LatticeConfiguration} (hB : IsCylinder B)
    (hind : DependsOn ({e}ᶜ) B) :
    μ.real (B ∩ {ω | ω e = true}) ≤ edgeParameter θ * μ.real B := by
  have : IsProbabilityMeasure μ := hμ.1
  have henergy := cylinder_finite_energy θ 1 μ hμ e hB hind
  have hopen : MeasurableSet {ω : LatticeConfiguration | ω e = true} :=
    (isCylinder_coordinate e true).measurableSet
  have hsplit :
      μ.real (B ∩ {ω | ω e = true}) + μ.real (B ∩ {ω | ω e = false}) = μ.real B := by
    have h := measureReal_inter_add_sdiff (μ := μ) (s := B)
      (t := {ω : LatticeConfiguration | ω e = true}) hopen
    have hdiff : B \ {ω : LatticeConfiguration | ω e = true} =
        B ∩ {ω : LatticeConfiguration | ω e = false} := by
      ext ω
      simp
    simpa [hdiff] using h
  have hclosed := henergy.2
  nlinarith

/-- The finite-energy open lower bound gives an upper bound for a closed
coordinate, uniformly over every cylinder that does not read that edge. -/
theorem limit_cylinder_closed_upper (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (e : LatticeEdge)
    {B : Set LatticeConfiguration} (hB : IsCylinder B)
    (hind : DependsOn ({e}ᶜ) B) :
    μ.real (B ∩ {ω | ω e = false}) ≤ (1 - openEnergy θ) * μ.real B := by
  have : IsProbabilityMeasure μ := hμ.1
  have henergy := cylinder_finite_energy θ 1 μ hμ e hB hind
  have hopen : MeasurableSet {ω : LatticeConfiguration | ω e = true} :=
    (isCylinder_coordinate e true).measurableSet
  have hsplit :
      μ.real (B ∩ {ω | ω e = true}) + μ.real (B ∩ {ω | ω e = false}) = μ.real B := by
    have h := measureReal_inter_add_sdiff (μ := μ) (s := B)
      (t := {ω : LatticeConfiguration | ω e = true}) hopen
    have hdiff : B \ {ω : LatticeConfiguration | ω e = true} =
        B ∩ {ω : LatticeConfiguration | ω e = false} := by
      ext ω
      simp
    simpa [hdiff] using h
  nlinarith [henergy.1]

/-- A finite all-closed cylinder has probability at most the corresponding
power of the one-edge closed upper bound. -/
theorem limit_allClosed_probability_upper (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (F : Finset LatticeEdge) :
    μ.real (LatticeConfiguration.allClosed F) ≤
      (1 - openEnergy θ) ^ F.card := by
  have : IsProbabilityMeasure μ := hμ.1
  induction F using Finset.induction_on with
  | empty => simp [LatticeConfiguration.allClosed_empty]
  | @insert e F hne ih =>
      have hB : IsCylinder (LatticeConfiguration.allClosed F) := by
        refine ⟨F, ?_⟩
        intro ω η hω
        change (∀ f ∈ F, ω f = false) ↔ (∀ f ∈ F, η f = false)
        constructor <;> intro h f hf
        · rw [← hω f hf]; exact h f hf
        · rw [hω f hf]; exact h f hf
      have hind : DependsOn ({e}ᶜ) (LatticeConfiguration.allClosed F) := by
        intro ω η hω
        change (∀ f ∈ F, ω f = false) ↔ (∀ f ∈ F, η f = false)
        constructor <;> intro h f hf
        · have hfe : f ≠ e := fun he => hne (he ▸ hf)
          have hfcomp : f ∈ ({e}ᶜ : Set LatticeEdge) := by simpa using hfe
          rw [← hω f hfcomp]
          exact h f hf
        · have hfe : f ≠ e := fun he => hne (he ▸ hf)
          have hfcomp : f ∈ ({e}ᶜ : Set LatticeEdge) := by simpa using hfe
          rw [hω f hfcomp]
          exact h f hf
      have hupper := limit_cylinder_closed_upper θ μ hμ e hB hind
      rw [LatticeConfiguration.allClosed_insert]
      calc
        μ.real ({ω | ω e = false} ∩ LatticeConfiguration.allClosed F) ≤
            (1 - openEnergy θ) * μ.real (LatticeConfiguration.allClosed F) := by
              simpa [inter_comm] using hupper
        _ ≤ (1 - openEnergy θ) * (1 - openEnergy θ) ^ F.card :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (openEnergy_le_one θ))
        _ = (1 - openEnergy θ) ^ (insert e F).card := by
          rw [Finset.card_insert_of_notMem hne, pow_succ]
          ring

/-- The open and closed finite-energy bounds iterate over a finite edge set.
For every wired infinite-volume limit, its all-open cylinder probability lies
between the corresponding lower and upper Bernoulli powers. -/
theorem limit_allOpen_probability_bounds (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (F : Finset LatticeEdge) :
    openEnergy θ ^ F.card ≤ μ.real (LatticeConfiguration.allOpen F) ∧
      μ.real (LatticeConfiguration.allOpen F) ≤ edgeParameter θ ^ F.card := by
  have : IsProbabilityMeasure μ := hμ.1
  induction F using Finset.induction_on with
  | empty =>
      simp
  | @insert e F hne ih =>
      have hB : IsCylinder (LatticeConfiguration.allOpen F) := isCylinder_allOpen F
      have hind := allOpen_dependsOn_edge_compl F e hne
      have henergy := cylinder_finite_energy θ 1 μ hμ e hB hind
      have hupper := limit_cylinder_open_upper θ μ hμ e hB hind
      have hset :
          LatticeConfiguration.allOpen (insert e F) =
            LatticeConfiguration.allOpen F ∩ {ω | ω e = true} := by
        rw [LatticeConfiguration.allOpen_insert, inter_comm]
      rw [hset]
      constructor
      · calc
          openEnergy θ ^ (insert e F).card =
              openEnergy θ * openEnergy θ ^ F.card := by
                rw [Finset.card_insert_of_notMem hne, pow_succ]
                ring
          _ ≤ openEnergy θ * μ.real (LatticeConfiguration.allOpen F) :=
                mul_le_mul_of_nonneg_left ih.1 (openEnergy_pos θ).le
          _ ≤ μ.real (LatticeConfiguration.allOpen F ∩ {ω | ω e = true}) := henergy.1
      · calc
          μ.real (LatticeConfiguration.allOpen F ∩ {ω | ω e = true}) ≤
              edgeParameter θ * μ.real (LatticeConfiguration.allOpen F) := hupper
          _ ≤ edgeParameter θ * edgeParameter θ ^ F.card :=
              mul_le_mul_of_nonneg_left ih.2 (edgeParameter_pos θ).le
          _ = edgeParameter θ ^ (insert e F).card := by
              rw [Finset.card_insert_of_notMem hne, pow_succ]
              ring

/-- Each nonrepeating direction code of length `n` has an all-open event of
limit probability at most `p^n`. -/
theorem limit_walkCodeOpenEvent_le (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (x : LatticeVertex) (n : ℕ) (c : GoodWalkCode x n) :
    μ.real (LatticeConfiguration.allOpen (walkCodeEdgeFinset x c.1)) ≤
      edgeParameter θ ^ n := by
  have h := (limit_allOpen_probability_bounds θ μ hμ
    (walkCodeEdgeFinset x c.1)).2
  have hcard : (walkCodeEdgeFinset x c.1).card = n := by
    simp [walkCodeEdgeFinset, List.toFinset_card_of_nodup c.2,
      walkCodeEdgeList_length]
  simpa [hcard] using h

/-- A finite union over all direction codes gives the same low-parameter path
bound for every wired infinite-volume limit. -/
theorem limit_openWalkCodeUnion_le (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (x : LatticeVertex) (n : ℕ) :
    μ.real (⋃ c : GoodWalkCode x n,
      LatticeConfiguration.allOpen (walkCodeEdgeFinset x c.1)) ≤
        (4 * edgeParameter θ) ^ n := by
  have : IsProbabilityMeasure μ := hμ.1
  classical
  have hcard : Fintype.card (GoodWalkCode x n) ≤ Fintype.card (WalkCode n) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  calc
    μ.real (⋃ c : GoodWalkCode x n,
        LatticeConfiguration.allOpen (walkCodeEdgeFinset x c.1)) ≤
      ∑ c : GoodWalkCode x n,
        μ.real (LatticeConfiguration.allOpen (walkCodeEdgeFinset x c.1)) :=
      MeasureTheory.measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : GoodWalkCode x n, edgeParameter θ ^ n :=
      Finset.sum_le_sum fun c _ => limit_walkCodeOpenEvent_le θ μ hμ x n c
    _ = (Fintype.card (GoodWalkCode x n) : ℝ) * edgeParameter θ ^ n := by simp
    _ ≤ (Fintype.card (WalkCode n) : ℝ) * edgeParameter θ ^ n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (pow_nonneg (edgeParameter_pos θ).le n)
    _ = (4 * edgeParameter θ) ^ n := by
      rw [card_walkCode]
      push_cast
      rw [← mul_pow]

/-- An infinite cluster has probability bounded by the low-parameter path
estimate under every wired limit. -/
theorem limit_infiniteAt_real_le (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (n : ℕ) :
    μ.real (infiniteAt (0, 0)) ≤ (4 * edgeParameter θ) ^ n := by
  have : IsProbabilityMeasure μ := hμ.1
  apply (measureReal_mono ?_).trans (limit_openWalkCodeUnion_le θ μ hμ (0, 0) n)
  intro ω hω
  have hpath := infiniteAt_subset_openSimpleWalkEvent n hω
  have hcodes := openSimpleWalkEvent_subset_openWalkCodeUnion (0, 0) n hpath
  rcases Set.mem_iUnion.mp hcodes with ⟨c, hc⟩
  apply Set.mem_iUnion.mpr ⟨c, ?_⟩
  change (walkCodeEdgeFinset (0, 0) c.1 : Set LatticeEdge) ⊆
    {e | ω e = true} at hc ⊢
  exact hc

/-- If `4p < 1`, every wired infinite-volume limit has zero probability of an
infinite cluster at the origin. -/
theorem limit_infiniteAt_real_eq_zero_of_four_p_lt_one (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (hsmall : 4 * edgeParameter θ < 1) :
    μ.real (infiniteAt (0, 0)) = 0 := by
  have hnonneg : 0 ≤ 4 * edgeParameter θ :=
    mul_nonneg (by norm_num) (edgeParameter_pos θ).le
  have hpow : Tendsto (fun n : ℕ => (4 * edgeParameter θ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hsmall
  have hbound : ∀ n : ℕ,
      μ.real (infiniteAt (0, 0)) ≤ (4 * edgeParameter θ) ^ n :=
    fun n => limit_infiniteAt_real_le θ μ hμ n
  have hle : μ.real (infiniteAt (0, 0)) ≤ 0 := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hpow
      (Filter.Eventually.of_forall hbound)
  exact le_antisymm hle (measureReal_nonneg)

/-- The corresponding measure of the infinite-cluster event is zero. -/
theorem limit_infiniteAt_zero_of_four_p_lt_one (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (hsmall : 4 * edgeParameter θ < 1) :
    μ (infiniteAt (0, 0)) = 0 := by
  have : IsProbabilityMeasure μ := hμ.1
  exact (measureReal_eq_zero_iff).mp
    (limit_infiniteAt_real_eq_zero_of_four_p_lt_one θ μ hμ hsmall)

end
end PottsContinuity.Critical
