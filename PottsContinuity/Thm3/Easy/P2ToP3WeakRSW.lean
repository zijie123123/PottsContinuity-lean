module

public import Mathlib
public import PottsContinuity.Infinite.Translation
public import PottsContinuity.PD.FK.WiredBoxTranslation
public import PottsContinuity.PD.CorrLength.ConnectionEvents
public import PottsContinuity.Thm3.Easy.P2ToP3Conditional

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.CorrLength

theorem oneArmBoundaryEvent_translation (a x : LatticeVertex) (n : ℕ)
    (ω : LatticeConfiguration) :
    latticeConfigurationTranslate a ω ∈
        oneArmBoundaryEvent (latticeTranslate a x) n ↔
      ω ∈ oneArmBoundaryEvent x n := by
  constructor
  · rintro ⟨y, hy, hconn⟩
    let y₀ := latticeTranslate (-a) y
    have hcancel : latticeTranslate a y₀ = y := by
      dsimp [y₀, latticeTranslate]
      ext <;> omega
    have hy' : latticeTranslate a y₀ ∈
        PottsContinuity.PD.vertexBoundary
          (latticeBox (latticeTranslate a x) n) := by
      simpa [hcancel] using hy
    refine ⟨y₀,
      (PottsContinuity.PD.FK.mem_vertexBoundary_latticeBox_translate_iff
        a x y₀ n).mp hy', ?_⟩
    have hconn' : latticeConfigurationTranslate a ω ∈
        connectionEvent (latticeTranslate a x) (latticeTranslate a y₀) := by
      simpa [hcancel] using hconn
    exact (connectionEvent_translation a x y₀ ω).mp hconn'
  · rintro ⟨y, hy, hconn⟩
    refine ⟨latticeTranslate a y,
      (PottsContinuity.PD.FK.mem_vertexBoundary_latticeBox_translate_iff
        a x y n).mpr hy, ?_⟩
    exact (connectionEvent_translation a x y ω).mpr hconn

theorem oneArmBoundaryEvent_measurable (x : LatticeVertex) (n : ℕ) :
    MeasurableSet (oneArmBoundaryEvent x n) := by
  classical
  have heq : oneArmBoundaryEvent x n =
      ⋃ y : LatticeVertex,
        if y ∈ PottsContinuity.PD.vertexBoundary (latticeBox x n)
        then connectionEvent x y else ∅ := by
    ext ω
    simp [oneArmBoundaryEvent]
  rw [heq]
  exact MeasurableSet.iUnion fun y => by
    split_ifs
    · exact connectionEvent_isMeasurableSet x y
    · exact MeasurableSet.empty

theorem oneArmBoundaryEvent_real_translation
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hq : 1 ≤ (q : ℝ)) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit p q 1 μ)
    (a x : LatticeVertex) (n : ℕ) :
    μ.real (oneArmBoundaryEvent (latticeTranslate a x) n) =
      μ.real (oneArmBoundaryEvent x n) := by
  let : IsProbabilityMeasure μ := hμ.1
  have hinv := Infinite.infinite_volume_translation_invariant p q hq 1 μ hμ a
  have hmap := congrArg
    (fun ν : Measure LatticeConfiguration =>
      ν (oneArmBoundaryEvent (latticeTranslate a x) n)) hinv
  have hmap_apply :
      (μ.map (latticeConfigurationTranslate a))
        (oneArmBoundaryEvent (latticeTranslate a x) n) =
      μ ((latticeConfigurationTranslate a) ⁻¹'
        oneArmBoundaryEvent (latticeTranslate a x) n) :=
    Measure.map_apply (latticeConfigurationTranslate_measurable a)
      (oneArmBoundaryEvent_measurable (latticeTranslate a x) n)
  have hpre : (latticeConfigurationTranslate a) ⁻¹'
      oneArmBoundaryEvent (latticeTranslate a x) n = oneArmBoundaryEvent x n := by
    ext ω
    exact oneArmBoundaryEvent_translation a x n ω
  have hprob : μ (oneArmBoundaryEvent x n) =
      μ (oneArmBoundaryEvent (latticeTranslate a x) n) := by
    calc
      μ (oneArmBoundaryEvent x n) =
          μ ((latticeConfigurationTranslate a) ⁻¹'
            oneArmBoundaryEvent (latticeTranslate a x) n) := by rw [hpre]
      _ = (μ.map (latticeConfigurationTranslate a))
          (oneArmBoundaryEvent (latticeTranslate a x) n) := hmap_apply.symm
      _ = μ (oneArmBoundaryEvent (latticeTranslate a x) n) := hmap
  have hreal := congrArg ENNReal.toReal hprob
  simpa [Measure.real_def] using hreal.symm

theorem wired_weakRSW_oneArm_lower_bound
    (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 1 μ)
    (hWeakRSW : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ μ.real (PottsContinuity.BD12.verticalRectangle
        (-(n : ℤ), 0) (2 * n) n))
    (n : ℕ) (hn : 1 ≤ n) :
    hWeakRSW.choose / (2 * (n : ℝ) + 1) ≤
      μ.real (oneArmBoundaryEvent (0, 0) n) := by
  classical
  let : IsProbabilityMeasure μ := hμ.1
  let c := hWeakRSW.choose
  have hc : 0 < c := hWeakRSW.choose_spec.1
  have hcross := hWeakRSW.choose_spec.2 n hn
  have hsubset := verticalRectangle_subset_bottom_oneArm_union n
  have hmono := measureReal_mono (μ := μ) hsubset
  have hunion := measureReal_iUnion_fintype_le (μ := μ)
    (fun x : {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)} =>
      oneArmBoundaryEvent (x.val, 0) n)
  have htrans : ∀ x : {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)},
      μ.real (oneArmBoundaryEvent (x.val, 0) n) =
        μ.real (oneArmBoundaryEvent (0, 0) n) := by
    intro x
    have h := oneArmBoundaryEvent_real_translation
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ
      (PottsContinuity.PD.FK.criticalParameters q).property
      μ hμ (x.val, 0) (0, 0) n
    simpa [latticeTranslate] using h
  have hcard :
      Fintype.card {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)} = 2 * n + 1 := by
    rw [Fintype.card_coe, Int.card_Icc]
    have hi :
        (n : ℤ) + 1 - (-(n : ℤ)) = ((2 * n + 1 : ℕ) : ℤ) := by omega
    rw [hi]
    apply (Nat.cast_inj (R := ℤ)).1
    rw [Int.toNat_of_nonneg (by positivity)]
  have hU : Finset.univ.card =
      Fintype.card {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)} := rfl
  have hsum :
      (∑ x : {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)},
        μ.real (oneArmBoundaryEvent (x.val, 0) n)) =
      ((2 * n + 1 : ℕ) : ℝ) *
        μ.real (oneArmBoundaryEvent (0, 0) n) := by
    calc
      _ = ∑ _x : {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)},
          μ.real (oneArmBoundaryEvent (0, 0) n) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact htrans x
      _ = Fintype.card {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)} •
          μ.real (oneArmBoundaryEvent (0, 0) n) := by
        rw [Finset.sum_const]
        exact congrArg (fun k : ℕ => k • μ.real (oneArmBoundaryEvent (0, 0) n)) hU
      _ = ((2 * n + 1 : ℕ) : ℝ) *
          μ.real (oneArmBoundaryEvent (0, 0) n) := by rw [hcard, nsmul_eq_mul]
  have hle : c ≤
      ((2 * n + 1 : ℕ) : ℝ) *
        μ.real (oneArmBoundaryEvent (0, 0) n) := by
    calc
      c ≤ μ.real (PottsContinuity.BD12.verticalRectangle
          (-(n : ℤ), 0) (2 * n) n) := hcross
      _ ≤ μ.real (⋃ x : {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)},
          oneArmBoundaryEvent (x.val, 0) n) := hmono
      _ ≤ ∑ x : {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)},
          μ.real (oneArmBoundaryEvent (x.val, 0) n) := hunion
      _ = _ := hsum
  have hden : 0 < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hprod : c ≤
      μ.real (oneArmBoundaryEvent (0, 0) n) * ((2 * n + 1 : ℕ) : ℝ) := by
    simpa [mul_comm] using hle
  have hdiv := (div_le_iff₀ hden).2 hprod
  simpa [c, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hdiv

end PottsContinuity.Thm3.Easy
