module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Foundations.Bridges
public import PottsContinuity.PD.RCInfinite.TranslationSupport
public import PottsContinuity.Infinite.ComparisonStatements
public import PottsContinuity.Thm3.Easy.P5AnnulusEventProperties

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.DualityExt

/-- The intersection of a finite consecutive block of annulus events, ordered
from the innermost annulus outwards. -/
def dyadicAnnulusTail (E : ℕ → Set LatticeConfiguration) (start : ℕ) :
    ℕ → Set LatticeConfiguration
  | 0 => Set.univ
  | n + 1 => E start ∩ dyadicAnnulusTail E (start + 1) n
termination_by n => n
decreasing_by omega

private theorem dyadicAnnulusTail_isCylinder
    (E : ℕ → Set LatticeConfiguration)
    (start count : ℕ)
    (hE : ∀ j, IsCylinder (E j)) :
    IsCylinder (dyadicAnnulusTail E start count) := by
  induction count generalizing start with
  | zero =>
      refine ⟨∅, ?_⟩
      intro ω η hω
      simp [dyadicAnnulusTail]
  | succ count ih =>
      simp only [dyadicAnnulusTail]
      exact (hE start).inter (ih (start + 1))

private theorem dyadicAnnulusTail_dependsOn_after
    (E : ℕ → Set LatticeConfiguration)
    (r start count : ℕ)
    (hE : ∀ j r, start ≤ j → r < j →
      DependsOn (boxEdges (0, 0) (2 ^ r))ᶜ (E j))
    (hrs : r < start) :
    DependsOn (boxEdges (0, 0) (2 ^ r))ᶜ
      (dyadicAnnulusTail E start count) := by
  induction count generalizing start with
  | zero =>
      intro ω η hω
      simp [dyadicAnnulusTail]
  | succ count ih =>
      intro ω η hω
      simp only [dyadicAnnulusTail, Set.mem_inter_iff]
      exact and_congr (hE start r le_rfl hrs ω η hω)
        (ih (start + 1)
          (fun j r hj hr => hE j r (by omega) hr) (by omega) ω η hω)

/-- A wired one-arm event that forces crossings of consecutive annuli has a
product upper bound whenever each annulus event has a uniform wired-box bound.
The support premises express that the current annulus is local to its outer
box and all subsequent annuli use only edges strictly outside that box. -/
theorem wired_dyadic_annulus_product_bound_from
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p q 1 μ)
    (E : ℕ → Set LatticeConfiguration) (c : ℝ)
    (hc : 0 ≤ 1 - c)
    (start count : ℕ)
    (hCylinder : ∀ j, IsCylinder (E j))
    (hlocal : ∀ j, start ≤ j →
      DependsOn (boxEdges (0, 0) (2 ^ j)) (E j) ∧ IsUpperSet (E j))
    (houtside : ∀ j r, start ≤ j → r < j →
      DependsOn (boxEdges (0, 0) (2 ^ r))ᶜ (E j))
    (hbound : ∀ j, start ≤ j →
      (boxMeasure (PottsContinuity.Infinite.pdParameters p q hp0 hp1 hq)
        1 (0, 0) (2 ^ j) :
        Measure LatticeConfiguration).real (E j) ≤ 1 - c) :
    μ.real (dyadicAnnulusTail E start count) ≤ (1 - c) ^ count := by
  cases PottsContinuity.Foundations.squareLattice_eq_PD
  induction count generalizing start with
  | zero =>
      simp only [dyadicAnnulusTail]
      have huniv : μ Set.univ = 1 := hμ.1.measure_univ
      change ENNReal.toReal (μ Set.univ) ≤ 1
      rw [huniv]
      norm_num
  | succ count ih =>
      simp only [dyadicAnnulusTail]
      have hDMP := PottsContinuity.Infinite.wired_infinite_DMP_local
        p q hp0 hp1 hq μ hμ (2 ^ start) (hCylinder start)
        (dyadicAnnulusTail_isCylinder E (start + 1) count hCylinder)
        (hlocal start le_rfl).1
        (dyadicAnnulusTail_dependsOn_after E
          start (start + 1) count
          (fun j r hj hr => houtside j r (by omega) hr)
          (by omega))
        (hlocal start le_rfl).2
      have hboundTail : ∀ j, start + 1 ≤ j →
          (boxMeasure (PottsContinuity.Infinite.pdParameters
            p q hp0 hp1 hq) 1 (0, 0) (2 ^ j) :
            Measure LatticeConfiguration).real (E j) ≤ 1 - c := by
        intro j hj
        exact hbound j (by omega)
      have hlocalTail : ∀ j, start + 1 ≤ j →
          DependsOn (boxEdges (0, 0) (2 ^ j)) (E j) ∧ IsUpperSet (E j) := by
        intro j hj
        exact hlocal j (by omega)
      have houtsideTail : ∀ j r, start + 1 ≤ j → r < j →
          DependsOn (boxEdges (0, 0) (2 ^ r))ᶜ (E j) := by
        intro j r hj hr
        exact houtside j r (by omega) hr
      have htail := ih (start + 1) hlocalTail houtsideTail hboundTail
      have hfactor := hbound start (by omega)
      have hmeasureNonneg := measureReal_nonneg (μ := μ)
        (s := dyadicAnnulusTail E (start + 1) count)
      calc
        μ.real (E start ∩ dyadicAnnulusTail E (start + 1) count) ≤
            (boxMeasure (PottsContinuity.Infinite.pdParameters
              p q hp0 hp1 hq) 1 (0, 0) (2 ^ start) :
              Measure LatticeConfiguration).real (E start) *
                μ.real (dyadicAnnulusTail E (start + 1) count) := hDMP
        _ ≤ (1 - c) * μ.real (dyadicAnnulusTail E (start + 1) count) :=
          mul_le_mul_of_nonneg_right hfactor hmeasureNonneg
        _ ≤ (1 - c) * (1 - c) ^ count :=
          mul_le_mul_of_nonneg_left htail hc
        _ = (1 - c) ^ (count + 1) := by rw [pow_succ]; ring

private theorem boxEdges_mono (m n : ℕ) (hmn : m ≤ n) :
    boxEdges (0, 0) m ⊆ boxEdges (0, 0) n := by
  intro e he
  apply (mem_boxEdges_iff (0, 0) n e).2
  intro x hx
  exact latticeBox_mono (0, 0) hmn
    ((mem_boxEdges_iff (0, 0) m e).1 he x hx)

/-- The wired open crossing of the dyadic full-inner-box annulus at scale `j`.
For `j ≥ 1` its annulus has vertex set `Λ_(2^j) \\ Λ_(2^(j-1)-1)`. -/
def dyadicAnnulusOpenCrossingEvent (j : ℕ) : Set LatticeConfiguration :=
  {ω | annulusOpenCrossing (2 ^ (j - 1)) ω}

private theorem dyadicAnnulus_radius_eq (j : ℕ) (hj : 1 ≤ j) :
    2 * 2 ^ (j - 1) = 2 ^ j := by
  calc
    2 * 2 ^ (j - 1) = 2 ^ (j - 1) * 2 := by omega
    _ = 2 ^ ((j - 1) + 1) := by rw [Nat.pow_succ]
    _ = 2 ^ j := by congr 1; omega

private theorem dyadicAnnulus_local (j : ℕ) (hj : 1 ≤ j) :
    DependsOn (boxEdges (0, 0) (2 ^ j))
      (dyadicAnnulusOpenCrossingEvent j) ∧
    IsUpperSet (dyadicAnnulusOpenCrossingEvent j) := by
  constructor
  · have h := annulusOpenCrossing_dependsOn_outerBox (2 ^ (j - 1))
    rw [dyadicAnnulus_radius_eq j hj] at h
    simpa [dyadicAnnulusOpenCrossingEvent] using h
  · simpa [dyadicAnnulusOpenCrossingEvent] using
      annulusOpenCrossing_isUpperSet (2 ^ (j - 1))

private theorem dyadicAnnulus_dependsOn_outside
    (j r : ℕ) (hj : 3 ≤ j) (hrj : r < j) :
    DependsOn (boxEdges (0, 0) (2 ^ r))ᶜ
      (dyadicAnnulusOpenCrossingEvent j) := by
  have hjinner : 1 ≤ 2 ^ (j - 1) := by
    have hpowPos : 0 < 2 ^ (j - 1) := Nat.pow_pos (by omega)
    omega
  have hinner := annulusOpenCrossing_dependsOn_outside
    (2 ^ (j - 1)) hjinner
  have hr : r ≤ j - 1 := by omega
  have hpow : 2 ^ r ≤ 2 ^ (j - 1) :=
    Nat.pow_le_pow_right (by omega) hr
  have hbox := boxEdges_mono (2 ^ r) (2 ^ (j - 1)) hpow
  intro ω η hAgree
  apply hinner
  intro e he
  have heSmall : e ∈ (boxEdges (0, 0) (2 ^ r))ᶜ := by
    intro hmem
    exact he (hbox hmem)
  exact hAgree e heSmall

/-- Assuming the annular law-transfer estimate at a fixed constant, the
actual annulus crossings enjoy the consecutive product bound from scale three
onward. The premise is exactly the wired-box annulus estimate `hboundθ`; no
annulus-duality conclusion is hidden here. -/
theorem wired_dyadic_annulus_product_of_annulusDuality_fixed
    (q : Set.Ici (1 : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 1 μ)
    (count : ℕ) (c : ℝ)
    (hboundθ : ∀ j : ℕ, 3 ≤ j →
      (boxMeasure (PottsContinuity.PD.FK.criticalParameters q)
        1 (0, 0) (2 ^ j) : Measure LatticeConfiguration).real
          (dyadicAnnulusOpenCrossingEvent j) ≤ 1 - c) :
    μ.real (dyadicAnnulusTail dyadicAnnulusOpenCrossingEvent 3 count) ≤
      (1 - c) ^ count := by
  let θ := PottsContinuity.PD.FK.criticalParameters q
  let p : Set.Icc (0 : ℝ) 1 := θ.toP
  let q' : Set.Ioi (0 : ℝ) := θ.toQ
  have hp0 : 0 < (p : ℝ) := θ.edgeProbability.property.1
  have hp1 : (p : ℝ) < 1 := θ.edgeProbability.property.2
  have hq : 1 ≤ (q' : ℝ) := θ.property
  have hμ' : IsRCInfiniteVolumeLimit p q' 1 μ := by
    simpa [p, q'] using hμ
  have hparams : PottsContinuity.Infinite.pdParameters
      p q' hp0 hp1 hq = θ := by
    dsimp [θ, p, q', PottsContinuity.Infinite.pdParameters,
      PottsContinuity.PD.FK.criticalParameters,
      PottsContinuity.PD.FK.Parameters.toP,
      PottsContinuity.PD.FK.Parameters.toQ,
      PottsContinuity.PD.FK.edgeParameter]
  have hCylinder : ∀ j, IsCylinder (dyadicAnnulusOpenCrossingEvent j) := by
    intro j
    simpa [dyadicAnnulusOpenCrossingEvent] using
      annulusOpenCrossing_isCylinder (2 ^ (j - 1))
  have hlocal : ∀ j, 3 ≤ j →
      DependsOn (boxEdges (0, 0) (2 ^ j))
        (dyadicAnnulusOpenCrossingEvent j) ∧
      IsUpperSet (dyadicAnnulusOpenCrossingEvent j) := by
    intro j hj
    exact dyadicAnnulus_local j (by omega)
  have houtside : ∀ j r, 3 ≤ j → r < j →
      DependsOn (boxEdges (0, 0) (2 ^ r))ᶜ
        (dyadicAnnulusOpenCrossingEvent j) := by
    intro j r hj hr
    exact dyadicAnnulus_dependsOn_outside j r hj hr
  have hbound : ∀ j, 3 ≤ j →
      (boxMeasure (PottsContinuity.Infinite.pdParameters
        p q' hp0 hp1 hq) 1 (0, 0) (2 ^ j) :
        Measure LatticeConfiguration).real
          (dyadicAnnulusOpenCrossingEvent j) ≤ 1 - c := by
    intro j hj
    rw [hparams]
    exact hboundθ j hj
  have hhc : 0 ≤ 1 - c := by
    have hnonneg := measureReal_nonneg (μ :=
      (boxMeasure (PottsContinuity.PD.FK.criticalParameters q)
        1 (0, 0) (2 ^ 3) : Measure LatticeConfiguration))
      (s := dyadicAnnulusOpenCrossingEvent 3)
    exact hnonneg.trans (hboundθ 3 (by omega))
  exact wired_dyadic_annulus_product_bound_from p q' hp0 hp1 hq μ hμ'
    dyadicAnnulusOpenCrossingEvent c hhc 3 count hCylinder
    (fun j hj => hlocal j (by omega))
    (fun j r hj hr => houtside j r (by omega) hr)
    hbound

end PottsContinuity.Thm3.Easy
