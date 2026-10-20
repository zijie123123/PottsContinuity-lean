-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/TrifurcationProbability.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.FiniteBoxCounting
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open MeasureTheory Set Finset

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

def trifurcationEvent (v : LatticeVertex) : Set LatticeConfiguration :=
  {ω | isTrifurcationAt ω v}

def trifurcationIndicator (v : LatticeVertex) : LatticeConfiguration → ℝ :=
  (trifurcationEvent v).indicator (fun _ => 1)

def boxTrifurcationCountReal (ω : LatticeConfiguration) (n : ℕ) : ℝ :=
  ∑ v ∈ (Finset.univ : Finset (BoxVertex (0, 0) n)), trifurcationIndicator v.val ω

theorem measurableSet_trifurcationEvent (v : LatticeVertex) :
    MeasurableSet (trifurcationEvent v) := measurableSet_isTrifurcationAt v

theorem trifurcationEvent_preimage_translate (a v : LatticeVertex) :
    (edgeTranslate a) ⁻¹' trifurcationEvent (latticeTranslate a v) = trifurcationEvent v := by
  ext ω
  exact isTrifurcationAt_translation a ω v

theorem trifurcation_probability_translation (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (a v : LatticeVertex) :
    μ.real (trifurcationEvent (latticeTranslate a v)) = μ.real (trifurcationEvent v) := by
  rw [← limit_translate_real θ i μ hμ a (measurableSet_trifurcationEvent _),
    trifurcationEvent_preimage_translate]

theorem boxTrifurcationCountReal_eq_card (ω : LatticeConfiguration) (n : ℕ) :
    boxTrifurcationCountReal ω n = (boxTrifurcationVertices ω n).card := by
  unfold boxTrifurcationCountReal trifurcationIndicator trifurcationEvent
    boxTrifurcationVertices
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  exact Finset.sum_boole (fun v : BoxVertex (0, 0) n => isTrifurcationAt ω v.val)
    (Finset.univ : Finset (BoxVertex (0, 0) n))

theorem integral_boxTrifurcationCountReal (μ : Measure LatticeConfiguration)
    (hμ : IsFiniteMeasure μ) (n : ℕ) :
    ∫ ω, boxTrifurcationCountReal ω n ∂μ =
      ∑ v ∈ (Finset.univ : Finset (BoxVertex (0, 0) n)),
        μ.real (trifurcationEvent v.val) := by
  unfold boxTrifurcationCountReal
  have hInt (v : BoxVertex (0, 0) n) (hv : v ∈ (Finset.univ : Finset _)) :
      Integrable (fun ω => trifurcationIndicator v.val ω) μ := by
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_trifurcationEvent v.val)
  rw [integral_finsetSum (Finset.univ : Finset (BoxVertex (0, 0) n)) hInt]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [trifurcationIndicator]
  rw [show (fun _ : LatticeConfiguration => (1 : ℝ)) =
      (1 : LatticeConfiguration → ℝ) from rfl]
  exact integral_indicator_one (measurableSet_trifurcationEvent v.val)

theorem expected_box_trifurcation_count_le (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (n : ℕ) :
    ∫ ω, boxTrifurcationCountReal ω n ∂μ ≤ (boxBoundaryVertices (n + 1)).card := by
  have : IsProbabilityMeasure μ := hμ.1
  have hcount : Integrable (fun ω => boxTrifurcationCountReal ω n) μ := by
    unfold boxTrifurcationCountReal
    apply integrable_finsetSum
    intro v hv
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_trifurcationEvent v.val)
  have hconst : Integrable (fun _ : LatticeConfiguration =>
      ((boxBoundaryVertices (n + 1)).card : ℝ)) μ := integrable_const _
  have hle : (fun ω => boxTrifurcationCountReal ω n) ≤ᵐ[μ]
      (fun _ => ((boxBoundaryVertices (n + 1)).card : ℝ)) := by
    filter_upwards [] with ω
    rw [boxTrifurcationCountReal_eq_card]
    exact_mod_cast box_trifurcation_card_le_boundary ω n
  calc
    ∫ ω, boxTrifurcationCountReal ω n ∂μ ≤
        ∫ _ : LatticeConfiguration, ((boxBoundaryVertices (n + 1)).card : ℝ) ∂μ :=
      integral_mono_ae hcount hconst hle
    _ = (boxBoundaryVertices (n + 1)).card := by simp [Measure.real]

theorem expected_box_trifurcation_count_eq_volume_mul_origin
    (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) (n : ℕ) :
    ∫ ω, boxTrifurcationCountReal ω n ∂μ =
      ((2 * n + 1) ^ 2 : ℕ) * μ.real (trifurcationEvent (0, 0)) := by
  have : IsProbabilityMeasure μ := hμ.1
  rw [integral_boxTrifurcationCountReal μ inferInstance n]
  calc
    ∑ v ∈ (Finset.univ : Finset (BoxVertex (0, 0) n)),
        μ.real (trifurcationEvent v.val) =
      ∑ v ∈ (Finset.univ : Finset (BoxVertex (0, 0) n)),
        μ.real (trifurcationEvent (0, 0)) := by
          apply Finset.sum_congr rfl
          intro v hv
          simpa [latticeTranslate] using
            (trifurcation_probability_translation θ i μ hμ v.val (0, 0))
    _ = (Fintype.card (BoxVertex (0, 0) n) : ℝ) *
        μ.real (trifurcationEvent (0, 0)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((2 * n + 1) ^ 2 : ℕ) * μ.real (trifurcationEvent (0, 0)) := by
          rw [card_boxVertex]


theorem isRCInfiniteVolumeLimit_origin_trifurcation_probability_zero
    (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    μ.real (trifurcationEvent (0, 0)) = 0 := by
  let δ : ℝ := μ.real (trifurcationEvent (0, 0))
  have hδ_nonneg : 0 ≤ δ := measureReal_nonneg
  have hbound (n : ℕ) :
      ((2 * n + 1) ^ 2 : ℕ) * δ ≤ (4 * (2 * (n + 1) + 1) : ℕ) := by
    have hEq := expected_box_trifurcation_count_eq_volume_mul_origin θ i μ hμ n
    have hLe := expected_box_trifurcation_count_le θ i μ hμ n
    have hBoundary := box_boundary_card_le (n + 1)
    rw [hEq] at hLe
    exact_mod_cast hLe.trans (Nat.cast_le.mpr hBoundary)
  by_contra hδzero
  have hδpos : 0 < δ := lt_of_le_of_ne hδ_nonneg (Ne.symm hδzero)
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / δ + 2)
  have hn' : 4 / δ < (n : ℝ) := by linarith
  have hnδ : 4 < (n : ℝ) * δ := (div_lt_iff₀ hδpos).mp hn'
  have hn2 : 2 < (n : ℝ) := by
    have hdiv : 0 < 4 / δ := div_pos (by norm_num) hδpos
    linarith
  have hquad : 16 * (n : ℝ) < 4 * (n : ℝ) ^ 2 * δ := by
    have hm := mul_lt_mul_of_pos_left hnδ (show 0 < (n : ℝ) by linarith)
    nlinarith [hm]
  have hBoundN : (2 * (n : ℝ) + 1) ^ 2 * δ ≤ 8 * (n : ℝ) + 12 := by
    have h := hbound n
    have hleft : (((2 * n + 1) ^ 2 : ℕ) : ℝ) = (2 * (n : ℝ) + 1) ^ 2 := by
      push_cast
      ring
    have hright : ((4 * (2 * (n + 1) + 1) : ℕ) : ℝ) = 8 * (n : ℝ) + 12 := by
      push_cast
      ring
    rw [hleft, hright] at h
    exact h
  have hstrict : 8 * (n : ℝ) + 12 < 4 * (n : ℝ) ^ 2 * δ := by
    nlinarith [hquad, hn2]
  have hlarge : 8 * (n : ℝ) + 12 < (2 * (n : ℝ) + 1) ^ 2 * δ := by
    nlinarith [hstrict, hδpos, hn2]
  have : (2 * (n : ℝ) + 1) ^ 2 * δ ≤ 8 * (n : ℝ) + 12 := hBoundN
  linarith

end
end PottsContinuity.PD.RCInfinite
