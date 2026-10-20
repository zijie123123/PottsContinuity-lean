module

public import PottsContinuity.BD12.KSTUniformScaleInduction
public import PottsContinuity.BD12.KSTScales
public import PottsContinuity.BD12.KSTCascadeExport
public import PottsContinuity.BD12.KSTConstructionExport

/-! Uniform KST bridge bounds from actual adjacent quasi-crossings. All
corridor and closing geometry is discharged by the shared planar exports. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK MeasureTheory
noncomputable section

/-- Uniform adjacent quasi-crossings transport a positive base bridge to all
larger integral scales. The start index may be shifted to retain divisibility. -/
theorem wired_kst_uniform_bridge_of_adjacent_quasi_crossings
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (J : ℕ) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hbase : 0 < μ.real (kstBridge (kstScale J)))
    (hquasi : ∀ j, a ≤ μ.real (kstQuasiCrossing (4*kstScale (J+j)) (kstScale (J+j)))) :
    ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ μ.real (kstBridge (kstScale (J+j))) := by
  let S := fun j => kstScale (J+j)
  let b := fun j => μ.real (kstBridge (S j))
  let Q := fun j k => μ.real (kstQuasiCrossing (S j) (S k))
  let r := 1-Real.sqrt (1-a)
  have hslt : Real.sqrt (1-a) < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith only [ha])
  have hr : 0 < r := sub_pos.mpr hslt
  have hr1 : r ≤ 1 := sub_le_self _ (Real.sqrt_nonneg _)
  have hra : r ≤ a := by
    have hs2 := Real.sq_sqrt (sub_nonneg.mpr ha1)
    have hs0 := Real.sqrt_nonneg (1-a)
    have hs1 := hslt.le
    dsimp only [r]
    nlinarith only [hs2,hs0,hs1]
  have hSmono : Monotone S := fun j k hjk => kstScale_mono (Nat.add_le_add_left hjk J)
  have hSsucc (j : ℕ) : S (j+1) = 4*S j := by
    simpa only [S,Nat.add_assoc] using kstScale_succ (J+j)
  have hA (j : ℕ) : a ≤ Q (j+1) j := by
    dsimp only [Q]
    rw [hSsucc]
    exact hquasi j
  apply kst_exists_uniform_bridge_lower_bound b Q r hr hr1
    (by simpa only [b,S,Nat.add_zero] using hbase)
  · intro j
    exact hra.trans (hA j)
  · intro N m hm hQ
    have hc := wired_kst_cascade θ μ hμ (S (N+1)) (S N) (S m)
      (hSmono (Nat.le_succ N)) (hSmono hm.le) (kstScale_pos (J+m))
      (kstScale_dvd_twelve (J+N)) (kstScale_dvd_twelve (J+m)) hQ
    have hroot : r ≤ 1-Real.sqrt (1-Q (N+1) N) :=
      sub_le_sub_left (Real.sqrt_le_sqrt (sub_le_sub_left (hA N) 1)) 1
    exact hroot.trans hc
  · intro N m hm
    exact wired_kst_closing θ μ hμ (S N) (S m) (hSmono hm) (kstScale_pos (J+m))

/-- A uniform lower bound on the six literal construction inputs supplies all
adjacent quasi-crossing bounds. No corridor, cascade or closing premise remains. -/
theorem wired_kst_uniform_bridge_of_construction_bound
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (J : ℕ) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hbase : 0 < μ.real (kstBridge (kstScale J)))
    (hbound : ∀ j i, a ≤ μ.real (kstConstructionInputs (kstScale (J+j)) i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ μ.real (kstBridge (kstScale (J+j))) := by
  apply wired_kst_uniform_bridge_of_adjacent_quasi_crossings θ μ hμ J (a^6)
    (pow_pos ha _) (pow_le_one₀ ha.le ha1) hbase
  intro j
  exact wired_kst_construction_lower_bound θ μ hμ (J+j) a ha.le (hbound j)

end
end PottsContinuity.BD12
