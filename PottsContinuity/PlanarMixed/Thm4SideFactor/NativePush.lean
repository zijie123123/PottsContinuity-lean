module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePushDefinitions

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open RSW PD.FK PD.RCInfinite
noncomputable section

private theorem floor_nat_mul (a n : ℕ) :
    ⌊(a:ℝ)*(n:ℝ)⌋ = (a:ℤ)*(n:ℤ) := by
  rw [← Nat.cast_mul,Int.floor_natCast,Nat.cast_mul]

theorem nativeSide_symmetric_reference_eq (q : Set.Ici (1:ℝ)) (m : ℕ) (hm : 1 ≤ m) :
    selfDualTopWiredCrossingProbability q
      ((16*(m:ℝ)+1)/(4*m-1:ℕ)) ((15*(m:ℝ))/(4*m-1:ℕ)) (4*m-1) =
    finiteBoundaryEventProbability
      (PottsContinuity.latticeRectangle (-16*(m:ℤ)-1) (16*(m:ℤ)+1) 0 (15*(m:ℤ)))
      (selfDualParameters q)
      (BoundaryCondition.wired {v | v.val.1 = -16*(m:ℤ)-1 ∨
        v.val.1 = 16*(m:ℤ)+1 ∨ v.val.2 = 15*(m:ℤ)})
      (horizontalCrossing
        (PottsContinuity.latticeRectangle (-16*(m:ℤ)-1) (16*(m:ℤ)+1) 0 (15*(m:ℤ)))
        (-16*(m:ℤ)-1) (16*(m:ℤ)+1) 0 (4*m-1:ℕ)) := by
  have hs : (0:ℝ) < (4*m-1:ℕ) := by exact_mod_cast (show 0 < 4*m-1 by omega)
  have hw : ⌊((16*(m:ℝ)+1)/(4*m-1:ℕ))*((4*m-1:ℕ):ℝ)⌋ = 16*(m:ℤ)+1 := by
    rw [div_mul_cancel₀ _ hs.ne', Int.floor_add_one]
    congr 1
    simpa using floor_nat_mul 16 m
  have hh : ⌊((15*(m:ℝ))/(4*m-1:ℕ))*((4*m-1:ℕ):ℝ)⌋ = 15*(m:ℤ) := by
    rw [div_mul_cancel₀ _ hs.ne']
    simpa using floor_nat_mul 15 m
  let F (l r H : ℤ) := finiteBoundaryEventProbability
    (PottsContinuity.latticeRectangle l r 0 H) (selfDualParameters q)
    (BoundaryCondition.wired {v | v.val.1=l ∨ v.val.1=r ∨ v.val.2=H})
    (horizontalCrossing (PottsContinuity.latticeRectangle l r 0 H) l r 0 (4*m-1:ℕ))
  change F (-⌊((16*(m:ℝ)+1)/(4*m-1:ℕ))*((4*m-1:ℕ):ℝ)⌋)
    ⌊((16*(m:ℝ)+1)/(4*m-1:ℕ))*((4*m-1:ℕ):ℝ)⌋
    ⌊((15*(m:ℝ))/(4*m-1:ℕ))*((4*m-1:ℕ):ℝ)⌋ = _
  rw [hw,hh]
  have he : -(16*(m:ℤ)+1) = -16*(m:ℤ)-1 := by omega
  rw [he]

theorem nativeSide_reference_le (q : Set.Ici (1:ℝ)) (m : ℕ) (hm : 1 ≤ m) :
    selfDualTopWiredCrossingProbability q 6 5 (4*m-1) ≤
      nativeSideCrossingProbability q m := by
  have hs : (0:ℝ) < (4*m-1:ℕ) := by exact_mod_cast (show 0 < 4*m-1 by omega)
  have hwidth : ⌊((16*(m:ℝ)+1)/(4*m-1:ℕ))*((4*m-1:ℕ):ℝ)⌋ = 16*(m:ℤ)+1 := by
    rw [div_mul_cancel₀ _ hs.ne', Int.floor_add_one]
    congr 1
    simpa using floor_nat_mul 16 m
  have hheight : ⌊((15*(m:ℝ))/(4*m-1:ℕ))*((4*m-1:ℕ):ℝ)⌋ = 15*(m:ℤ) := by
    rw [div_mul_cancel₀ _ hs.ne']
    simpa using floor_nat_mul 15 m
  have hcomp := Push.top_wired_enclosing_comparison (selfDualParameters q)
    ((16*(m:ℝ)+1)/(4*m-1:ℕ)) ((15*(m:ℝ))/(4*m-1:ℕ)) 6 5
    (4*m-1) (4*m-1) (by positivity) (by
      apply (le_div_iff₀ hs).mpr
      have hsle : ((4*m-1:ℕ):ℝ) ≤ 4*(m:ℝ) := by exact_mod_cast (show 4*m-1 ≤ 4*m by omega)
      nlinarith [Nat.cast_nonneg (α:=ℝ) m]) le_rfl
    (by
      have hf : ⌊6 * ((4*m-1:ℕ):ℝ)⌋ = 6 * ((4*m-1:ℕ):ℤ) := by simpa using floor_nat_mul 6 (4*m-1)
      rw [hwidth, hf]; omega)
    (by
      have hf : ⌊5 * ((4*m-1:ℕ):ℝ)⌋ = 5 * ((4*m-1:ℕ):ℤ) := by simpa using floor_nat_mul 5 (4*m-1)
      rw [hheight, hf]; omega)
  change selfDualTopWiredCrossingProbability q 6 5 (4*m-1) ≤
    selfDualTopWiredCrossingProbability q
      ((16*(m:ℝ)+1)/(4*m-1:ℕ)) ((15*(m:ℝ))/(4*m-1:ℕ)) (4*m-1) at hcomp
  rw [nativeSide_symmetric_reference_eq q m hm] at hcomp
  exact hcomp.trans (Push.asymmetric_rectangle_enclosing_comparison (selfDualParameters q)
    (-16*(m:ℤ)-1) (16*(m:ℤ)) (-16*(m:ℤ)-1) (16*(m:ℤ)+1) (15*(m:ℤ))
    (4*m-1) le_rfl (by omega) (by omega) (by omega))

theorem nativeSide_crossing_uniform_pos (q : Set.Ici (1:ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m → c ≤ nativeSideCrossingProbability q m := by
  obtain ⟨c,hc,hpush⟩ := Push.selfDual_push q 6 (by norm_num) 5 (by norm_num)
  exact ⟨c,hc,fun m hm => (hpush (4*m-1) (by omega)).trans (nativeSide_reference_le q m hm)⟩

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
