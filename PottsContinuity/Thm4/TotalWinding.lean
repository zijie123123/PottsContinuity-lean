module

public import PottsContinuity.Thm4.SourceNormalization
public import PottsContinuity.Thm4.ExteriorWinding

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

/-- Summing over the full retained port carrier leaves exactly the actual source
winding. Every uncut corner cancels, and the terminal has zero winding. -/
theorem total_signed_winding_sum (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    (∑ c : ParafermionicCoverFinitePort n,
      (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
        parafermionicCoverPathWindingAtom n hn A (c, true)) = 2 * Real.pi := by
  classical
  let C := parafermionicCoverFiniteCornerPairPerm n
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  have hs : parafermionicCoverIncomingPrimalLeft s.1 = true := by
    simp [s, parafermionicCoverFiniteOriginCornerPort_val,
      parafermionicCoverIncomingPrimalLeft_origin]
  have hCs : parafermionicCoverIncomingPrimalLeft (C s).1 = false := by
    change parafermionicCoverIncomingPrimalLeft (parafermionicCoverCornerPair s.1) = false
    rw [parafermionicCoverIncomingPrimalLeft_cornerPair, hs]
    rfl
  have h := sum_signed_eq_incoming_pairs C
    (fun c => parafermionicCoverIncomingPrimalLeft c.1)
    (fun c => parafermionicCoverIncomingPrimalLeft_cornerPair c.1)
    (fun _ => True) (fun _ => Iff.rfl)
    (fun c => parafermionicCoverPathWindingAtom n hn A (c, true))
  simp only [ite_mul, one_mul, neg_one_mul]
  simp only [ite_true, true_and] at h
  rw [h]
  have hterm : ∀ c : ParafermionicCoverFinitePort n,
      (if parafermionicCoverIncomingPrimalLeft c.1 then
        parafermionicCoverPathWindingAtom n hn A (c, true) -
          parafermionicCoverPathWindingAtom n hn A (C c, true) else 0) =
      if c = s then 2 * Real.pi else 0 := by
    intro c
    by_cases heq : c = s
    · subst c
      simp only [hs, ↓reduceIte]
      change parafermionicCoverPathWindingAtom n hn A
        (parafermionicCoverFiniteOriginCornerPort n hn, true) -
        parafermionicCoverPathWindingAtom n hn A
          (parafermionicCoverFiniteCornerPairPerm n
            (parafermionicCoverFiniteOriginCornerPort n hn), true) = _
      rw [pathWindingAtom_source, parafermionicCoverPathWindingAtom_target, sub_zero]
    · rw [ite_eq_right heq]
      by_cases hf : parafermionicCoverIncomingPrimalLeft c.1 = true
      · rw [ite_eq_left hf]
        have hc : c ≠ C s := by
          intro hh
          rw [hh, hCs] at hf
          cases hf
        exact sub_eq_zero.mpr
          (parafermionicCoverPathWindingAtom_corner_eq_of_not_cut n hn A c ⟨heq, hc⟩)
      · exact ite_eq_right hf
  simp_rw [hterm]
  simp

end
end PottsContinuity.Thm4
