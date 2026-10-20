module

public import PottsContinuity.Thm3.RSW.Lemma4PaddedPushComparison
public import PottsContinuity.Thm3.RSW.RectangleBandBooleanBridge

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.RCInfinite
noncomputable section

private theorem floor_nat_product (a n : ℕ) :
    ⌊(a:ℝ)*(n:ℝ)⌋ = (a:ℤ)*(n:ℤ) := by
  rw [← Nat.cast_mul,Int.floor_natCast,Nat.cast_mul]

/-- The exact symmetric reference probability, including both lattice
rounding operations, is the canonical ordinary-rectangle band probability. -/
theorem lemma4_symmetric_reference_eq_canonical (q : Set.Ici (1:ℝ))
    (n : ℕ) (hn : 2 ≤ n) :
    selfDualTopWiredCrossingProbability q
      ((56*(n:ℝ)+1)/(n-1:ℕ)) ((54*(n:ℝ))/(n-1:ℕ)) (n-1) =
    finiteBoundaryEventProbability (PD.FK.latticeRectangle (-56*(n:ℤ)-1,0) (112*n+2) (54*n))
      (selfDualParameters q)
      (BoundaryCondition.wired {v | v.val.1 = -56*(n:ℤ)-1 ∨
        v.val.1 = 56*(n:ℤ)+1 ∨ v.val.2 = ((54*n:ℕ):ℤ)})
      (horizontalCrossing (PD.FK.latticeRectangle (-56*(n:ℤ)-1,0) (112*n+2) (54*n))
        (-56*(n:ℤ)-1) (56*(n:ℤ)+1) 0 (n-1:ℕ)) := by
  have hnpos : (0:ℝ) < (n-1:ℕ) := by exact_mod_cast (show 0 < n-1 by omega)
  have hw : ⌊((56*(n:ℝ)+1)/(n-1:ℕ))*((n-1:ℕ):ℝ)⌋ = 56*(n:ℤ)+1 := by
    rw [div_mul_cancel₀ _ hnpos.ne',Int.floor_add_one]
    exact congrArg (fun z : ℤ => z+1) (floor_nat_product 56 n)
  have hh : ⌊((54*(n:ℝ))/(n-1:ℕ))*((n-1:ℕ):ℝ)⌋ = ((54*n:ℕ):ℤ) := by
    rw [div_mul_cancel₀ _ hnpos.ne']
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using floor_nat_product 54 n
  have hneg : -(56*(n:ℤ)+1) = -56*(n:ℤ)-1 := by omega
  let P (V : Finset LatticeVertex) : ℝ := finiteBoundaryEventProbability V (selfDualParameters q)
    (BoundaryCondition.wired {v | v.val.1 = -56*(n:ℤ)-1 ∨
      v.val.1 = 56*(n:ℤ)+1 ∨ v.val.2 = ((54*n:ℕ):ℤ)})
    (horizontalCrossing V (-56*(n:ℤ)-1) (56*(n:ℤ)+1) 0 (n-1:ℕ))
  have hd : topWiredRectangle ((56*(n:ℝ)+1)/(n-1:ℕ))
      ((54*(n:ℝ))/(n-1:ℕ)) (n-1) =
      PD.FK.latticeRectangle (-56*(n:ℤ)-1,0) (112*n+2) (54*n) := by
    unfold topWiredRectangle
    rw [hw,hh]
    have hd := Foundations.pdRectangle_eq_frozenRectangle_of_corners
      (-56*(n:ℤ)-1) (56*(n:ℤ)+1) 0 ((54*n:ℕ):ℤ) (by omega) (by omega)
    have hwidth : (56*(n:ℤ)+1-(-56*(n:ℤ)-1)).toNat = 112*n+2 := by omega
    have hheight : (((54*n:ℕ):ℤ)-0).toNat = 54*n := by omega
    rw [hwidth,hheight] at hd
    rw [hneg]
    exact hd.symm
  have hs : selfDualTopWiredCrossingProbability q
      ((56*(n:ℝ)+1)/(n-1:ℕ)) ((54*(n:ℝ))/(n-1:ℕ)) (n-1) =
      P (topWiredRectangle ((56*(n:ℝ)+1)/(n-1:ℕ)) ((54*(n:ℝ))/(n-1:ℕ)) (n-1)) := by
    unfold selfDualTopWiredCrossingProbability topWiredRectangleBoundary
    rw [hw,hh]
    rw [hneg]
  exact hs.trans (congrArg P hd)

end
end PottsContinuity.RSW
