module

public import PottsContinuity.Thm3.RSW.ReflectedChain
public import PottsContinuity.Thm3.RSW.PairStrict

/-!
# A bounded reflected chain at every intermediate scale

The source lists fifteen translates, some outside the ambient box. Use
2*ceil(n/m)≤14 adjacent doubled-square blocks instead. The whole chain lies
within horizontal distance 4n, so local free comparison is valid in box(8n).
-/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK

/-- Exact integer choice for the corrected reflected chain length. -/
theorem exists_corridor_half_count (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnm : n ≤ 7*m) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ 7 ∧ n ≤ h*m ∧ h*m < n+m := by
  let h := (n+m-1)/m
  have hrem := Nat.mod_lt (n+m-1) (show 0 < m from hm)
  have heq : h*m+(n+m-1)%m = n+m-1 := by
    simpa only [h,Nat.mul_comm] using Nat.div_add_mod (n+m-1) m
  have hlow : n ≤ h*m := by omega
  have hprod : h*m ≤ n+m-1 := Nat.div_mul_le_self _ _
  have hlt : h < 8 := (Nat.div_lt_iff_lt_mul (show 0 < m from hm)).mpr (by omega)
  refine ⟨h,?_,by omega,hlow,by omega⟩
  apply Nat.one_le_iff_ne_zero.mpr
  intro hh
  rw [hh,zero_mul] at hlow
  omega

/-- The corrected common-box corridor bound. The band may be placed anywhere
vertically inside the ambient box. Local translated free laws are compared
with the common law; ambient translation invariance is not assumed. -/
theorem squarePair_pow_twentyEight_le_box_corridor (θ : Parameters)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m < n) (hnm : n ≤ 7*m)
    (i j : Fin (m+1)) (b : ℤ)
    (hb0 : -(8*(n:ℤ)) ≤ b) (hb1 : b+(m:ℤ) ≤ 8*(n:ℤ)) :
    (squarePairProbability θ m i j)^28 ≤
      finiteBoundaryEventProbability (box (8*n)) θ (frozenBoundaryCondition (box (8*n)) 0)
        (horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ)) b (b+(m:ℤ))) := by
  obtain ⟨h,hh,h7,hcover,hspan⟩ := exists_corridor_half_count n m hn hm hnm
  have hcoverR : (n:ℤ) ≤ (h:ℤ)*(m:ℤ) := by exact_mod_cast hcover
  have hspanR : (h:ℤ)*(m:ℤ) < (n:ℤ)+(m:ℤ) := by exact_mod_cast hspan
  have hmR : (m:ℤ) < (n:ℤ) := by exact_mod_cast hmn
  have hnR : (1:ℤ) ≤ n := by exact_mod_cast hn
  let a := -2*(m:ℤ)*(h:ℤ)
  have hband : latticeRectangle a (a+2*(m:ℤ)*(2*h:ℕ)) b (b+(m:ℤ)) ⊆ box (8*n) := by
    intro z hz
    simp only [latticeRectangle,box,Finset.mem_product,Finset.mem_Icc,
      Nat.cast_mul,Nat.cast_ofNat] at hz ⊢
    dsimp only [a] at hz
    constructor
    · constructor <;> nlinarith only [hz.1.1,hz.1.2,hspanR,hmR,hnR]
    · constructor <;> omega
  have hchain := squarePair_pow_le_horizontalCrossing_of_reflected_chain θ (box (8*n)) m i j
    (2*h) (by omega) a b (-2*(n:ℤ)) (2*(n:ℤ))
    (by dsimp [a]; nlinarith only [hcoverR]) (by omega)
    (by dsimp [a]; nlinarith only [hcoverR]) hband
  exact (pow_le_pow_of_le_one (squarePairProbability_nonneg θ m i j)
    (squarePairProbability_lt_one θ m hm i j).le (by omega : 2*(2*h) ≤ 28)).trans hchain

end PottsContinuity.RSW
