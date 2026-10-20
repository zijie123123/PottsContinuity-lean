module

public import PottsContinuity.Thm3.RSW.AnnulusChainScale

/-! Integer translates of local annulus windows fit the exact frozen buffer. -/

@[expose] public section

namespace PottsContinuity.RSW

/-- Lattice centers, with integer horizontal spacing and integer mid-height. -/
def annulusChainCenter (n m l : ℕ) : ℤ × ℤ := ((l*m:ℕ),(n/2:ℕ))

/-- Every radius-8m local sampling window fits in the exact buffered domain.
There is no translation of the ambient FK law in this assertion. -/
theorem annulus_chain_window_in_buffer (α : ℝ) (n m K : ℕ)
    (hscale : 16*m ≤ n) (hspan : (K*m:ℕ) ≤ ⌊α*(n:ℝ)⌋+(m:ℤ))
    (l : ℕ) (hl : l ≤ K) (z : ℤ × ℤ) (hz : z ∈ box (8*m)) :
    (z.1+(annulusChainCenter n m l).1,z.2+(annulusChainCenter n m l).2) ∈
      latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ)) := by
  have hlm : (l*m:ℕ) ≤ (K*m:ℕ) := Nat.mul_le_mul_right m hl
  have hscaleR : 16*(m:ℤ) ≤ n := by exact_mod_cast hscale
  have hlmR : (l:ℤ)*(m:ℤ) ≤ (K:ℤ)*(m:ℤ) := by exact_mod_cast hlm
  have hnonneg : (0:ℤ) ≤ (l:ℤ)*(m:ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hmid : n/2 ≤ n := Nat.div_le_self _ _
  have hmidR : ((n/2:ℕ):ℤ) ≤ n := by exact_mod_cast hmid
  have hmid0 : (0:ℤ) ≤ (n/2:ℕ) := Int.natCast_nonneg _
  simp only [box,Finset.mem_product,Finset.mem_Icc,Nat.cast_mul,Nat.cast_ofNat] at hz
  simp only [latticeRectangle,Finset.mem_product,Finset.mem_Icc,annulusChainCenter,
    Nat.cast_mul,buffered_right_floor_eq]
  push_cast at hspan
  constructor
  · constructor <;> omega
  · constructor <;> omega

/-- The circuit-support boxes, unlike the larger sampling windows, fit inside
the height band of the actual target crossing. -/
theorem annulus_chain_circuit_height_band (n m l : ℕ) (hscale : 16*m ≤ n)
    (z : ℤ × ℤ) (hz : z ∈ box (2*m)) :
    z.2+(annulusChainCenter n m l).2 ∈ Set.Icc (0:ℤ) n := by
  have hmidlo : 2*m ≤ n/2 := (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (by omega)
  have hmidhi : n/2+2*m ≤ n := by omega
  have hmidloR : 2*(m:ℤ) ≤ ((n/2:ℕ):ℤ) := by exact_mod_cast hmidlo
  have hmidhiR : ((n/2:ℕ):ℤ)+2*(m:ℤ) ≤ n := by exact_mod_cast hmidhi
  simp only [box,Finset.mem_product,Finset.mem_Icc,Nat.cast_mul,Nat.cast_ofNat] at hz
  change 0 ≤ z.2+((n/2:ℕ):ℤ) ∧ z.2+((n/2:ℕ):ℤ) ≤ n
  constructor <;> omega

end PottsContinuity.RSW
