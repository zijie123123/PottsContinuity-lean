module

public import PottsContinuity.Thm3.Prop4.TiltedWindow
public import PottsContinuity.PD.FK.Lattice

/-!
# Digital boundary geometry of the tilted strip

The supporting lines need not contain lattice vertices. For |t|≤1, intrinsic
top means height>n-1 and intrinsic bottom means height<1. The source's free
arc is the part of the digital bottom not already assigned to a wired side.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

private theorem neighbour_cases {z y : ℤ × ℤ} (h : squareLattice.Adj z y) :
    y = (z.1+1,z.2) ∨ y = (z.1-1,z.2) ∨
      y = (z.1,z.2+1) ∨ y = (z.1,z.2-1) := by
  change PD.FK.squareLattice.Adj z y at h
  rw [PD.FK.squareLattice_adj_iff] at h
  simp only [Prod.ext_iff]
  omega

/-- Each nearest-neighbour step changes tilted height by at most one when |t|≤1. -/
theorem tiltedHeight_step_le {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    {z y : ℤ × ℤ} (h : squareLattice.Adj z y) :
    tiltedHeight t y ≤ tiltedHeight t z + 1 := by
  rcases neighbour_cases h with rfl | rfl | rfl | rfl
  all_goals
    dsimp [tiltedHeight]
    push_cast
    nlinarith only [ht.1, ht.2]

/-- Upper digital boundary characterization, including irrational slopes. -/
theorem tiltedTop_iff_height (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (z : ℤ × ℤ) : tiltedTop n t z ↔ (n : ℝ) < tiltedHeight t z + 1 := by
  constructor
  · rintro ⟨y, hzy, hy⟩
    exact hy.trans_le (tiltedHeight_step_le ht hzy)
  · intro hz
    refine ⟨(z.1,z.2+1), ?_, ?_⟩
    · change |z.1-z.1| + |z.2-(z.2+1)| = 1
      simp
    · dsimp [tiltedHeight] at hz ⊢
      push_cast
      linarith only [hz]

/-- The topmost integer in every column is an actual strip vertex when n≥1. -/
theorem top_column_mem (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (k : ℤ) :
    (k, ⌊t*(k : ℝ)+(n : ℝ)⌋) ∈ tiltedStripVertices n t := by
  have hlo := Int.lt_floor_add_one (t*(k : ℝ)+(n : ℝ))
  have hhi := Int.floor_le (t*(k : ℝ)+(n : ℝ))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor <;> dsimp [tiltedHeight] <;> linarith only [hlo, hhi, hnR]

/-- The same topmost integer has an actual neighbour above the supporting line. -/
theorem top_column_isTop (n : ℕ) (t : ℝ) (k : ℤ) :
    tiltedTop n t (k, ⌊t*(k : ℝ)+(n : ℝ)⌋) := by
  refine ⟨(k, ⌊t*(k : ℝ)+(n : ℝ)⌋+1), ?_, ?_⟩
  · change |k-k| + |⌊t*(k : ℝ)+(n : ℝ)⌋-(⌊t*(k : ℝ)+(n : ℝ)⌋+1)| = 1
    simp
  · have h := Int.lt_floor_add_one (t*(k : ℝ)+(n : ℝ))
    dsimp [tiltedHeight]
    push_cast
    linarith only [h]

end PottsContinuity.Thm3.Prop4
