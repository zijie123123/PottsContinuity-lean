-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/CorrLength/RotatedLattice.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.FK.Lattice
public import PottsContinuity.PD.Defs.DiagonalSite
public import Mathlib.Tactic

/-!
# The rotated lattice and its square-lattice coordinates

The carrier `rotatedVertex` is the even-coordinate-sum sublattice of `ℤ²`.
The map to square-lattice coordinates sends `(i,j)` to
`((i+j)/2, (j-i)/2)`.
-/

@[expose] public section

namespace PottsContinuity.PD.CorrLength

/-- Vertices of the rotated lattice: pairs of integers with even sum. -/
abbrev RotatedVertex := {z : ℤ × ℤ // Even (z.1 + z.2)}

/-- The rotated-lattice coordinates of a square-lattice vertex. -/
def squareToRotatedVertex (x : ℤ × ℤ) : RotatedVertex :=
  ⟨(x.1 - x.2, x.1 + x.2), ⟨x.1, by simp⟩⟩

/-- The square-lattice coordinates of a rotated-lattice vertex. -/
def rotatedToSquareVertex (x : RotatedVertex) : ℤ × ℤ :=
  ((x.1.1 + x.1.2) / 2, (x.1.2 - x.1.1) / 2)

@[simp] theorem rotatedToSquare_squareToRotated (x : ℤ × ℤ) :
    rotatedToSquareVertex (squareToRotatedVertex x) = x := by
  rcases x with ⟨a, b⟩
  simp only [rotatedToSquareVertex, squareToRotatedVertex]
  apply Prod.ext
  · rw [show a - b + (a + b) = 2 * a by ring]
    exact Int.mul_ediv_cancel_left (a := 2) a (by norm_num)
  · rw [show a + b - (a - b) = 2 * b by ring]
    exact Int.mul_ediv_cancel_left (a := 2) b (by norm_num)

theorem squareToRotated_rotatedToSquare (x : RotatedVertex) :
    squareToRotatedVertex (rotatedToSquareVertex x) = x := by
  apply Subtype.ext
  rcases x with ⟨⟨i, j⟩, hij⟩
  obtain ⟨k, hk⟩ := hij
  change (((i + j) / 2 - (j - i) / 2, (i + j) / 2 + (j - i) / 2)) = (i, j)
  have hk' : i + j = 2 * k := by omega
  have h₁ : (i + j) / 2 = k := by
    rw [hk']
    exact Int.mul_ediv_cancel_left (a := 2) k (by norm_num)
  have h₂ : (j - i) / 2 = j - k := by
    rw [show j - i = 2 * (j - k) by omega]
    exact Int.mul_ediv_cancel_left (a := 2) (j - k) (by norm_num)
  rw [h₁, h₂]
  congr 1 <;> omega

/-- The vertex bijection from the rotated lattice to `ℤ²`. -/
def rotatedVertexEquiv : RotatedVertex ≃ ℤ × ℤ where
  toFun := rotatedToSquareVertex
  invFun := squareToRotatedVertex
  left_inv := squareToRotated_rotatedToSquare
  right_inv := rotatedToSquare_squareToRotated

@[simp] theorem diagonalSite_even (m : ℕ) :
    PottsContinuity.PD.diagonalSite (2 * m) = ((m : ℤ), (m : ℤ)) := by
  simp [PottsContinuity.PD.diagonalSite]

@[simp] theorem diagonalSite_odd (m : ℕ) :
    PottsContinuity.PD.diagonalSite (2 * m + 1) = ((m : ℤ), (m : ℤ)) := by
  simp [PottsContinuity.PD.diagonalSite]
  omega

@[simp] theorem rotatedVertexEquiv_apply_origin_to_even_site (m : ℕ) :
    rotatedVertexEquiv ⟨(0, 2 * (m : ℤ)), ⟨(m : ℤ), by ring⟩⟩ =
      ((m : ℤ), (m : ℤ)) := by
  simp [rotatedVertexEquiv, rotatedToSquareVertex]

end PottsContinuity.PD.CorrLength
