-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Duality/LatticeEmbedding.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `LatticeEmbedding.lean`.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsContinuity.PD.FK.Lattice
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic

/-!
# The positive-mesh square lattice in the complex plane

The vertex `(x,y)` is embedded as `δ*x + I*δ*y` for a strictly positive real
mesh `δ`. Nearest-neighbor edges have exactly Euclidean length `δ`. A bounded
plane region contains only finitely many embedded vertices, by an explicit
integer-box bound. No boundary approximation or polygon is defined here.
-/

@[expose] public section

namespace PottsContinuity.PD.FK

noncomputable section

/-- A genuine, strictly positive lattice mesh. -/
abbrev PositiveMesh := {δ : ℝ // 0 < δ}

/-- The usual Euclidean embedding of the square lattice at mesh `δ`. -/
def latticeEmbed (δ : PositiveMesh) (v : LatticeVertex) : ℂ :=
  ⟨δ.val * (v.1 : ℝ), δ.val * (v.2 : ℝ)⟩

@[simp] theorem latticeEmbed_re (δ : PositiveMesh) (v : LatticeVertex) :
    (latticeEmbed δ v).re = δ.val * (v.1 : ℝ) := rfl

@[simp] theorem latticeEmbed_im (δ : PositiveMesh) (v : LatticeVertex) :
    (latticeEmbed δ v).im = δ.val * (v.2 : ℝ) := rfl

@[simp] theorem latticeEmbed_zero (δ : PositiveMesh) : latticeEmbed δ 0 = 0 := by
  apply Complex.ext <;> simp only [latticeEmbed_re, latticeEmbed_im, Prod.fst_zero, Prod.snd_zero,
    Int.cast_zero, mul_zero, Complex.zero_re, Complex.zero_im]

end

end PottsContinuity.PD.FK
