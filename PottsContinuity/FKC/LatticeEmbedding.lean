-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `LatticeEmbedding.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Lattice
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

namespace PottsContinuity.FKC

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

theorem latticeEmbed_injective (δ : PositiveMesh) : Function.Injective (latticeEmbed δ) := by
  intro u v h
  apply Prod.ext
  · have hre := congrArg Complex.re h
    have hcoord : (u.1 : ℝ) = (v.1 : ℝ) :=
      mul_left_cancel₀ δ.property.ne' hre
    exact_mod_cast hcoord
  · have him := congrArg Complex.im h
    have hcoord : (u.2 : ℝ) = (v.2 : ℝ) :=
      mul_left_cancel₀ δ.property.ne' him
    exact_mod_cast hcoord

@[simp] theorem latticeEmbed_zero (δ : PositiveMesh) : latticeEmbed δ 0 = 0 := by
  apply Complex.ext <;> simp only [latticeEmbed_re, latticeEmbed_im, Prod.fst_zero, Prod.snd_zero,
    Int.cast_zero, mul_zero, Complex.zero_re, Complex.zero_im]

theorem abs_fst_le_norm_div_mesh (δ : PositiveMesh) (v : LatticeVertex) :
    |(v.1 : ℝ)| ≤ ‖latticeEmbed δ v‖ / δ.val := by
  apply (le_div_iff₀ δ.property).mpr
  calc
    |(v.1 : ℝ)| * δ.val = |(latticeEmbed δ v).re| := by
      rw [latticeEmbed_re, abs_mul, abs_of_pos δ.property, mul_comm]
    _ ≤ ‖latticeEmbed δ v‖ := Complex.abs_re_le_norm _

theorem abs_snd_le_norm_div_mesh (δ : PositiveMesh) (v : LatticeVertex) :
    |(v.2 : ℝ)| ≤ ‖latticeEmbed δ v‖ / δ.val := by
  apply (le_div_iff₀ δ.property).mpr
  calc
    |(v.2 : ℝ)| * δ.val = |(latticeEmbed δ v).im| := by
      rw [latticeEmbed_im, abs_mul, abs_of_pos δ.property, mul_comm]
    _ ≤ ‖latticeEmbed δ v‖ := Complex.abs_im_le_norm _

/-- Every bounded plane set has all its lattice preimages in one finite integer box. -/
theorem exists_latticeBox_of_isBounded (δ : PositiveMesh) {S : Set ℂ}
    (hS : Bornology.IsBounded S) :
    ∃ r : ℕ, latticeEmbed δ ⁻¹' S ⊆ (latticeBox 0 r : Set LatticeVertex) := by
  obtain ⟨M, hM⟩ := hS.exists_norm_le
  obtain ⟨r, hr⟩ := exists_nat_gt (M / δ.val)
  refine ⟨r, ?_⟩
  intro v hv
  have hnorm : ‖latticeEmbed δ v‖ ≤ M := hM _ hv
  have hdiv : ‖latticeEmbed δ v‖ / δ.val ≤ M / δ.val :=
    div_le_div_of_nonneg_right hnorm δ.property.le
  have hx : |(v.1 : ℝ)| < (r : ℝ) :=
    ((abs_fst_le_norm_div_mesh δ v).trans hdiv).trans_lt hr
  have hy : |(v.2 : ℝ)| < (r : ℝ) :=
    ((abs_snd_le_norm_div_mesh δ v).trans hdiv).trans_lt hr
  rw [Finset.mem_coe, mem_latticeBox]
  simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, zero_add]
  constructor
  · constructor
    · exact_mod_cast (abs_lt.mp hx).1.le
    · exact_mod_cast (abs_lt.mp hx).2.le
  · constructor
    · exact_mod_cast (abs_lt.mp hy).1.le
    · exact_mod_cast (abs_lt.mp hy).2.le

/-- Bounded Euclidean sets contain only finitely many vertices of a positive-mesh lattice. -/
theorem finite_preimage_latticeEmbed_of_isBounded (δ : PositiveMesh) {S : Set ℂ}
    (hS : Bornology.IsBounded S) : (latticeEmbed δ ⁻¹' S).Finite := by
  obtain ⟨r, hr⟩ := exists_latticeBox_of_isBounded δ hS
  exact (latticeBox 0 r).finite_toSet.subset hr

end

end PottsContinuity.FKC
