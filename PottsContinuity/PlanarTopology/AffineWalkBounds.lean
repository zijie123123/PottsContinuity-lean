module

public import PottsContinuity.PlanarTopology.WalkIntersection
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Curves unitInterval Set
noncomputable section

/-- Every convex region containing the original walk vertices contains the
entire straight interpolation, including repeated visits and the empty walk. -/
theorem latticeWalkPath_mem_of_convex (δ : PositiveMesh) {S : Set ℂ} (hS : Convex ℝ S)
    {u v : LatticeVertex} (p : squareLattice.Walk u v)
    (hp : ∀ z ∈ p.support, latticeEmbed δ z ∈ S) (a : I) : latticeWalkPath δ p a ∈ S := by
  obtain ⟨x,y,hx,hy,_,hseg⟩ := latticeWalkPath_range_subset_segments δ p ⟨a,rfl⟩
  rw [Path.range_segment] at hseg
  exact hS.segment_subset (hp x hx) (hp y hy) hseg

/-- A strict affine band and a closed horizontal slab are preserved by
interpolating the original nearest-neighbour walk. -/
theorem latticeWalkPath_affine_band_bounds {u v : LatticeVertex}
    (p : squareLattice.Walk u v) (l r t b H : ℝ)
    (hp : ∀ z ∈ p.support, l ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ r ∧
      |(z.2 : ℝ)-(t*z.1+b)| < H) :
    ∀ a : I, l ≤ (latticeWalkPath ⟨1,by norm_num⟩ p a).re ∧
      (latticeWalkPath ⟨1,by norm_num⟩ p a).re ≤ r ∧
      |(latticeWalkPath ⟨1,by norm_num⟩ p a).im -
        (t*(latticeWalkPath ⟨1,by norm_num⟩ p a).re+b)| < H := by
  let F : ℂ →ᵃ[ℝ] ℝ := (Complex.imLm - t • Complex.reLm).toAffineMap - AffineMap.const ℝ ℂ b
  have hF : ∀ z : ℂ, F z = z.im - (t*z.re+b) := by
    intro z
    change z.im - t*z.re - b = z.im - (t*z.re+b)
    ring
  have hc : Convex ℝ (Complex.re ⁻¹' Icc l r ∩ F ⁻¹' Ioo (-H) H) :=
    ((convex_Icc l r).affine_preimage Complex.reLm.toAffineMap).inter
      ((convex_Ioo (-H) H).affine_preimage F)
  intro a
  have h := latticeWalkPath_mem_of_convex ⟨1,by norm_num⟩ hc p (fun z hz => by
    obtain ⟨hl,hr,hh⟩ := hp z hz
    change (l ≤ (latticeEmbed ⟨1,by norm_num⟩ z).re ∧
      (latticeEmbed ⟨1,by norm_num⟩ z).re ≤ r) ∧
      -H < F (latticeEmbed ⟨1,by norm_num⟩ z) ∧ F (latticeEmbed ⟨1,by norm_num⟩ z) < H
    simpa only [hF,latticeEmbed_re,latticeEmbed_im,one_mul] using ⟨⟨hl,hr⟩,abs_lt.mp hh⟩) a
  change (l ≤ _ ∧ _ ≤ r) ∧ -H < F _ ∧ F _ < H at h
  exact ⟨h.1.1,h.1.2,abs_lt.mpr (by simpa only [hF] using h.2)⟩

end
end PottsContinuity.PlanarTopology
