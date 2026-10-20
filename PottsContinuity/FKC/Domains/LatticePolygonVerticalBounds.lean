-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygonVerticalBounds.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.PolygonDomain
public import PottsContinuity.FKC.Domains.LatticeCells
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open Set OAI.SLEExactGauge Schoenflies

noncomputable section

variable {m : ℕ} (P : LatticePolygon m)

private theorem carrier_im_le_of_vertex_bound (δ : PositiveMesh) (R : ℤ)
    (hvertex : ∀ i : ZMod (m + 3), (P.vertex i).2 ≤ R)
    {z : ℂ} (hz : z ∈ P.carrier δ) : z.im ≤ δ.val * (R : ℝ) := by
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
  rw [segment_eq_image] at hzi
  obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := hzi
  have him := congrArg Complex.im hzt
  simp only [Complex.real_smul, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    latticeEmbed_im] at him
  have hleft : ((P.vertex i).2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hvertex i
  have hright : ((P.vertex (i + 1)).2 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hvertex (i + 1)
  have hcombo : (1 - t) * ((P.vertex i).2 : ℝ) +
      t * ((P.vertex (i + 1)).2 : ℝ) ≤ (R : ℝ) := by nlinarith [hleft, hright]
  calc
    z.im = δ.val * ((1 - t) * ((P.vertex i).2 : ℝ) +
        t * ((P.vertex (i + 1)).2 : ℝ)) := by rw [← him]; ring
    _ ≤ δ.val * (R : ℝ) := mul_le_mul_of_nonneg_left hcombo δ.property.le

/-- A point above a bound on every polygon vertex lies in the actual exterior. -/
theorem exterior_of_im_gt_vertex_bound (δ : PositiveMesh) (R : ℤ)
    (hvertex : ∀ i : ZMod (m + 3), (P.vertex i).2 ≤ R)
    {z : ℂ} (hz : δ.val * (R : ℝ) < z.im) : z ∈ P.exterior δ := by
  let C : Set Plane := complexPlaneCoordinates '' P.carrier δ
  let q : Plane := complexPlaneCoordinates z
  let ray : ℝ → Plane := fun t => Plane.mk (q 0) (q 1 + t)
  let S : Set Plane := ray '' Ici (0 : ℝ)
  have hraycont : Continuous ray := by dsimp [ray]; fun_prop
  have hS : IsPreconnected S := isPreconnected_Ici.image ray hraycont.continuousOn
  have hq : q ∈ S := by
    have hzero : ray 0 = q := by ext i; fin_cases i <;> simp [ray, q]
    rw [← hzero]
    exact mem_image_of_mem ray (show (0 : ℝ) ∈ Ici 0 by simp)
  have hSC : S ⊆ Cᶜ := by
    rintro w ⟨t, ht, rfl⟩ hwC
    obtain ⟨w', hw', hcoord⟩ := hwC
    have hbound := P.carrier_im_le_of_vertex_bound δ R hvertex hw'
    have hcoord1 := congrArg (fun p : Plane => p 1) hcoord
    have hq1 : q 1 = z.im := rfl
    have hstrict : δ.val * (R : ℝ) < q 1 := by simpa [hq1] using hz
    simp [ray] at hcoord1
    have hreal : w'.im = q 1 + t := by change w'.im = q 1 + t at hcoord1; exact hcoord1
    have ht0 : 0 ≤ t := ht
    nlinarith
  have hcomponent := hS.subset_connectedComponentIn hq hSC
  have hnotBounded : ¬ Bornology.IsBounded (connectedComponentIn Cᶜ q) := by
    intro hbounded
    obtain ⟨M, hM⟩ := hbounded.exists_norm_le
    have hMnonneg : 0 ≤ M := le_trans (norm_nonneg q) (hM q (hcomponent hq))
    have hthreshold : 0 < M + |q 1| + 1 := by positivity
    obtain ⟨n, hn⟩ := exists_nat_gt (M + |q 1| + 1)
    have hnmem : (n : ℝ) ∈ Ici (0 : ℝ) := by exact le_of_lt (lt_trans hthreshold hn)
    have hnray : ray n ∈ S := mem_image_of_mem ray hnmem
    have hcomp := hcomponent hnray
    have hnorm := hM (ray n) hcomp
    have hcoordle := Plane.supNorm_le_norm (ray n)
    have hsecond : |(ray n) 1| ≤ Plane.supNorm (ray n) := le_max_right _ _
    have hncoordinate : M < (ray n) 1 := by
      dsimp [ray]
      have hq1 : -|q 1| ≤ q 1 := neg_abs_le _
      nlinarith
    have hpositive : 0 ≤ (ray n) 1 := le_trans hMnonneg hncoordinate.le
    have habs : |(ray n) 1| = (ray n) 1 := abs_of_nonneg hpositive
    linarith
  have hregion := (P.isSeparating_carrier δ).isRegionOf_connectedComponentIn (hSC hq)
  rcases hregion with hinside | houtside
  · have hbdd := (P.isSeparating_carrier δ).isBounded_inside
    exact False.elim (hnotBounded (by rw [hinside]; exact hbdd))
  · change complexPlaneCoordinates z ∈ outside C
    rw [← houtside]
    exact hcomponent hq

end
end PottsContinuity.FKC.LatticePolygon
