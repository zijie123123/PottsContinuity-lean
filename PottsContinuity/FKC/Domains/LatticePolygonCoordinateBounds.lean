-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygonCoordinateBounds.lean`, with
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

private theorem carrier_re_le_of_vertex_bound (δ : PositiveMesh) (R : ℤ)
    (hvertex : ∀ i : ZMod (m + 3), (P.vertex i).1 ≤ R)
    {z : ℂ} (hz : z ∈ P.carrier δ) : z.re ≤ δ.val * (R : ℝ) := by
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
  rw [segment_eq_image] at hzi
  obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := hzi
  have hre := congrArg Complex.re hzt
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    latticeEmbed_re] at hre
  have hleft : ((P.vertex i).1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hvertex i
  have hright : ((P.vertex (i + 1)).1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hvertex (i + 1)
  have hcombo : (1 - t) * ((P.vertex i).1 : ℝ) +
      t * ((P.vertex (i + 1)).1 : ℝ) ≤ (R : ℝ) := by
    nlinarith [hleft, hright]
  calc
    z.re = δ.val * ((1 - t) * ((P.vertex i).1 : ℝ) +
        t * ((P.vertex (i + 1)).1 : ℝ)) := by rw [← hre]; ring
    _ ≤ δ.val * (R : ℝ) := mul_le_mul_of_nonneg_left hcombo δ.property.le

/-- Any point strictly to the right of the polygon's vertex-coordinate bound
belongs to the actual unbounded exterior Jordan region. -/
theorem exterior_of_re_gt_vertex_bound (δ : PositiveMesh) (R : ℤ)
    (hvertex : ∀ i : ZMod (m + 3), (P.vertex i).1 ≤ R)
    {z : ℂ} (hz : δ.val * (R : ℝ) < z.re) : z ∈ P.exterior δ := by
  let C : Set Plane := complexPlaneCoordinates '' P.carrier δ
  let q : Plane := complexPlaneCoordinates z
  let ray : ℝ → Plane := fun t => Plane.mk (q 0 + t) (q 1)
  let S : Set Plane := ray '' Ici (0 : ℝ)
  have hraycont : Continuous ray := by
    dsimp [ray]
    fun_prop
  have hS : IsPreconnected S := isPreconnected_Ici.image ray hraycont.continuousOn
  have hq : q ∈ S := by
    have hzero : ray 0 = q := by ext i; fin_cases i <;> simp [ray, q]
    rw [← hzero]
    exact mem_image_of_mem ray (show (0 : ℝ) ∈ Ici 0 by simp)
  have hSC : S ⊆ Cᶜ := by
    rintro w ⟨t, ht, rfl⟩ hwC
    obtain ⟨w', hw', hcoord⟩ := hwC
    have hbound := P.carrier_re_le_of_vertex_bound δ R hvertex hw'
    have hcoord0 := congrArg (fun p : Plane => p 0) hcoord
    have hq0 : q 0 = z.re := rfl
    have hstrict : δ.val * (R : ℝ) < q 0 := by simpa [hq0] using hz
    simp [ray] at hcoord0
    have hreal : w'.re = q 0 + t := by change w'.re = q 0 + t at hcoord0; exact hcoord0
    have ht0 : 0 ≤ t := ht
    nlinarith
  have hcomponent := hS.subset_connectedComponentIn hq hSC
  have hnotBounded : ¬ Bornology.IsBounded (connectedComponentIn Cᶜ q) := by
    intro hbounded
    obtain ⟨M, hM⟩ := hbounded.exists_norm_le
    have hMnonneg : 0 ≤ M := le_trans (norm_nonneg q) (hM q (hcomponent hq))
    have hthreshold : 0 < M + |q 0| + 1 := by positivity
    obtain ⟨n, hn⟩ := exists_nat_gt (M + |q 0| + 1)
    have hnmem : (n : ℝ) ∈ Ici (0 : ℝ) := by
      exact le_of_lt (lt_trans hthreshold hn)
    have hnray : ray n ∈ S := mem_image_of_mem ray hnmem
    have hcomp := hcomponent hnray
    have hnorm := hM (ray n) hcomp
    have hcoordle := Plane.supNorm_le_norm (ray n)
    have hfirst : |(ray n) 0| ≤ Plane.supNorm (ray n) := le_max_left _ _
    have hncoordinate : M < (ray n) 0 := by
      dsimp [ray]
      have hq0 : -|q 0| ≤ q 0 := neg_abs_le _
      nlinarith
    have hpositive : 0 ≤ (ray n) 0 := le_trans hMnonneg hncoordinate.le
    have habs : |(ray n) 0| = (ray n) 0 := abs_of_nonneg hpositive
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
