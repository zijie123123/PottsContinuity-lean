-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygonCellBoundaryCriterion.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticePolygonFiniteCellFilling
public import PottsContinuity.FKC.Domains.LatticeCells
public import PottsContinuity.FKC.Domains.LatticeEdges
public import PottsContinuity.FKC.Medial.LatticePorts
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open Set
open PottsContinuity.FKC.Medial
open OAI.SLEExactGauge

noncomputable section

variable {m : ℕ} (P : LatticePolygon m)

private theorem segment_coordinate_parameter (δ : PositiveMesh)
    {u v z : ℂ} (hz : z ∈ segment ℝ u v) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z.re / δ.val = (1 - t) * (u.re / δ.val) + t * (v.re / δ.val) ∧
      z.im / δ.val = (1 - t) * (u.im / δ.val) + t * (v.im / δ.val) := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := hz
  refine ⟨t, ht0, ht1, ?_, ?_⟩
  · have hr := congrArg Complex.re hzt
    simp only [Complex.real_smul, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
    calc
      z.re / δ.val = ((1 - t) * u.re + t * v.re) / δ.val := by rw [hr]
      _ = (1 - t) * (u.re / δ.val) + t * (v.re / δ.val) := by ring
  · have hi := congrArg Complex.im hzt
    simp only [Complex.real_smul, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hi
    calc
      z.im / δ.val = ((1 - t) * u.im + t * v.im) / δ.val := by rw [hi]
      _ = (1 - t) * (u.im / δ.val) + t * (v.im / δ.val) := by ring

private theorem int_eq_of_half_bounds {a b : ℤ}
    (hab : (a : ℝ) - 1 / 2 ≤ (b : ℝ))
    (hba : (b : ℝ) ≤ (a : ℝ) + 1 / 2) : a = b := by
  have h₁ : a < b + 1 := by exact_mod_cast (show (a : ℝ) < (b : ℝ) + 1 by linarith)
  have h₂ : b < a + 1 := by exact_mod_cast (show (b : ℝ) < (a : ℝ) + 1 by linarith)
  omega

private theorem int_eq_of_center_interval {a b : ℤ}
    (hab : (a : ℝ) ≤ (b : ℝ) + 1 / 2)
    (hba : (b : ℝ) + 1 / 2 ≤ (a : ℝ) + 1) : a = b := by
  have h₁ : a < b + 1 := by exact_mod_cast (show (a : ℝ) < (b : ℝ) + 1 by linarith)
  have h₂ : b < a + 1 := by exact_mod_cast (show (b : ℝ) < (a : ℝ) + 1 by linarith)
  omega

private theorem no_int_eq_half_int {a b : ℤ}
    (h : (a : ℝ) + 1 / 2 = (b : ℝ)) : False := by
  have hreal : (2 * (a : ℝ) + 1) = 2 * (b : ℝ) := by nlinarith [h]
  have h' : (2 * a + 1 : ℤ) = 2 * b := by exact_mod_cast hreal
  omega

/-- If the transverse segment between the two cells adjacent to e meets a
primal unit bond f, then f is e. -/
private theorem dualSegment_inter_primalBond_eq (δ : PositiveMesh)
    (e f : LatticeBond) {z : ℂ}
    (hdual : z ∈ segment ℝ (latticeCellCenter δ (e.faceBase true))
      (latticeCellCenter δ (e.faceBase false)))
    (hprimal : z ∈ segment ℝ (latticeEmbed δ f.source) (latticeEmbed δ f.target)) :
    e = f := by
  obtain ⟨t, ht0, ht1, hdx, hdy⟩ := segment_coordinate_parameter δ hdual
  obtain ⟨s, hs0, hs1, hpx, hpy⟩ := segment_coordinate_parameter δ hprimal
  rcases e with ⟨⟨x, y⟩, ae⟩
  rcases f with ⟨⟨a, b⟩, af⟩
  cases ae <;> cases af
  · simp only [LatticeBond.faceBase, latticeCellCenter] at hdx hdy
    simp only [LatticeBond.source, LatticeBond.target, latticeEmbed_re,
      latticeEmbed_im] at hpx hpy
    simp only [mul_div_cancel_left₀ _ δ.property.ne'] at hdx hdy hpx hpy
    push_cast at hdx hdy hpx hpy
    ring_nf at hdx hdy hpx hpy
    simp only [div_eq_mul_inv] at hdx hdy hpx hpy ⊢
    have hdxD : z.re / δ.val = (x : ℝ) + 1 / 2 := by
      simpa [div_eq_mul_inv, mul_comm, add_comm] using hdx
    have hdyD : z.im / δ.val = (y : ℝ) + (1 / 2 - t) := by
      simpa [div_eq_mul_inv, mul_comm, add_comm] using hdy
    have hpxD : z.re / δ.val = (a : ℝ) + s := by
      simpa [div_eq_mul_inv, mul_comm, add_comm] using hpx
    have hpyD : z.im / δ.val = (b : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using hpy
    have hdylo : (y : ℝ) - 1 / 2 ≤ z.im / δ.val := by nlinarith [hdyD, ht0, ht1]
    have hdyhi : z.im / δ.val ≤ (y : ℝ) + 1 / 2 := by nlinarith [hdyD, ht0, ht1]
    have hpya := hpyD
    have hdx' := hdxD
    have hpxlo : (a : ℝ) ≤ z.re / δ.val := by nlinarith [hpxD, hs0, hs1]
    have hpxhi : z.re / δ.val ≤ (a : ℝ) + 1 := by nlinarith [hpxD, hs0, hs1]
    have hbaseX : a = x := int_eq_of_center_interval (by rw [hdx'] at hpxlo; exact hpxlo)
      (by rw [hdx'] at hpxhi; exact hpxhi)
    have hdylo' := hdylo
    have hdyhi' := hdyhi
    rw [hpya] at hdylo' hdyhi'
    have hbaseY := int_eq_of_half_bounds (a := y) (b := b) hdylo' hdyhi'
    subst a
    subst b
    rfl
  · simp only [LatticeBond.faceBase, latticeCellCenter] at hdx hdy
    simp only [LatticeBond.source, LatticeBond.target, latticeEmbed_re,
      latticeEmbed_im] at hpx hpy
    simp only [mul_div_cancel_left₀ _ δ.property.ne'] at hdx hdy hpx hpy
    push_cast at hdx hdy hpx hpy
    ring_nf at hdx hdy hpx hpy
    have hdx' : z.re / δ.val = (x : ℝ) + 1 / 2 := by
      simpa [div_eq_mul_inv, mul_comm, add_comm] using hdx
    have hpx' : z.re / δ.val = (a : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using hpx
    exact (no_int_eq_half_int (hdx'.symm.trans hpx')).elim
  · simp only [LatticeBond.faceBase, latticeCellCenter] at hdx hdy
    simp only [LatticeBond.source, LatticeBond.target, latticeEmbed_re,
      latticeEmbed_im] at hpx hpy
    simp only [mul_div_cancel_left₀ _ δ.property.ne'] at hdx hdy hpx hpy
    push_cast at hdx hdy hpx hpy
    ring_nf at hdx hdy hpx hpy
    have hdy' : z.im / δ.val = (y : ℝ) + 1 / 2 := by
      simpa [div_eq_mul_inv, mul_comm, add_comm] using hdy
    have hpy' : z.im / δ.val = (b : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using hpy
    exact (no_int_eq_half_int (hdy'.symm.trans hpy')).elim
  · simp only [LatticeBond.faceBase, latticeCellCenter] at hdx hdy
    simp only [LatticeBond.source, LatticeBond.target, latticeEmbed_re,
      latticeEmbed_im] at hpx hpy
    simp only [mul_div_cancel_left₀ _ δ.property.ne'] at hdx hdy hpx hpy
    push_cast at hdx hdy hpx hpy
    ring_nf at hdx hdy hpx hpy
    have hdxD : z.re / δ.val = (x : ℝ) + (1 / 2 - t) := by
      simpa [div_eq_mul_inv, mul_comm, add_comm] using hdx
    have hdyD : z.im / δ.val = (y : ℝ) + 1 / 2 := by
      simpa [div_eq_mul_inv, mul_comm, add_comm] using hdy
    have hpxD : z.re / δ.val = (a : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using hpx
    have hpyD : z.im / δ.val = (b : ℝ) + s := by
      simpa [div_eq_mul_inv, mul_comm, add_comm] using hpy
    have hdxlo : (x : ℝ) - 1 / 2 ≤ z.re / δ.val := by nlinarith [hdxD, ht0, ht1]
    have hdxhi : z.re / δ.val ≤ (x : ℝ) + 1 / 2 := by nlinarith [hdxD, ht0, ht1]
    have hpylow : (b : ℝ) ≤ z.im / δ.val := by nlinarith [hpyD, hs0, hs1]
    have hpyhi : z.im / δ.val ≤ (b : ℝ) + 1 := by nlinarith [hpyD, hs0, hs1]
    have hdxlo' := hdxlo
    have hdxhi' := hdxhi
    rw [hpxD] at hdxlo' hdxhi'
    have hbaseX := int_eq_of_half_bounds (a := x) (b := a) hdxlo' hdxhi'
    have hpylow' := hpylow
    have hpyhi' := hpyhi
    rw [hdyD] at hpylow' hpyhi'
    have hbaseY := int_eq_of_center_interval (a := b) (b := y) hpylow' hpyhi'
    subst a
    subst b
    rfl
private theorem dualSegment_same_domain_status_of_disjoint (δ : PositiveMesh)
    (e : LatticeBond)
    (hdisj : Disjoint
      (segment ℝ (latticeCellCenter δ (e.faceBase true))
        (latticeCellCenter δ (e.faceBase false))) (P.carrier δ)) :
    (latticeCellCenter δ (e.faceBase true) ∈ P.domain δ) ↔
      (latticeCellCenter δ (e.faceBase false) ∈ P.domain δ) := by
  let C := complexPlaneCoordinates '' P.carrier δ
  let S := complexPlaneCoordinates ''
    (segment ℝ (latticeCellCenter δ (e.faceBase true))
      (latticeCellCenter δ (e.faceBase false)))
  have hs : IsPreconnected S := (convex_segment _ _).isPreconnected.image
    complexPlaneCoordinates complexPlaneCoordinates.continuous.continuousOn
  have hleft : latticeCellCenter δ (e.faceBase true) ∈
      segment ℝ (latticeCellCenter δ (e.faceBase true))
        (latticeCellCenter δ (e.faceBase false)) := left_mem_segment ℝ _ _
  have hright : latticeCellCenter δ (e.faceBase false) ∈
      segment ℝ (latticeCellCenter δ (e.faceBase true))
        (latticeCellCenter δ (e.faceBase false)) := right_mem_segment ℝ _ _
  have hc : complexPlaneCoordinates (latticeCellCenter δ (e.faceBase true)) ∈ S :=
    mem_image_of_mem _ hleft
  have hSC : S ⊆ Cᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    have hzw := complexPlaneCoordinates.injective heq
    subst w
    exact Set.disjoint_left.mp hdisj hz hw
  have hsub := hs.subset_connectedComponentIn hc hSC
  rcases (P.isSeparating_carrier δ).isRegionOf_connectedComponentIn (hSC hc) with hi | he
  · constructor
    · intro _
      change complexPlaneCoordinates (latticeCellCenter δ (e.faceBase false)) ∈
        Schoenflies.inside C
      rw [← hi]
      exact hsub (mem_image_of_mem _ hright)
    · intro _
      change complexPlaneCoordinates (latticeCellCenter δ (e.faceBase true)) ∈
        Schoenflies.inside C
      rw [← hi]
      exact hsub (mem_image_of_mem _ hleft)
  · constructor
    · intro hx
      have hout : complexPlaneCoordinates (latticeCellCenter δ (e.faceBase true)) ∈
          Schoenflies.outside C := by
        rw [← he]
        exact hsub hc
      change complexPlaneCoordinates (latticeCellCenter δ (e.faceBase true)) ∈
        Schoenflies.inside C at hx
      exact (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hx hout).elim
    · intro hy
      have hout : complexPlaneCoordinates (latticeCellCenter δ (e.faceBase false)) ∈
          Schoenflies.outside C := by
        rw [← he]
        exact hsub (mem_image_of_mem _ hright)
      change complexPlaneCoordinates (latticeCellCenter δ (e.faceBase false)) ∈
        Schoenflies.inside C at hy
      exact (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hy hout).elim

/-- Cell membership changes across a dual segment exactly at polygon boundary bonds. -/
theorem cellCenters_differ_iff_boundaryBond (δ : PositiveMesh) (e : LatticeBond) :
    (latticeCellCenter δ (e.faceBase true) ∈ P.domain δ) ≠
      (latticeCellCenter δ (e.faceBase false) ∈ P.domain δ) ↔
    ∃ i : ZMod (m + 3), e = P.boundaryBond i := by
  constructor
  · intro hdiff
    by_contra hnot
    have hdisj : Disjoint
        (segment ℝ (latticeCellCenter δ (e.faceBase true))
          (latticeCellCenter δ (e.faceBase false))) (P.carrier δ) := by
      rw [Set.disjoint_left]
      intro z hzdual hzcarrier
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hzcarrier
      have horient := P.boundaryBond_toSym2 i
      simp only [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target] at horient
      rcases Sym2.eq_iff.mp horient with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
      · have hzprimal : z ∈ segment ℝ (latticeEmbed δ (P.boundaryBond i).source)
            (latticeEmbed δ (P.boundaryBond i).target) := by
          rw [← hsource, ← htarget] at hzi
          simp only [LatticeBond.source, LatticeBond.target]
          exact hzi
        exact hnot ⟨i, dualSegment_inter_primalBond_eq δ e (P.boundaryBond i)
          hzdual hzprimal⟩
      · have hzprimal : z ∈ segment ℝ (latticeEmbed δ (P.boundaryBond i).source)
            (latticeEmbed δ (P.boundaryBond i).target) := by
          rw [← hsource, ← htarget] at hzi
          simp only [LatticeBond.source, LatticeBond.target]
          simpa [segment_symm] using hzi
        exact hnot ⟨i, dualSegment_inter_primalBond_eq δ e (P.boundaryBond i)
          hzdual hzprimal⟩
    exact hdiff (propext (P.dualSegment_same_domain_status_of_disjoint δ e hdisj))
  · rintro ⟨i, rfl⟩
    exact P.boundaryBond_cellCenters_differ δ _ ⟨i, rfl⟩

end
end PottsContinuity.FKC.LatticePolygon
