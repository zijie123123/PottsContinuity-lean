-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverBranchCorridorCoefficient.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceOrientedBoundary
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCorridorAvoidance
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

 theorem branchCorridor_face_mem (n : ℕ) (hn : 4 ≤ n)
    (x y : ℤ) (hxlo : -3 ≤ x) (hxhi : x ≤ 0)
    (hylo : 0 ≤ y) (hyhi : y ≤ 1) :
    ((x,y),0) ∈ parafermionicCoverFiniteOrdinaryFaces n := by
  apply (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),0)).2
  change -(n : ℤ) ≤ x ∧ x < (n : ℤ) ∧ -(n : ℤ) ≤ y ∧ y < (n : ℤ) ∧
    -((n ^ 5 : ℕ) : ℤ) ≤ 0 ∧ 0 ≤ ((n ^ 5 : ℕ) : ℤ) ∧
    (x,y) ≠ (0,-1) ∧ (x = 0 ∧ y < -1 → 0 < ((n ^ 5 : ℕ) : ℤ))
  have hpow : 0 ≤ ((n ^ 5 : ℕ) : ℤ) := Int.natCast_nonneg _
  exact ⟨by omega, by omega, by omega, by omega, by omega, hpow,
    by intro h; rcases h with ⟨hx,hy⟩; omega,
    by intro h; rcases h with ⟨_,hy⟩; omega⟩

def branchCorridorFace (n : ℕ) (hn : 4 ≤ n) (x y : ℤ)
    (hxlo : -3 ≤ x) (hxhi : x ≤ 0) (hylo : 0 ≤ y) (hyhi : y ≤ 1) :
    ParafermionicCoverFiniteFaceTopIndex n :=
  ⟨((x,y),0), branchCorridor_face_mem n hn x y hxlo hxhi hylo hyhi⟩

 theorem branchCorridor_vertex_mem (n : ℕ) (hn : 4 ≤ n)
    (x y : ℤ) (hxlo : -3 ≤ x) (hxhi : x ≤ 1)
    (hylo : 0 ≤ y) (hyhi : y ≤ 2) :
    ((x,y),0) ∈ parafermionicCoverBoxVertices n := by
  apply (parafermionicCoverBoxVertices_mem n ((x,y),0)).2
  change -(n : ℤ) ≤ x ∧ x ≤ (n : ℤ) ∧ -(n : ℤ) ≤ y ∧ y ≤ (n : ℤ) ∧
    -((n ^ 5 : ℕ) : ℤ) ≤ 0 ∧ 0 ≤ ((n ^ 5 : ℕ) : ℤ)
  have hpow : 0 ≤ ((n ^ 5 : ℕ) : ℤ) := Int.natCast_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, hpow⟩
  · have : -(n : ℤ) ≤ -3 := by omega
    omega
  · omega
  · omega
  · omega
  · omega

def branchCorridorVertex (n : ℕ) (hn : 4 ≤ n) (x y : ℤ)
    (hxlo : -3 ≤ x) (hxhi : x ≤ 1) (hylo : 0 ≤ y) (hyhi : y ≤ 2) :
    ParafermionicCoverBoxVertex n :=
  ⟨((x,y),0), branchCorridor_vertex_mem n hn x y hxlo hxhi hylo hyhi⟩

private theorem branchCorridor_positiveCount_eq_ite {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n)
    (f : ParafermionicCoverFiniteFaceTopIndex n)
    (hd : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts f.1) :
    parafermionicCoverFacePositiveDartCount S u v = if f ∈ S then 1 else 0 := by
  classical
  have hunique : ∀ i : ParafermionicCoverFiniteFaceTopIndex n,
      (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 → i = f := by
    intro i hi
    apply Subtype.ext
    exact parafermionicCoverFiniteFaceDart_unique n i.2 f.2 hi hd
  have hfilter : S.filter
      (fun i => (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1) =
      if f ∈ S then {f} else ∅ := by
    ext i
    by_cases hfi : f ∈ S
    · simp only [Finset.mem_filter, hfi, ite_eq_left, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hiD⟩
        exact hunique i hiD
      · rintro rfl
        exact ⟨hfi, hd⟩
    · simp only [Finset.mem_filter, hfi]
      constructor
      · rintro ⟨hiS, hiD⟩
        exact (hfi ((hunique i hiD).symm ▸ hiS)).elim
      · intro hi
        contradiction
  unfold parafermionicCoverFacePositiveDartCount
  rw [hfilter]
  by_cases hfi : f ∈ S <;> simp [hfi]

private theorem branchCorridor_zero_coeff_face_iff {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n)
    (f g : ParafermionicCoverFiniteFaceTopIndex n)
    (hfg : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts f.1)
    (hgf : (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts g.1)
    (hzero : parafermionicCoverFaceBoundaryCoefficient S u v = 0) :
    f ∈ S ↔ g ∈ S := by
  have hpos := branchCorridor_positiveCount_eq_ite S u v f hfg
  have hneg := branchCorridor_positiveCount_eq_ite S v u g hgf
  unfold parafermionicCoverFaceBoundaryCoefficient at hzero
  rw [hpos, hneg] at hzero
  by_cases hf : f ∈ S
  · by_cases hg : g ∈ S
    · simp [hf, hg]
    · norm_num [hf, hg] at hzero
  · by_cases hg : g ∈ S
    · norm_num [hf, hg] at hzero
    · simp [hf, hg]

private theorem branchCorridor_no_missing_reverse_dart {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n)
    (hd : (((1,0),0),((0,0),0)) ∈ parafermionicCoverFiniteFaceDarts i.1) : False := by
  rcases i with ⟨⟨⟨x,y⟩,k⟩,hi⟩
  have hcoord := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),k)).mp hi
  rcases hcoord with ⟨_,_,_,_,_,_,hnot,_⟩
  change (x,y) ≠ (0,-1) at hnot
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert,
    Finset.mem_singleton, parafermionicCoverFaceRightLift_formula,
    parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula] at hd
  rcases hd with h | h | h | h
  · have hsx := congrArg (fun d : ParafermionicCoverVertex × ParafermionicCoverVertex => d.1.1.1) h
    have htx := congrArg (fun d : ParafermionicCoverVertex × ParafermionicCoverVertex => d.2.1.1) h
    change 1 = x at hsx
    change 0 = x + 1 at htx
    omega
  · have hsx := congrArg (fun d : ParafermionicCoverVertex × ParafermionicCoverVertex => d.1.1.1) h
    have htx := congrArg (fun d : ParafermionicCoverVertex × ParafermionicCoverVertex => d.2.1.1) h
    have hsy := congrArg (fun d : ParafermionicCoverVertex × ParafermionicCoverVertex => d.1.1.2) h
    have hty := congrArg (fun d : ParafermionicCoverVertex × ParafermionicCoverVertex => d.2.1.2) h
    change 1 = x + 1 at hsx
    change 0 = x + 1 at htx
    change 0 = y at hsy
    change 0 = y + 1 at hty
    omega
  · have hsx := congrArg (fun d : ParafermionicCoverVertex × ParafermionicCoverVertex => d.1.1.1) h
    have hsy := congrArg (fun d : ParafermionicCoverVertex × ParafermionicCoverVertex => d.1.1.2) h
    change 1 = x + 1 at hsx
    change 0 = y + 1 at hsy
    apply hnot
    apply Prod.ext <;> omega
  · have hsx := congrArg (fun d : ParafermionicCoverVertex × ParafermionicCoverVertex => d.1.1.1) h
    have htx := congrArg (fun d : ParafermionicCoverVertex × ParafermionicCoverVertex => d.2.1.1) h
    change 1 = x at hsx
    change 0 = x at htx
    omega

/-- Zero coefficients along the explicit five-face corridor force the face on
the east side of the negative anchor dart to be absent, hence the anchor's
oriented coefficient is nonnegative. This is a finite corridor statement; it
does not assert that the coefficient premise holds for a source cycle. -/
theorem parafermionicCoverBranchCorridor_anchor_coefficient_nonneg
    (n : ℕ) (hn : 4 ≤ n)
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hzero : ∀ u v : ParafermionicCoverBoxVertex n,
      parafermionicCoverRefinedCentralRectangle u.1 →
      parafermionicCoverRefinedCentralRectangle v.1 →
      parafermionicCoverFaceBoundaryCoefficient S u v = 0) :
    0 ≤ parafermionicCoverFaceBoundaryCoefficient S
      (branchCorridorVertex n hn (-3) 1 (by omega) (by omega) (by omega) (by omega))
      (branchCorridorVertex n hn (-3) 2 (by omega) (by omega) (by omega) (by omega)) := by
  let f0 := branchCorridorFace n hn (-3) 1 (by omega) (by omega) (by omega) (by omega)
  let f1 := branchCorridorFace n hn (-2) 1 (by omega) (by omega) (by omega) (by omega)
  let f2 := branchCorridorFace n hn (-1) 1 (by omega) (by omega) (by omega) (by omega)
  let f3 := branchCorridorFace n hn 0 1 (by omega) (by omega) (by omega) (by omega)
  let f4 := branchCorridorFace n hn 0 0 (by omega) (by omega) (by omega) (by omega)
  let a0 := branchCorridorVertex n hn (-2) 1 (by omega) (by omega) (by omega) (by omega)
  let b0 := branchCorridorVertex n hn (-2) 2 (by omega) (by omega) (by omega) (by omega)
  let a1 := branchCorridorVertex n hn (-1) 1 (by omega) (by omega) (by omega) (by omega)
  let b1 := branchCorridorVertex n hn (-1) 2 (by omega) (by omega) (by omega) (by omega)
  let a2 := branchCorridorVertex n hn 0 1 (by omega) (by omega) (by omega) (by omega)
  let b2 := branchCorridorVertex n hn 0 2 (by omega) (by omega) (by omega) (by omega)
  let a3 := branchCorridorVertex n hn 0 1 (by omega) (by omega) (by omega) (by omega)
  let b3 := branchCorridorVertex n hn 1 1 (by omega) (by omega) (by omega) (by omega)
  let a4 := branchCorridorVertex n hn 0 0 (by omega) (by omega) (by omega) (by omega)
  let b4 := branchCorridorVertex n hn 1 0 (by omega) (by omega) (by omega) (by omega)
  have h01 : f0 ∈ S ↔ f1 ∈ S := by
    apply branchCorridor_zero_coeff_face_iff S a0 b0 f0 f1
    · change (((-2,1),0),((-2,2),0)) ∈ parafermionicCoverFiniteFaceDarts ((-3,1),0)
      simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula]
    · change (((-2,2),0),((-2,1),0)) ∈ parafermionicCoverFiniteFaceDarts ((-2,1),0)
      simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula]
    · apply hzero
      · change parafermionicCoverRefinedCentralRectangle ((-2,1),0); norm_num [parafermionicCoverRefinedCentralRectangle]
      · change parafermionicCoverRefinedCentralRectangle ((-2,2),0); norm_num [parafermionicCoverRefinedCentralRectangle]
  have h12 : f1 ∈ S ↔ f2 ∈ S := by
    apply branchCorridor_zero_coeff_face_iff S a1 b1 f1 f2
    · change (((-1,1),0),((-1,2),0)) ∈ parafermionicCoverFiniteFaceDarts ((-2,1),0)
      simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula]
    · change (((-1,2),0),((-1,1),0)) ∈ parafermionicCoverFiniteFaceDarts ((-1,1),0)
      simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula]
    · apply hzero
      · change parafermionicCoverRefinedCentralRectangle ((-1,1),0); norm_num [parafermionicCoverRefinedCentralRectangle]
      · change parafermionicCoverRefinedCentralRectangle ((-1,2),0); norm_num [parafermionicCoverRefinedCentralRectangle]
  have h23 : f2 ∈ S ↔ f3 ∈ S := by
    apply branchCorridor_zero_coeff_face_iff S a2 b2 f2 f3
    · change (((0,1),0),((0,2),0)) ∈ parafermionicCoverFiniteFaceDarts ((-1,1),0)
      simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula]
    · change (((0,2),0),((0,1),0)) ∈ parafermionicCoverFiniteFaceDarts ((0,1),0)
      simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula]
    · apply hzero
      · change parafermionicCoverRefinedCentralRectangle ((0,1),0); norm_num [parafermionicCoverRefinedCentralRectangle]
      · change parafermionicCoverRefinedCentralRectangle ((0,2),0); norm_num [parafermionicCoverRefinedCentralRectangle]
  have h34 : f3 ∈ S ↔ f4 ∈ S := by
    apply branchCorridor_zero_coeff_face_iff S a3 b3 f3 f4
    · change (((0,1),0),((1,1),0)) ∈ parafermionicCoverFiniteFaceDarts ((0,1),0)
      simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula]
    · change (((1,1),0),((0,1),0)) ∈ parafermionicCoverFiniteFaceDarts ((0,0),0)
      simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula]
    · apply hzero
      · change parafermionicCoverRefinedCentralRectangle ((0,1),0); norm_num [parafermionicCoverRefinedCentralRectangle]
      · change parafermionicCoverRefinedCentralRectangle ((1,1),0); norm_num [parafermionicCoverRefinedCentralRectangle]
  have h45zero : parafermionicCoverFacePositiveDartCount S a4 b4 =
      if f4 ∈ S then 1 else 0 := by
    apply branchCorridor_positiveCount_eq_ite
    change (((0,0),0),((1,0),0)) ∈ parafermionicCoverFiniteFaceDarts ((0,0),0)
    simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceRightLift_formula,
      parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula]
  have h45neg : parafermionicCoverFacePositiveDartCount S b4 a4 = 0 := by
    unfold parafermionicCoverFacePositiveDartCount
    rw [Finset.card_eq_zero]
    ext i
    simp only [Finset.mem_filter, Finset.notMem_empty]
    constructor
    · rintro ⟨_, hd⟩
      exact (branchCorridor_no_missing_reverse_dart i hd).elim
    · intro hi
      contradiction
  have hf4zero : f4 ∉ S := by
    by_contra hf
    have hcoef := hzero a4 b4 (by
      change parafermionicCoverRefinedCentralRectangle ((0,0),0)
      norm_num [parafermionicCoverRefinedCentralRectangle]) (by
      change parafermionicCoverRefinedCentralRectangle ((1,0),0)
      norm_num [parafermionicCoverRefinedCentralRectangle])
    unfold parafermionicCoverFaceBoundaryCoefficient at hcoef
    rw [h45zero, h45neg] at hcoef
    simp [hf] at hcoef
  have hf3zero : f3 ∉ S := by
    intro hf
    exact hf4zero ((h34.mp hf))
  have hf0zero : f0 ∉ S := by
    intro hf0
    exact hf3zero (h23.mp (h12.mp (h01.mp hf0)))
  have hrev : parafermionicCoverFacePositiveDartCount S
      (branchCorridorVertex n hn (-3) 2 (by omega) (by omega) (by omega) (by omega))
      (branchCorridorVertex n hn (-3) 1 (by omega) (by omega) (by omega) (by omega)) = 0 := by
    unfold parafermionicCoverFacePositiveDartCount
    rw [Finset.card_eq_zero]
    ext i
    simp only [Finset.mem_filter, Finset.notMem_empty]
    constructor
    · rintro ⟨hiS, hd⟩
      have hface := parafermionicCoverFiniteFaceDart_unique n i.2 f0.2 hd (by
      change (((-3,2),0),((-3,1),0)) ∈ parafermionicCoverFiniteFaceDarts ((-3,1),0)
      simp [parafermionicCoverFiniteFaceDarts, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula])
      have heq : i = f0 := Subtype.ext hface
      exact hf0zero (heq ▸ hiS)
    · intro hi
      contradiction
  unfold parafermionicCoverFaceBoundaryCoefficient
  rw [hrev]
  exact Int.natCast_nonneg _

end PottsContinuity.FKC.Medial
