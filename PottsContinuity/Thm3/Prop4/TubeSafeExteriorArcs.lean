module

public import PottsContinuity.Thm3.Prop4.TubeHalfPlaneEdges

/-!
# Safe affine half-planes meet the correct physical exterior arc

The supporting segment remains inside the source box. At a genuine exterior
face, a safe lower or upper affine height selects the complementary arc cut
at the actual source endpoints, rather than an arbitrary exterior target.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Supporting-line heights over the physical horizontal span remain inside
the box's vertical span. -/
theorem tube_supporting_height_bounds (n : ℕ) (u v : PD.FK.LatticeVertex)
    (huBox : u ∈ box n) (hvBox : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n) (t b x : ℝ)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (hx : -(n : ℝ) ≤ x ∧ x ≤ n) :
    -(n : ℝ) ≤ t*x+b ∧ t*x+b ≤ n := by
  have hUy : -(n : ℤ) ≤ u.2 ∧ u.2 ≤ n := Finset.mem_Icc.mp (Finset.mem_product.mp huBox).2
  have hVy : -(n : ℤ) ≤ v.2 ∧ v.2 ≤ n := Finset.mem_Icc.mp (Finset.mem_product.mp hvBox).2
  have hUyR : -(n : ℝ) ≤ (u.2 : ℝ) ∧ (u.2 : ℝ) ≤ n := by exact_mod_cast hUy
  have hVyR : -(n : ℝ) ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) ≤ n := by exact_mod_cast hVy
  rw [huX] at hu
  rw [hvX] at hv
  push_cast at hu hv
  by_cases ht : 0 ≤ t
  · have hmul := mul_le_mul_of_nonneg_left hx.1 ht
    have hmul' := mul_le_mul_of_nonneg_left hx.2 ht
    constructor <;> linarith only [hmul,hmul',hu,hv,hUyR.1,hVyR.2]
  · have hmul := mul_le_mul_of_nonpos_left hx.1 (le_of_lt (lt_of_not_ge ht))
    have hmul' := mul_le_mul_of_nonpos_left hx.2 (le_of_lt (lt_of_not_ge ht))
    constructor <;> linarith only [hmul,hmul',hu,hv,hUyR.2,hVyR.1]

open PD.FK PD.FK.Medial

private theorem actual_exterior_face_sides (n : ℕ)
    (d : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (s : LatticeVertex) (hs : s = d.crossingBond.source ∨ s = d.crossingBond.target)
    (hb : s ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :
    (s.2 = -(n : ℤ)-1 ∧ -(n : ℤ) ≤ s.1 ∧ s.1 < n) ∨
    (s.2 = (n : ℤ) ∧ -(n : ℤ) ≤ s.1 ∧ s.1 < n) ∨
    (s.1 = -(n : ℤ)-1 ∧ -(n : ℤ) ≤ s.2 ∧ s.2 < n) ∨
    (s.1 = (n : ℤ) ∧ -(n : ℤ) ≤ s.2 ∧ s.2 < n) := by
  have hbm := Finset.mem_filter.mp hb
  have hnot : ¬ (-(n : ℤ) ≤ s.1 ∧ s.1 < n ∧ -(n : ℤ) ≤ s.2 ∧ s.2 < n) := by
    intro h
    apply hbm.2
    apply Finset.mem_filter.mpr
    refine ⟨hbm.1,?_⟩
    dsimp
    omega
  let c := rectanglePrimalEdgeBondEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) d.primalEdge
  have hfaces : s = c.val.faceBase false ∨ s = c.val.faceBase true := by
    rcases hs with hs | hs
    · left
      exact hs.trans (rectangleDualEdgeSource_faceBase _ _ _ d)
    · right
      exact hs.trans (rectangleDualEdgeTarget_faceBase _ _ _ d)
  have hc0 := (mem_latticeRectangle _ _ _ _).mp c.property.1
  have hc1 := (mem_latticeRectangle _ _ _ _).mp c.property.2
  rcases c with ⟨⟨⟨x,y⟩,axis⟩,hc⟩
  cases axis <;> rcases hfaces with rfl | rfl <;>
    simp only [LatticeBond.faceBase,LatticeBond.source,LatticeBond.target,
      Nat.cast_mul,Nat.cast_ofNat] at hc0 hc1 hnot ⊢ <;> omega

/-- A genuine sampled exterior face in the lower safe half-plane belongs to
the lower complementary arc at the actual source marks. -/
theorem tube_safe_lower_exterior_arc (n : ℕ) (r : ℝ) (hr : 1 ≤ r)
    (u v : LatticeVertex) (huBox : u ∈ box n) (hvBox : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (d : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (s : LatticeVertex) (hs : s = d.crossingBond.source ∨ s = d.crossingBond.target)
    (hb : s ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hheight : (s.2 : ℝ)-t*s.1 ≤ b-2*r) :
    s ∈ PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v := by
  have hfaces := actual_exterior_face_sides n d s hs hb
  have huOrig := hu
  have hvOrig := hv
  have ht' := abs_le.mp ht
  rw [huX] at hu
  rw [hvX] at hv
  push_cast at hu hv
  rcases hfaces with hbottom | htop | hleft | hright
  · apply Or.inl
    dsimp
    exact ⟨hbottom.1,hbottom.2.1,by omega⟩
  · have hxZ : -(n : ℤ) ≤ s.1 ∧ s.1 ≤ n := ⟨htop.2.1,htop.2.2.le⟩
    have hx : -(n : ℝ) ≤ (s.1 : ℝ) ∧ (s.1 : ℝ) ≤ n := by exact_mod_cast hxZ
    have hline := (tube_supporting_height_bounds n u v huBox hvBox huX hvX t b s.1
      huOrig hvOrig hx).2
    rw [htop.1] at hheight
    push_cast at hheight
    linarith only [hheight,hline,hr]
  · apply Or.inr ∘ Or.inl
    have hy : s.2 < u.2 := by
      rw [hleft.1] at hheight
      push_cast at hheight
      exact_mod_cast (show (s.2 : ℝ) < (u.2 : ℝ) by linarith only [hheight,hu,ht'.1,hr])
    dsimp
    exact ⟨hleft.1,hleft.2.1,by omega,hy⟩
  · apply Or.inr ∘ Or.inr
    have hy : s.2 < v.2 := by
      rw [hright.1] at hheight
      push_cast at hheight
      exact_mod_cast (show (s.2 : ℝ) < (v.2 : ℝ) by linarith only [hheight,hv,hr])
    dsimp
    exact ⟨by omega,hright.2.1,by omega,hy⟩

/-- A genuine sampled exterior face in the upper safe half-plane belongs to
the upper complementary arc at the actual source marks. -/
theorem tube_safe_upper_exterior_arc (n : ℕ) (r : ℝ) (hr : 1 ≤ r)
    (u v : LatticeVertex) (huBox : u ∈ box n) (hvBox : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (d : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (s : LatticeVertex) (hs : s = d.crossingBond.source ∨ s = d.crossingBond.target)
    (hb : s ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hheight : b+2*r ≤ (s.2 : ℝ)-t*s.1) :
    s ∈ PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v := by
  have hfaces := actual_exterior_face_sides n d s hs hb
  have huOrig := hu
  have hvOrig := hv
  have ht' := abs_le.mp ht
  rw [huX] at hu
  rw [hvX] at hv
  push_cast at hu hv
  rcases hfaces with hbottom | htop | hleft | hright
  · have hxZ : -(n : ℤ) ≤ s.1 ∧ s.1 ≤ n := ⟨hbottom.2.1,hbottom.2.2.le⟩
    have hx : -(n : ℝ) ≤ (s.1 : ℝ) ∧ (s.1 : ℝ) ≤ n := by exact_mod_cast hxZ
    have hline := (tube_supporting_height_bounds n u v huBox hvBox huX hvX t b s.1
      huOrig hvOrig hx).1
    rw [hbottom.1] at hheight
    push_cast at hheight
    linarith only [hheight,hline,hr]
  · apply Or.inl
    dsimp
    exact ⟨by omega,htop.2.1,by omega⟩
  · apply Or.inr ∘ Or.inl
    have hy : u.2 ≤ s.2 := by
      rw [hleft.1] at hheight
      push_cast at hheight
      exact_mod_cast (show (u.2 : ℝ) ≤ (s.2 : ℝ) by linarith only [hheight,hu,ht'.2,hr])
    dsimp
    exact ⟨hleft.1,hleft.2.1,hy,by omega⟩
  · apply Or.inr ∘ Or.inr
    have hy : v.2 ≤ s.2 := by
      rw [hright.1] at hheight
      push_cast at hheight
      exact_mod_cast (show (v.2 : ℝ) ≤ (s.2 : ℝ) by linarith only [hheight,hv,hr])
    dsimp
    exact ⟨by omega,hright.2.1,hy,by omega⟩

end PottsContinuity.Thm3.Prop4
