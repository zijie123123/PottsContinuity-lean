module

public import PottsContinuity.Thm4Plane.GeneralEScreen

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK

/-- The part of the translated radius-`m` target square retained by the
finite slit box at the cofinal scale `16*m`. -/
def screenTargetCap (m : ℕ) : Set (SlitBoxVertex (16 * m)) :=
  {v | -(m : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (m : ℤ) ∧
    -(16 * (m : ℤ)) ≤ v.val.2 ∧ v.val.2 ≤ -(15 * (m : ℤ))}

def screenTargetRadius (m : ℕ) (v : SlitBoxVertex (16 * m)) : ℤ :=
  max |v.val.1| |v.val.2 + (16 * (m : ℤ))|

private theorem screenTargetCap_y_lower (m : ℕ)
    (v : SlitBoxVertex (16 * m)) :
    -(16 * (m : ℤ)) ≤ v.val.2 := by
  have hv := v.property
  change v.val ∈ FKC.latticeRectangle
    (-(16 * (m : ℤ)), -(16 * (m : ℤ))) (2 * (16 * m)) (2 * (16 * m)) at hv
  exact ((mem_latticeRectangle _ _ _ _).mp hv).2.1

private theorem max_le_add_one {a b c d : ℤ}
    (ha : a ≤ c + 1) (hb : b ≤ d + 1) :
    max a b ≤ max c d + 1 := by
  apply max_le
  · have hc := le_max_left c d
    omega
  · have hd := le_max_right c d
    omega

private theorem int_abs_adj_step {a b : ℤ}
    (h : a + 1 = b ∨ b + 1 = a) :
    |a| ≤ |b| + 1 ∧ |b| ≤ |a| + 1 := by
  rcases h with h | h
  · rw [← h]
    by_cases ha : 0 ≤ a
    · rw [abs_of_nonneg ha]
      by_cases hb : 0 ≤ a + 1
      · rw [abs_of_nonneg hb]
        omega
      · have hb' : a + 1 ≤ 0 := le_of_not_ge hb
        rw [abs_of_nonpos hb']
        omega
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [abs_of_nonpos ha']
      by_cases hb : 0 ≤ a + 1
      · rw [abs_of_nonneg hb]
        omega
      · have hb' : a + 1 ≤ 0 := le_of_not_ge hb
        rw [abs_of_nonpos hb']
        omega
  · rw [← h]
    by_cases hb : 0 ≤ b
    · rw [abs_of_nonneg hb]
      by_cases ha : 0 ≤ b + 1
      · rw [abs_of_nonneg ha]
        omega
      · have ha' : b + 1 ≤ 0 := le_of_not_ge ha
        rw [abs_of_nonpos ha']
        omega
    · have hb' : b ≤ 0 := le_of_not_ge hb
      rw [abs_of_nonpos hb']
      by_cases ha : 0 ≤ b + 1
      · rw [abs_of_nonneg ha]
        omega
      · have ha' : b + 1 ≤ 0 := le_of_not_ge ha
        rw [abs_of_nonpos ha']
        omega

private theorem screenTargetRadius_adj_bounds (m : ℕ)
    {x y : LatticeVertex}
    (hxy : PottsContinuity.FKC.squareLattice.Adj x y) :
    max |x.1| |x.2 + (16 * (m : ℤ))| ≤
        max |y.1| |y.2 + (16 * (m : ℤ))| + 1 ∧
      max |y.1| |y.2 + (16 * (m : ℤ))| ≤
        max |x.1| |x.2 + (16 * (m : ℤ))| + 1 := by
  rcases (PottsContinuity.FKC.squareLattice_adj_iff x y).mp hxy with
    ⟨horiz | horiz, hy⟩ | ⟨hx, vert | vert⟩
  · have habs := int_abs_adj_step (Or.inl horiz)
    have hshift : |x.2 + (16 * (m : ℤ))| = |y.2 + (16 * (m : ℤ))| := by
      rw [hy]
    constructor
    · apply max_le_add_one
      · exact habs.1
      · rw [hshift]
        omega
    · apply max_le_add_one
      · exact habs.2
      · rw [hshift]
        omega
  · have habs := int_abs_adj_step (Or.inr horiz)
    have hshift : |x.2 + (16 * (m : ℤ))| = |y.2 + (16 * (m : ℤ))| := by
      rw [hy]
    constructor
    · apply max_le_add_one
      · exact habs.1
      · rw [hshift]
        omega
    · apply max_le_add_one
      · exact habs.2
      · rw [hshift]
        omega
  · have habs := int_abs_adj_step
      (Or.inl (by omega : x.2 + (16 * (m : ℤ)) + 1 = y.2 + (16 * (m : ℤ))))
    have hfirst : |x.1| = |y.1| := by rw [hx]
    constructor
    · apply max_le_add_one
      · rw [hfirst]
        omega
      · exact habs.1
    · apply max_le_add_one
      · rw [hfirst]
        omega
      · exact habs.2
  · have habs := int_abs_adj_step
      (Or.inr (by omega : y.2 + (16 * (m : ℤ)) + 1 = x.2 + (16 * (m : ℤ))))
    have hfirst : |x.1| = |y.1| := by rw [hx]
    constructor
    · apply max_le_add_one
      · rw [hfirst]
        omega
      · exact habs.1
    · apply max_le_add_one
      · rw [hfirst]
        omega
      · exact habs.2
private theorem walk_prefix_to_radius
    {V : Type*} {G : SimpleGraph V} {src dst : V}
    (p : G.Walk src dst) (radius : V → ℤ) (r : ℤ)
    (hstep : ∀ {x y}, G.Adj x y →
      radius x ≤ radius y + 1 ∧ radius y ≤ radius x + 1)
    (a b : V) (ha : a = src) (hb : b = dst)
    (hstart : radius a ≤ r) (hend : r ≤ radius b) :
    ∃ z, ∃ preWalk : G.Walk a z, radius z = r ∧
        ∀ x ∈ preWalk.support, radius x ≤ r := by
  induction p generalizing a b with
  | nil =>
      have hba : b = a := hb.trans ha.symm
      rw [hba] at hend
      have heq : radius a = r := le_antisymm hstart hend
      refine ⟨a, .nil, heq, ?_⟩
      intro x hx
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact hstart
  | @cons u w v hadj tail ih =>
      subst a
      subst b
      by_cases hu : radius u = r
      · refine ⟨u, .nil, hu, ?_⟩
        intro x hx
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
        subst x
        exact hstart
      · have hlt : radius u < r := by omega
        have hw : radius w ≤ r := by
          have h := (hstep hadj).2
          omega
        obtain ⟨z, pre, hz, hbound⟩ :=
          ih w v rfl rfl hw hend
        refine ⟨z, .cons hadj pre, hz, ?_⟩
        intro x hx
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hstart
        · exact hbound x hx

private theorem screenTargetCap_radius_is_boundary (m : ℕ)
    (v : SlitBoxVertex (16 * m))
    (hvRadius : screenTargetRadius m v = (m : ℤ)) :
    v ∈ screenTargetCap m ∧
      (|v.val.1| = (m : ℤ) ∨ v.val.2 = -(15 * (m : ℤ))) := by
  let a : ℤ := |v.val.1|
  let b : ℤ := |v.val.2 + (16 * (m : ℤ))|
  have hmax : max a b = (m : ℤ) := by simpa [screenTargetRadius, a, b] using hvRadius
  have ha : a ≤ (m : ℤ) := by
    have h := le_max_left a b
    rw [hmax] at h
    exact h
  have hb : b ≤ (m : ℤ) := by
    have h := le_max_right a b
    rw [hmax] at h
    exact h
  have hx := abs_le.mp (show |v.val.1| ≤ (m : ℤ) by simpa [a] using ha)
  have hlow := screenTargetCap_y_lower m v
  have hyAbs : |v.val.2 + (16 * (m : ℤ))| ≤ (m : ℤ) := by simpa [b] using hb
  have hy := abs_le.mp hyAbs
  have hcap : v ∈ screenTargetCap m := by
    dsimp [screenTargetCap]
    exact ⟨hx.1, hx.2, hlow, by omega⟩
  rcases le_total a b with hab | hba
  · have hbEq : b = (m : ℤ) := by
      have h := hmax
      rw [max_eq_right hab] at h
      exact h
    have hshift : v.val.2 + (16 * (m : ℤ)) = (m : ℤ) := by
      dsimp [b] at hbEq
      rw [abs_of_nonneg (show 0 ≤ v.val.2 + (16 * (m : ℤ)) by omega)] at hbEq
      exact hbEq
    exact ⟨hcap, Or.inr (by omega)⟩
  · have haEq : a = (m : ℤ) := by
      have h := hmax
      rw [max_eq_left hba] at h
      exact h
    exact ⟨hcap, Or.inl (by simpa [a] using haEq)⟩

/-- Every source screen witness has a path witness whose whole support stays
inside the part of the translated square present in the finite slit box. -/
theorem generalEScreenEvent_has_path_in_screenTargetCap
    (m : ℕ) (A : Configuration (slitBoxGraph (16 * m)))
    (hE : A ∈ generalEScreenEvent (16 * m)) :
    ∃ v : SlitBoxVertex (16 * m), v ∈ screenTargetCap m ∧
      (|v.val.1| = (m : ℤ) ∨ v.val.2 = -(15 * (m : ℤ))) ∧
      ∃ p : (openGraph (slitBoxGraph (16 * m)) A).Walk
        (slitBoxBottomCenterVertex (16 * m)) v,
        ∀ z ∈ p.support, z ∈ screenTargetCap m := by
  rcases hE with ⟨v, hvRadius, hconn⟩
  obtain ⟨p⟩ := (actualConnected_iff_walk (slitBoxGraph (16 * m)) A
    (slitBoxBottomCenterVertex (16 * m)) v).mp hconn
  let radius : SlitBoxVertex (16 * m) → ℤ := screenTargetRadius m
  have hstep : ∀ {x y}, (openGraph (slitBoxGraph (16 * m)) A).Adj x y →
      radius x ≤ radius y + 1 ∧ radius y ≤ radius x + 1 := by
    intro x y hxy
    have hgraph := openGraph_le (slitBoxGraph (16 * m)) A hxy
    have hlat := (slitBoxGraph_adj_iff (16 * m) x y).mp hgraph |>.1
    exact screenTargetRadius_adj_bounds m hlat
  have hstart : radius (slitBoxBottomCenterVertex (16 * m)) ≤ (m : ℤ) := by
    simp [radius, screenTargetRadius, slitBoxBottomCenterVertex_val]
  have hend : (m : ℤ) ≤ radius v := by
    have hmRadius : generalEScreenRadius (16 * m) = (m : ℤ) := by
      dsimp [generalEScreenRadius]
      norm_cast
      omega
    rw [hmRadius] at hvRadius
    change (m : ℤ) ≤ screenTargetRadius m v
    rw [screenTargetRadius]
    exact le_of_eq hvRadius.symm
  obtain ⟨z, preWalk, hz, hbound⟩ :=
    walk_prefix_to_radius p radius (m : ℤ) hstep
      (slitBoxBottomCenterVertex (16 * m)) v rfl rfl hstart hend
  have hzData := screenTargetCap_radius_is_boundary m z hz
  refine ⟨z, hzData.1, hzData.2, preWalk, ?_⟩
  intro x hx
  dsimp [screenTargetCap, radius, screenTargetRadius]
  have hrad := hbound x hx
  have hxAbs : |x.val.1| ≤ (m : ℤ) := by
    exact (le_trans (le_max_left _ _) hrad)
  have hyAbs : |x.val.2 + (16 * (m : ℤ))| ≤ (m : ℤ) := by
    exact (le_trans (le_max_right _ _) hrad)
  have hx' := abs_le.mp hxAbs
  have hy' := abs_le.mp hyAbs
  have hlow := screenTargetCap_y_lower m x
  exact ⟨hx'.1, hx'.2, hlow, by omega⟩

end PottsContinuity.Thm4Plane
