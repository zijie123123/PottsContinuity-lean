-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitScreenDualEdgeClassification.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain
public import PottsContinuity.FKC.Medial.WholePlaneDualGraph

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

/-! Exact face-base coordinates and crossed-primal-bond support for the three
rectangles used by the DST17 slit screens at `n = 16*m`. -/

def slitScreenRightFaceBases (m : ℕ) : Finset LatticeVertex :=
  Finset.Icc (m : ℤ) (5 * (m : ℤ) - 1) ×ˢ
    Finset.Icc (-(16 * (m : ℤ)) - 1) (16 * (m : ℤ))

def slitScreenLeftFaceBases (m : ℕ) : Finset LatticeVertex :=
  Finset.Icc (-(5 * (m : ℤ))) (-(m : ℤ) - 1) ×ˢ
    Finset.Icc (-(16 * (m : ℤ)) - 1) (16 * (m : ℤ))

def slitScreenMiddleFaceBases (m : ℕ) : Finset LatticeVertex :=
  Finset.Icc (-(5 * (m : ℤ))) (5 * (m : ℤ) - 1) ×ˢ
    Finset.Icc (-(12 * (m : ℤ))) (-(2 * (m : ℤ)) - 1)

/-- Literal membership of the primal bond crossed by a dual bond in the slit
graph edge carrier. -/
def slitScreenPrimalBondInSlit (n : ℕ) (b : LatticeBond) : Prop :=
  ∃ u v : SlitBoxVertex n,
    u.val = b.source ∧ v.val = b.target ∧
      s(u, v) ∈ (slitBoxGraph n).edgeSet

private theorem slitScreen_memBox_iff (n : ℕ) (z : LatticeVertex) :
    z ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) ↔
      -(n : ℤ) ≤ z.1 ∧ z.1 ≤ n ∧ -(n : ℤ) ≤ z.2 ∧ z.2 ≤ n := by
  rw [mem_latticeRectangle]
  omega

private theorem slitScreen_dualCrossedBond_inSlit_iff
    (n : ℕ) (b : LatticeBond) :
    slitScreenPrimalBondInSlit n b ↔
      b.source ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) ∧
      b.target ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) ∧
      ¬ (b.source.1 = 0 ∧ b.target.1 = 0 ∧
        0 ≤ b.source.2 ∧ b.source.2 ≤ n ∧
        0 ≤ b.target.2 ∧ b.target.2 ≤ n) := by
  constructor
  · rintro ⟨u, v, hu, hv, he⟩
    have hboxu := u.property
    have hboxv := v.property
    have hadj : (slitBoxGraph n).Adj u v :=
      (slitBoxGraph n).mem_edgeSet.mp he
    have hnot := (slitBoxGraph_adj_iff n u v).mp hadj |>.2
    refine ⟨?_, ?_, ?_⟩
    · simpa [hu] using hboxu
    · simpa [hv] using hboxv
    · intro hbad
      apply hnot
      rcases hbad with ⟨hux, hvx, huy0, huyn, hvy0, hvyn⟩
      constructor
      · simpa [hu] using (show b.source.1 = 0 ∧
          0 ≤ b.source.2 ∧ b.source.2 ≤ n from ⟨hux, huy0, huyn⟩)
      · simpa [hv] using (show b.target.1 = 0 ∧
          0 ≤ b.target.2 ∧ b.target.2 ≤ n from ⟨hvx, hvy0, hvyn⟩)
  · rintro ⟨hs, ht, hnot⟩
    let u : SlitBoxVertex n := ⟨b.source, hs⟩
    let v : SlitBoxVertex n := ⟨b.target, ht⟩
    refine ⟨u, v, rfl, rfl, ?_⟩
    apply (slitBoxGraph n).mem_edgeSet.mpr
    apply (slitBoxGraph_adj_iff n u v).mpr
    refine ⟨LatticeBond.adjacent b, ?_⟩
    intro hboth
    apply hnot
    rcases hboth with ⟨hu, hv⟩
    rcases hu with ⟨hux, huy0, huyn⟩
    rcases hv with ⟨hvx, hvy0, hvyn⟩
    exact ⟨by simpa using hux, by simpa using hvx,
      by simpa using huy0, by simpa using huyn,
      by simpa using hvy0, by simpa using hvyn⟩

private theorem slitScreen_tall_box_iff_coords
    (m : ℕ) (x y : ℤ) (ax : LatticeAxis)
    (hx0 : -(↑(16 * m)) ≤ x) (hx1 : x < ↑(16 * m))
    (hy0 : -(↑(16 * m)) - 1 ≤ y) (hy1 : y ≤ ↑(16 * m))
    (hvy : ax = .vertical → y < ↑(16 * m)) :
    ((primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).source ∈
        latticeRectangle (-(↑(16 * m)), -(↑(16 * m)))
          (2 * (16 * m)) (2 * (16 * m)) ∧
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).target ∈
        latticeRectangle (-(↑(16 * m)), -(↑(16 * m)))
          (2 * (16 * m)) (2 * (16 * m))) ↔
      ¬ (ax = .horizontal ∧
        (y = -(↑(16 * m)) - 1 ∨ y = ↑(16 * m))) := by
  cases ax with
  | horizontal =>
      have hwidth : (↑(2 * (16 * m)) : ℤ) = 2 * ↑(16 * m) := by norm_cast
      change (((x + 1, y) ∈ latticeRectangle (-(↑(16 * m)), -(↑(16 * m)))
          (2 * (16 * m)) (2 * (16 * m))) ∧
        ((x + 1, y + 1) ∈ latticeRectangle (-(↑(16 * m)), -(↑(16 * m)))
          (2 * (16 * m)) (2 * (16 * m)))) ↔
        ¬ (LatticeAxis.horizontal = .horizontal ∧
          (y = -(↑(16 * m)) - 1 ∨ y = ↑(16 * m)))
      rw [slitScreen_memBox_iff, slitScreen_memBox_iff]
      simp only at *
      constructor
      · intro h hbad
        rcases hbad with hlow | hupp; omega
      · intro hnot
        have hylo : y ≠ -(↑(16 * m)) - 1 := by
          intro heq
          apply hnot
          exact ⟨trivial, Or.inl heq⟩
        have hyhi : y ≠ ↑(16 * m) := by
          intro heq
          apply hnot
          exact ⟨trivial, Or.inr heq⟩
        constructor <;> constructor <;> omega
  | vertical =>
      have hwidth : (↑(2 * (16 * m)) : ℤ) = 2 * ↑(16 * m) := by norm_cast
      have hylt := hvy rfl
      change (((x, y + 1) ∈ latticeRectangle (-(↑(16 * m)), -(↑(16 * m)))
          (2 * (16 * m)) (2 * (16 * m))) ∧
        ((x + 1, y + 1) ∈ latticeRectangle (-(↑(16 * m)), -(↑(16 * m)))
          (2 * (16 * m)) (2 * (16 * m)))) ↔
        ¬ (LatticeAxis.vertical = .horizontal ∧
          (y = -(↑(16 * m)) - 1 ∨ y = ↑(16 * m)))
      rw [slitScreen_memBox_iff, slitScreen_memBox_iff]
      constructor
      · intro _
        simp
      · intro _
        constructor <;> constructor <;> omega

private theorem slitScreen_tall_notArc_coords
    (m : ℕ) (x y : ℤ) (ax : LatticeAxis)
    (_hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    ¬ ((primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).source.1 = 0 ∧
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).target.1 = 0 ∧
      0 ≤ (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).source.2 ∧
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).source.2 ≤ 16 * m ∧
      0 ≤ (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).target.2 ∧
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).target.2 ≤ 16 * m) := by
  cases ax <;> simp [primalBondOfDual, LatticeBond.source, LatticeBond.target] <;>
    omega

private theorem slitScreen_middle_box_coords
    (m : ℕ) (x y : ℤ) (ax : LatticeAxis)
    (hx0 : -5 * (m : ℤ) ≤ x) (hx1 : x ≤ 5 * (m : ℤ) - 1)
    (hy0 : -(12 * (m : ℤ)) ≤ y)
    (hy1 : y ≤ -(2 * (m : ℤ)) - 1) :
    (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).source ∈
        latticeRectangle (-(↑(16 * m)), -(↑(16 * m)))
          (2 * (16 * m)) (2 * (16 * m)) ∧
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).target ∈
        latticeRectangle (-(↑(16 * m)), -(↑(16 * m)))
          (2 * (16 * m)) (2 * (16 * m)) := by
  cases ax <;>
    simp [primalBondOfDual, LatticeBond.source, LatticeBond.target,
      mem_latticeRectangle] <;> omega

private theorem slitScreen_middle_notArc_coords
    (m : ℕ) (x y : ℤ) (ax : LatticeAxis)
    (hy0 : -(12 * (m : ℤ)) ≤ y)
    (hy1 : y ≤ -(2 * (m : ℤ)) - 1) :
    ¬ ((primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).source.1 = 0 ∧
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).target.1 = 0 ∧
      0 ≤ (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).source.2 ∧
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).source.2 ≤ 16 * m ∧
      0 ≤ (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).target.2 ∧
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)).target.2 ≤ 16 * m) := by
  cases ax <;> simp [primalBondOfDual, LatticeBond.source, LatticeBond.target] <;>
    omega

/-- Every middle-screen dual bond crosses an actual slit-graph edge. The
hypotheses are precisely the endpoint-in-face-rectangle coordinate bounds. -/
private theorem slitScreenMiddle_primalBondInSlit
    (m : ℕ) (_hm : 1 ≤ m) (x y : ℤ) (ax : LatticeAxis)
    (hx0 : -5 * (m : ℤ) ≤ x) (hx1 : x ≤ 5 * (m : ℤ) - 1)
    (hy0 : -(12 * (m : ℤ)) ≤ y)
    (hy1 : y ≤ -(2 * (m : ℤ)) - 1)
    (_hh : ax = .horizontal → x < 5 * (m : ℤ) - 1)
    (_hv : ax = .vertical → y < -(2 * (m : ℤ)) - 1) :
    slitScreenPrimalBondInSlit (16 * m)
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)) := by
  apply (slitScreen_dualCrossedBond_inSlit_iff (16 * m) _).2
  have hbox := slitScreen_middle_box_coords m x y ax hx0 hx1 hy0 hy1
  have hnot := slitScreen_middle_notArc_coords m x y ax hy0 hy1
  exact ⟨hbox.1, hbox.2, hnot⟩

/-- In the right tall screen, membership of the crossed bond in the actual
slit graph fails exactly for the two horizontal boundary-tangential dual rows. -/
private theorem slitScreenRight_primalBondInSlit_iff
    (m : ℕ) (_hm : 1 ≤ m) (x y : ℤ) (ax : LatticeAxis)
    (hx0 : (m : ℤ) ≤ x) (hx1 : x ≤ 5 * (m : ℤ) - 1)
    (hy0 : -(16 * (m : ℤ)) - 1 ≤ y) (hy1 : y ≤ 16 * (m : ℤ))
    (_hh : ax = .horizontal → x < 5 * (m : ℤ) - 1)
    (hv : ax = .vertical → y < 16 * (m : ℤ)) :
    slitScreenPrimalBondInSlit (16 * m)
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)) ↔
      ¬ (ax = .horizontal ∧
        (y = -(16 * (m : ℤ)) - 1 ∨ y = 16 * (m : ℤ))) := by
  rw [slitScreen_dualCrossedBond_inSlit_iff]
  have hbox := slitScreen_tall_box_iff_coords m x y ax
    (by omega) (by omega) (by omega) (by omega) hv
  have hnot := slitScreen_tall_notArc_coords m x y ax
    (by omega) (by omega)
  constructor
  · rintro ⟨hs, ht, _⟩
    exact hbox.mp ⟨hs, ht⟩
  · intro h
    exact ⟨(hbox.mpr h).1, (hbox.mpr h).2, hnot⟩

/-- The same exact boundary-row classification in the left tall screen. -/
private theorem slitScreenLeft_primalBondInSlit_iff
    (m : ℕ) (_hm : 1 ≤ m) (x y : ℤ) (ax : LatticeAxis)
    (hx0 : -5 * (m : ℤ) ≤ x) (hx1 : x ≤ -(m : ℤ) - 1)
    (hy0 : -(16 * (m : ℤ)) - 1 ≤ y) (hy1 : y ≤ 16 * (m : ℤ))
    (_hh : ax = .horizontal → x < -(m : ℤ) - 1)
    (hv : ax = .vertical → y < 16 * (m : ℤ)) :
    slitScreenPrimalBondInSlit (16 * m)
      (primalBondOfDual (⟨(x,y), ax⟩ : LatticeBond)) ↔
      ¬ (ax = .horizontal ∧
        (y = -(16 * (m : ℤ)) - 1 ∨ y = 16 * (m : ℤ))) := by
  rw [slitScreen_dualCrossedBond_inSlit_iff]
  have hbox := slitScreen_tall_box_iff_coords m x y ax
    (by omega) (by omega) (by omega) (by omega) hv
  have hnot := slitScreen_tall_notArc_coords m x y ax
    (by omega) (by omega)
  constructor
  · rintro ⟨hs, ht, _⟩
    exact hbox.mp ⟨hs, ht⟩
  · intro h
    exact ⟨(hbox.mpr h).1, (hbox.mpr h).2, hnot⟩

/-- The right-screen classification stated directly for bonds whose two dual
endpoints lie in the literal right face-base rectangle. -/
theorem slitScreenRightFaceBond_primalBondInSlit_iff
    (m : ℕ) (hm : 1 ≤ m) (d : LatticeBond)
    (hs : d.source ∈ slitScreenRightFaceBases m)
    (ht : d.target ∈ slitScreenRightFaceBases m) :
    slitScreenPrimalBondInSlit (16 * m) (primalBondOfDual d) ↔
      ¬ (d.axis = .horizontal ∧
        (d.base.2 = -(16 * (m : ℤ)) - 1 ∨ d.base.2 = 16 * (m : ℤ))) := by
  rcases d with ⟨⟨x, y⟩, ax⟩
  cases ax with
  | horizontal =>
      change (x, y) ∈ slitScreenRightFaceBases m at hs
      change (x + 1, y) ∈ slitScreenRightFaceBases m at ht
      rcases Finset.mem_product.mp hs with ⟨hxs, hys⟩
      rcases Finset.mem_Icc.mp hxs with ⟨hx0, hx1⟩
      rcases Finset.mem_Icc.mp hys with ⟨hy0, hy1⟩
      rcases Finset.mem_product.mp ht with ⟨hxt, _⟩
      rcases Finset.mem_Icc.mp hxt with ⟨_, hx2⟩
      exact slitScreenRight_primalBondInSlit_iff m hm x y .horizontal
        hx0 hx1 hy0 hy1 (by intro; omega) (by intro h; cases h)
  | vertical =>
      change (x, y) ∈ slitScreenRightFaceBases m at hs
      change (x, y + 1) ∈ slitScreenRightFaceBases m at ht
      rcases Finset.mem_product.mp hs with ⟨hxs, hys⟩
      rcases Finset.mem_Icc.mp hxs with ⟨hx0, hx1⟩
      rcases Finset.mem_Icc.mp hys with ⟨hy0, hy1⟩
      rcases Finset.mem_product.mp ht with ⟨_, hyt⟩
      rcases Finset.mem_Icc.mp hyt with ⟨_, hy2⟩
      exact slitScreenRight_primalBondInSlit_iff m hm x y .vertical
        hx0 hx1 hy0 hy1 (by intro h; cases h) (by intro; omega)

/-- The analogous literal face-endpoint statement for the left tall screen. -/
theorem slitScreenLeftFaceBond_primalBondInSlit_iff
    (m : ℕ) (hm : 1 ≤ m) (d : LatticeBond)
    (hs : d.source ∈ slitScreenLeftFaceBases m)
    (ht : d.target ∈ slitScreenLeftFaceBases m) :
    slitScreenPrimalBondInSlit (16 * m) (primalBondOfDual d) ↔
      ¬ (d.axis = .horizontal ∧
        (d.base.2 = -(16 * (m : ℤ)) - 1 ∨ d.base.2 = 16 * (m : ℤ))) := by
  rcases d with ⟨⟨x, y⟩, ax⟩
  cases ax with
  | horizontal =>
      change (x, y) ∈ slitScreenLeftFaceBases m at hs
      change (x + 1, y) ∈ slitScreenLeftFaceBases m at ht
      rcases Finset.mem_product.mp hs with ⟨hxs, hys⟩
      rcases Finset.mem_Icc.mp hxs with ⟨hx0, hx1⟩
      rcases Finset.mem_Icc.mp hys with ⟨hy0, hy1⟩
      rcases Finset.mem_product.mp ht with ⟨hxt, _⟩
      rcases Finset.mem_Icc.mp hxt with ⟨_, hx2⟩
      exact slitScreenLeft_primalBondInSlit_iff m hm x y .horizontal
        hx0 hx1 hy0 hy1 (by intro; omega) (by intro h; cases h)
  | vertical =>
      change (x, y) ∈ slitScreenLeftFaceBases m at hs
      change (x, y + 1) ∈ slitScreenLeftFaceBases m at ht
      rcases Finset.mem_product.mp hs with ⟨hxs, hys⟩
      rcases Finset.mem_Icc.mp hxs with ⟨hx0, hx1⟩
      rcases Finset.mem_Icc.mp hys with ⟨hy0, hy1⟩
      rcases Finset.mem_product.mp ht with ⟨_, hyt⟩
      rcases Finset.mem_Icc.mp hyt with ⟨_, hy2⟩
      exact slitScreenLeft_primalBondInSlit_iff m hm x y .vertical
        hx0 hx1 hy0 hy1 (by intro h; cases h) (by intro; omega)

/-- Every dual bond with both endpoints in the literal middle face rectangle
crosses an edge of the actual slit graph. -/
theorem slitScreenMiddleFaceBond_primalBondInSlit
    (m : ℕ) (hm : 1 ≤ m) (d : LatticeBond)
    (hs : d.source ∈ slitScreenMiddleFaceBases m)
    (ht : d.target ∈ slitScreenMiddleFaceBases m) :
    slitScreenPrimalBondInSlit (16 * m) (primalBondOfDual d) := by
  rcases d with ⟨⟨x, y⟩, ax⟩
  cases ax with
  | horizontal =>
      change (x, y) ∈ slitScreenMiddleFaceBases m at hs
      change (x + 1, y) ∈ slitScreenMiddleFaceBases m at ht
      rcases Finset.mem_product.mp hs with ⟨hxs, hys⟩
      rcases Finset.mem_Icc.mp hxs with ⟨hx0, hx1⟩
      rcases Finset.mem_Icc.mp hys with ⟨hy0, hy1⟩
      rcases Finset.mem_product.mp ht with ⟨hxt, _⟩
      rcases Finset.mem_Icc.mp hxt with ⟨_, hx2⟩
      apply slitScreenMiddle_primalBondInSlit m hm x y .horizontal
      · exact hx0
      · omega
      · exact hy0
      · exact hy1
      · omega
      · intro h; cases h
  | vertical =>
      change (x, y) ∈ slitScreenMiddleFaceBases m at hs
      change (x, y + 1) ∈ slitScreenMiddleFaceBases m at ht
      rcases Finset.mem_product.mp hs with ⟨hxs, hys⟩
      rcases Finset.mem_Icc.mp hxs with ⟨hx0, hx1⟩
      rcases Finset.mem_Icc.mp hys with ⟨hy0, hy1⟩
      rcases Finset.mem_product.mp ht with ⟨_, hyt⟩
      rcases Finset.mem_Icc.mp hyt with ⟨_, hy2⟩
      apply slitScreenMiddle_primalBondInSlit m hm x y .vertical
      · exact hx0
      · exact hx1
      · exact hy0
      · omega
      · intro h; cases h
      · omega

end PottsContinuity.FKC.FiniteFK


