-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleEdgeCardinality.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleFlowDimension
public import Mathlib.Data.Int.Interval

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

abbrev RectangleHorizontalCoordinates (a : LatticeVertex) (w h : ℕ) :=
  {x : ℤ // x ∈ Finset.Ico a.1 (a.1 + (w : ℤ))} ×
    {y : ℤ // y ∈ Finset.Icc a.2 (a.2 + (h : ℤ))}

abbrev RectangleVerticalCoordinates (a : LatticeVertex) (w h : ℕ) :=
  {x : ℤ // x ∈ Finset.Icc a.1 (a.1 + (w : ℤ))} ×
    {y : ℤ // y ∈ Finset.Ico a.2 (a.2 + (h : ℤ))}

abbrev RectangleHorizontalBondType (a : LatticeVertex) (w h : ℕ) :=
  {b : RectanglePrimalBond a w h // b.1.axis = LatticeAxis.horizontal}

abbrev RectangleVerticalBondType (a : LatticeVertex) (w h : ℕ) :=
  {b : RectanglePrimalBond a w h // b.1.axis = LatticeAxis.vertical}

def rectangleHorizontalBondEquiv (a : LatticeVertex) (w h : ℕ) :
    RectangleHorizontalCoordinates a w h ≃ RectangleHorizontalBondType a w h where
  toFun p := by
    have hx := Finset.mem_Ico.mp p.1.2
    have hy := Finset.mem_Icc.mp p.2.2
    refine ⟨⟨⟨(p.1.1, p.2.1), LatticeAxis.horizontal⟩, ?_⟩, rfl⟩
    change (p.1.1, p.2.1) ∈ latticeRectangle a w h ∧
      (p.1.1 + 1, p.2.1) ∈ latticeRectangle a w h
    constructor
    · rw [mem_latticeRectangle]
      exact ⟨⟨hx.1, by omega⟩, hy⟩
    · rw [mem_latticeRectangle]
      exact ⟨⟨by omega, by omega⟩, hy⟩
  invFun b := by
    rcases b with ⟨⟨⟨base, axis⟩, hmem⟩, haxis⟩
    change axis = LatticeAxis.horizontal at haxis
    cases axis with
    | horizontal =>
      have hs := (mem_latticeRectangle a base w h).mp hmem.1
      have ht := (mem_latticeRectangle a (base.1 + 1, base.2) w h).mp hmem.2
      refine (⟨⟨base.1, ?_⟩, ⟨base.2, ?_⟩⟩ : RectangleHorizontalCoordinates a w h)
      · apply Finset.mem_Ico.mpr
        omega
      · apply Finset.mem_Icc.mpr
        omega
    | vertical => cases haxis
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  right_inv b := by
    rcases b with ⟨⟨⟨base, axis⟩, hmem⟩, haxis⟩
    change axis = LatticeAxis.horizontal at haxis
    cases axis with
    | horizontal => simp [LatticeBond.source, LatticeBond.target]
    | vertical => cases haxis

def rectangleVerticalBondEquiv (a : LatticeVertex) (w h : ℕ) :
    RectangleVerticalCoordinates a w h ≃ RectangleVerticalBondType a w h where
  toFun p := by
    have hx := Finset.mem_Icc.mp p.1.2
    have hy := Finset.mem_Ico.mp p.2.2
    refine ⟨⟨⟨(p.1.1, p.2.1), LatticeAxis.vertical⟩, ?_⟩, rfl⟩
    change (p.1.1, p.2.1) ∈ latticeRectangle a w h ∧
      (p.1.1, p.2.1 + 1) ∈ latticeRectangle a w h
    constructor
    · rw [mem_latticeRectangle]
      exact ⟨hx, ⟨hy.1, by omega⟩⟩
    · rw [mem_latticeRectangle]
      exact ⟨hx, ⟨by omega, by omega⟩⟩
  invFun b := by
    rcases b with ⟨⟨⟨base, axis⟩, hmem⟩, haxis⟩
    change axis = LatticeAxis.vertical at haxis
    cases axis with
    | horizontal => cases haxis
    | vertical =>
      have hs := (mem_latticeRectangle a base w h).mp hmem.1
      have ht := (mem_latticeRectangle a (base.1, base.2 + 1) w h).mp hmem.2
      refine (⟨⟨base.1, ?_⟩, ⟨base.2, ?_⟩⟩ : RectangleVerticalCoordinates a w h)
      · apply Finset.mem_Icc.mpr
        omega
      · apply Finset.mem_Ico.mpr
        omega
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  right_inv b := by
    rcases b with ⟨⟨⟨base, axis⟩, hmem⟩, haxis⟩
    change axis = LatticeAxis.vertical at haxis
    cases axis with
    | horizontal => cases haxis
    | vertical => simp [LatticeBond.source, LatticeBond.target]

def rectanglePrimalBondAxisEquiv (a : LatticeVertex) (w h : ℕ) :
    RectanglePrimalBond a w h ≃
      RectangleHorizontalBondType a w h ⊕ RectangleVerticalBondType a w h where
  toFun b := by
    rcases b with ⟨⟨base, axis⟩, hmem⟩
    cases axis with
    | horizontal => exact Sum.inl ⟨⟨⟨base, .horizontal⟩, hmem⟩, rfl⟩
    | vertical => exact Sum.inr ⟨⟨⟨base, .vertical⟩, hmem⟩, rfl⟩
  invFun b := by
    rcases b with b | b
    · exact b.1
    · exact b.1
  left_inv b := by
    rcases b with ⟨⟨base, axis⟩, hmem⟩
    cases axis <;> rfl
  right_inv b := by
    rcases b with b | b
    · rcases b with ⟨⟨⟨base, axis⟩, hmem⟩, hb⟩
      change axis = LatticeAxis.horizontal at hb
      cases axis with
      | horizontal => rfl
      | vertical => cases hb
    · rcases b with ⟨⟨⟨base, axis⟩, hmem⟩, hb⟩
      change axis = LatticeAxis.vertical at hb
      cases axis with
      | horizontal => cases hb
      | vertical => rfl

lemma rectangleHorizontalCoordinates_card (a : LatticeVertex) (w h : ℕ) :
    Fintype.card (RectangleHorizontalCoordinates a w h) = w * (h + 1) := by
  rw [Fintype.card_prod, Fintype.card_coe, Int.card_Ico,
    Fintype.card_coe, Int.card_Icc]
  have hx : a.1 + (w : ℤ) - a.1 = (w : ℤ) := by ring
  have hy : a.2 + (h : ℤ) + 1 - a.2 = (h + 1 : ℤ) := by ring
  rw [hx, hy]
  norm_num

lemma rectangleVerticalCoordinates_card (a : LatticeVertex) (w h : ℕ) :
    Fintype.card (RectangleVerticalCoordinates a w h) = (w + 1) * h := by
  rw [Fintype.card_prod, Fintype.card_coe, Int.card_Icc,
    Fintype.card_coe, Int.card_Ico]
  have hx : a.1 + (w : ℤ) + 1 - a.1 = (w + 1 : ℤ) := by ring
  have hy : a.2 + (h : ℤ) - a.2 = (h : ℤ) := by ring
  rw [hx, hy]
  norm_num

local instance rectangleHorizontalBondTypeFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleHorizontalBondType a w h) :=
  Fintype.ofEquiv (RectangleHorizontalCoordinates a w h)
    (rectangleHorizontalBondEquiv a w h)
local instance rectangleVerticalBondTypeFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleVerticalBondType a w h) :=
  Fintype.ofEquiv (RectangleVerticalCoordinates a w h)
    (rectangleVerticalBondEquiv a w h)
local instance rectanglePrimalBondFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectanglePrimalBond a w h) :=
  Fintype.ofEquiv (RectangleHorizontalBondType a w h ⊕ RectangleVerticalBondType a w h)
    (rectanglePrimalBondAxisEquiv a w h).symm

theorem rectanglePrimalBond_card (a : LatticeVertex) (w h : ℕ) :
    Fintype.card (RectanglePrimalBond a w h) = w * (h + 1) + (w + 1) * h := by
  rw [Fintype.card_congr (rectanglePrimalBondAxisEquiv a w h)]
  simp only [Fintype.card_sum]
  have hH := Fintype.card_congr (rectangleHorizontalBondEquiv a w h).symm
  have hV := Fintype.card_congr (rectangleVerticalBondEquiv a w h).symm
  calc
    _ = Fintype.card (RectangleHorizontalCoordinates a w h) +
        Fintype.card (RectangleVerticalCoordinates a w h) := by rw [hH, hV]
    _ = _ := by rw [rectangleHorizontalCoordinates_card, rectangleVerticalCoordinates_card]

theorem rectangleGraph_edgeSet_card (a : LatticeVertex) (w h : ℕ) :
    Nat.card (rectangleGraph a w h).edgeSet = w * (h + 1) + (w + 1) * h := by
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (rectangleGraph a w h).edgeSet =
        Fintype.card (RectanglePrimalBond a w h) :=
      Fintype.card_congr (rectanglePrimalEdgeBondEquiv a w h)
    _ = _ := rectanglePrimalBond_card a w h

theorem rectangleGraph_edgeSet_card_expanded (a : LatticeVertex) (w h : ℕ) :
    Nat.card (rectangleGraph a w h).edgeSet = 2 * w * h + w + h := by
  rw [rectangleGraph_edgeSet_card]
  ring

end

end PottsContinuity.FKC.FiniteFK
