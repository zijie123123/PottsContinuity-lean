-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleDualRightBoundaryParity.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleDualBoundaryParity
public import PottsContinuity.FKC.FiniteFK.RectangleVerticalReflection
public import PottsContinuity.FKC.FiniteFK.RectangleLabelCutIncidence
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
open scoped BigOperators

noncomputable section

def rectangleClampedRightLabel (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (j : ℕ) : Bool :=
  σ ⟨(a.1 + (w : ℤ), a.2 + ((Nat.min j h : ℕ) : ℤ)), by
    have hmin : Nat.min j h ≤ h := Nat.min_le_right j h
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> omega⟩

def rectangleDualRightInnerVertex (a : LatticeVertex) (w h : ℕ) (j : ℕ) :
    RectangleDualVertex a w h := by
  have hj : Nat.min j h ≤ h := Nat.min_le_right j h
  refine ⟨(a.1 + (w : ℤ) - 1, a.2 + ((Nat.min j h : ℕ) : ℤ)), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

lemma rectangleDualRightPort_val_of_lt (a : LatticeVertex) (w h : ℕ)
    (j : ℕ) (hj : j < h) :
    (rectangleDualRightPortVertex a w h j).1 =
      (a.1 + (w : ℤ), a.2 + (j : ℤ)) := by
  change (a.1 + (w : ℤ), a.2 + ((Nat.min j h : ℕ) : ℤ)) = _
  simp only [Nat.min_eq_left (Nat.le_of_lt hj)]

lemma rectangleDualRightInner_val_of_lt (a : LatticeVertex) (w h : ℕ)
    (j : ℕ) (hj : j < h) :
    (rectangleDualRightInnerVertex a w h j).1 =
      (a.1 + (w : ℤ) - 1, a.2 + (j : ℤ)) := by
  change (a.1 + (w : ℤ) - 1, a.2 + ((Nat.min j h : ℕ) : ℤ)) = _
  simp only [Nat.min_eq_left (Nat.le_of_lt hj)]

theorem rectangleDualRightPort_adj_iff_left_and_flip
    (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool)
    (j : ℕ) (hj : j < h) (z : RectangleDualVertex a w h) :
    (rectangleLabelCutDualGraph a w h σ).Adj (rectangleDualRightPortVertex a w h j) z ↔
      z = rectangleDualRightInnerVertex a w h j ∧
        rectangleClampedRightLabel a w h σ j !=
          rectangleClampedRightLabel a w h σ (j + 1) := by
  constructor
  · intro hadj
    obtain ⟨b, hs, ht, hdiff, huv⟩ :=
      (rectangleLabelCutDual_adj_iff_bond a w h σ
        (rectangleDualRightPortVertex a w h j) z).mp hadj
    rcases b with ⟨⟨x,y⟩, axis⟩
    have hsOrig := hs
    have htOrig := ht
    rw [mem_latticeRectangle] at hs ht
    have hport := rectangleDualRightPort_val_of_lt a w h j hj
    cases axis
    · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
      rcases huv with hcase | hcase <;>
        have hx := congrArg Prod.fst hcase.1 <;>
        have hy := congrArg Prod.snd hcase.1 <;> rw [hport] at hx hy <;> omega
    · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
      rcases huv with hcase | hcase
      · have hx := congrArg Prod.fst hcase.1
        have hy := congrArg Prod.snd hcase.1
        rw [hport] at hx hy
        omega
      · have hx := congrArg Prod.fst hcase.1
        have hy := congrArg Prod.snd hcase.1
        rw [hport] at hx hy
        have hxy : x = a.1 + (w : ℤ) ∧ y = a.2 + (j : ℤ) := by omega
        have hz : z = rectangleDualRightInnerVertex a w h j := by
          apply Subtype.ext
          calc
            (z : LatticeVertex) = (x - 1,y) := hcase.2
            _ = (a.1 + (w : ℤ) - 1,a.2 + (j : ℤ)) := by rw [hxy.1,hxy.2]
            _ = (rectangleDualRightInnerVertex a w h j : LatticeVertex) :=
              (rectangleDualRightInner_val_of_lt a w h j hj).symm
        subst z
        refine ⟨rfl, ?_⟩
        have hfirst : rectangleClampedRightLabel a w h σ j = σ ⟨(x,y), hsOrig⟩ := by
          apply congrArg σ
          apply Subtype.ext
          change (a.1 + (w : ℤ), a.2 + ((Nat.min j h : ℕ) : ℤ)) = (x,y)
          have hmin : Nat.min j h = j := Nat.min_eq_left (Nat.le_of_lt hj)
          rw [hmin]
          exact Prod.ext hxy.1.symm hxy.2.symm
        have hsecond : rectangleClampedRightLabel a w h σ (j+1) =
            σ ⟨(x,y+1), htOrig⟩ := by
          apply congrArg σ
          apply Subtype.ext
          change (a.1 + (w : ℤ), a.2 + ((Nat.min (j+1) h : ℕ) : ℤ)) = (x,y+1)
          have hmin : Nat.min (j+1) h = j+1 :=
            Nat.min_eq_left (Nat.succ_le_of_lt hj)
          rw [hmin]
          push_cast
          exact Prod.ext hxy.1.symm (by omega)
        have hdiff' : rectangleClampedRightLabel a w h σ j !=
            rectangleClampedRightLabel a w h σ (j+1) := by
          rw [hfirst, hsecond]
          simpa [LatticeBond.source, LatticeBond.target] using hdiff
        exact hdiff'
  · rintro ⟨rfl, hflip⟩
    let b : LatticeBond := ⟨(a.1 + (w : ℤ), a.2 + (j : ℤ)), .vertical⟩
    have hs : b.source ∈ latticeRectangle a w h := by
      rw [mem_latticeRectangle]
      simp only [b, LatticeBond.source]
      constructor <;> constructor <;> omega
    have ht : b.target ∈ latticeRectangle a w h := by
      rw [mem_latticeRectangle]
      simp only [b, LatticeBond.target]
      constructor <;> constructor <;> omega
    have hfirst : rectangleClampedRightLabel a w h σ j = σ ⟨b.source, hs⟩ := by
      simp [rectangleClampedRightLabel, b, LatticeBond.source,
        Nat.min_eq_left (Nat.le_of_lt hj)]
    have hsecond : rectangleClampedRightLabel a w h σ (j+1) =
        σ ⟨b.target, ht⟩ := by
      apply congrArg σ
      apply Subtype.ext
      change (a.1 + (w : ℤ), a.2 + ((Nat.min (j+1) h : ℕ) : ℤ)) =
        (a.1 + (w : ℤ), a.2 + (j : ℤ) + 1)
      have hmin : Nat.min (j+1) h = j+1 :=
        Nat.min_eq_left (Nat.succ_le_of_lt hj)
      rw [hmin]
      push_cast
      congr 1; omega
    have hdiff : σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ := by
      rw [← hfirst, ← hsecond]
      exact hflip
    apply (rectangleLabelCutDual_adj_iff_bond a w h σ
      (rectangleDualRightPortVertex a w h j)
      (rectangleDualRightInnerVertex a w h j)).2
    refine ⟨b, hs, ht, hdiff, Or.inr ?_⟩
    constructor
    · rw [rectangleDualRightPort_val_of_lt a w h j hj]
      simp [b, LatticeBond.faceBase]
    · rw [rectangleDualRightInner_val_of_lt a w h j hj]
      simp [b, LatticeBond.faceBase]

local instance rectangleDualRightVertexFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualVertex a w h) :=
  Fintype.ofFinset (rectangleDualExpanded a w h) (fun _ => Iff.rfl)

noncomputable local instance rectangleDualRightNeighborFintype (a : LatticeVertex)
    (w h : ℕ) (σ : RectangleVertex a w h → Bool) (v : RectangleDualVertex a w h) :
    Fintype ((rectangleLabelCutDualGraph a w h σ).neighborSet v) := by
  classical
  exact Fintype.ofFinset
    ((Finset.univ : Finset (RectangleDualVertex a w h)).filter
      fun z => (rectangleLabelCutDualGraph a w h σ).Adj v z)
    (by intro z; simp [SimpleGraph.neighborSet])

theorem rectangleDualRightPort_degree (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (j : ℕ) (hj : j < h) :
    (rectangleLabelCutDualGraph a w h σ).degree (rectangleDualRightPortVertex a w h j) =
      if rectangleClampedRightLabel a w h σ j !=
          rectangleClampedRightLabel a w h σ (j + 1) then 1 else 0 := by
  classical
  let G := rectangleLabelCutDualGraph a w h σ
  let u := rectangleDualRightPortVertex a w h j
  let v := rectangleDualRightInnerVertex a w h j
  let L := rectangleClampedRightLabel a w h σ j
  let R := rectangleClampedRightLabel a w h σ (j + 1)
  have huv : ∀ z, G.Adj u z ↔ z = v ∧ (L != R) = true := by
    intro z
    exact rectangleDualRightPort_adj_iff_left_and_flip a w h σ j hj z
  have hne : v ≠ u := by
    intro he
    have hx := congrArg (fun z : RectangleDualVertex a w h => z.1.1) he
    rw [rectangleDualRightInner_val_of_lt a w h j hj,
      rectangleDualRightPort_val_of_lt a w h j hj] at hx
    omega
  rw [← G.card_neighborFinset_eq_degree]
  have hset : G.neighborFinset u = if h : L = R then ∅ else {v} := by
    ext z
    rw [G.mem_neighborFinset]
    rw [huv z]
    by_cases h : L = R <;> simp [h]
  rw [hset]
  by_cases h : L = R <;> simp [L, R, h]

def rectangleDualRightPorts (a : LatticeVertex) (w h : ℕ) :
    Finset (RectangleDualVertex a w h) :=
  (Finset.range h).image (rectangleDualRightPortVertex a w h)

lemma rectangleDualRightPortVertex_injOn_range (a : LatticeVertex) (w h : ℕ) :
    Set.InjOn (rectangleDualRightPortVertex a w h) (Finset.range h : Set ℕ) := by
  intro i hi j hj heq
  have hiy := congrArg (fun z : RectangleDualVertex a w h => z.1.2) heq
  rw [rectangleDualRightPort_val_of_lt a w h i (Finset.mem_range.mp hi),
    rectangleDualRightPort_val_of_lt a w h j (Finset.mem_range.mp hj)] at hiy
  exact_mod_cast (add_left_cancel hiy)

theorem rectangleDualRightPortDegreeSum_odd (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hends : rectangleClampedRightLabel a w h σ 0 !=
      rectangleClampedRightLabel a w h σ h) :
    Odd (∑ j ∈ Finset.range h,
      (rectangleLabelCutDualGraph a w h σ).degree
        (rectangleDualRightPortVertex a w h j)) := by
  have hsum : (∑ j ∈ Finset.range h,
      (rectangleLabelCutDualGraph a w h σ).degree
        (rectangleDualRightPortVertex a w h j)) =
      ∑ j ∈ Finset.range h,
        if rectangleClampedRightLabel a w h σ j !=
            rectangleClampedRightLabel a w h σ (j + 1) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    exact rectangleDualRightPort_degree a w h σ j (Finset.mem_range.mp hj)
  rw [hsum]
  exact (rectangleBoolFlipCount_odd_iff
    (rectangleClampedRightLabel a w h σ) h).2 hends

theorem rectangleDualRightPortsDegreeSum_odd (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hends : rectangleClampedRightLabel a w h σ 0 !=
      rectangleClampedRightLabel a w h σ h) :
    Odd (∑ v ∈ rectangleDualRightPorts a w h,
      (rectangleLabelCutDualGraph a w h σ).degree v) := by
  have himage : (∑ v ∈ rectangleDualRightPorts a w h,
      (rectangleLabelCutDualGraph a w h σ).degree v) =
      ∑ j ∈ Finset.range h,
        (rectangleLabelCutDualGraph a w h σ).degree
          (rectangleDualRightPortVertex a w h j) := by
    simpa only [rectangleDualRightPorts] using
      (Finset.sum_image
        (f := fun v : RectangleDualVertex a w h =>
          (rectangleLabelCutDualGraph a w h σ).degree v)
        (s := Finset.range h)
        (g := rectangleDualRightPortVertex a w h)
        (rectangleDualRightPortVertex_injOn_range a w h))
  rw [himage]
  exact rectangleDualRightPortDegreeSum_odd a w h σ hends

theorem rectangleDualTopRow_isolated (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (b : Bool)
    (htop : ∀ v : RectangleVertex a w h, v.1.2 = a.2 + (h : ℤ) → σ v = b)
    (z : RectangleDualVertex a w h) (hz : z.1.2 = a.2 + (h : ℤ)) :
    (rectangleLabelCutDualGraph a w h σ).IsIsolated z := by
  intro y hadj
  obtain ⟨b, hs0, ht0, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ z y).mp hadj
  rcases b with ⟨⟨x,y0⟩,axis⟩
  have hsMem := hs0
  have htMem := ht0
  rw [mem_latticeRectangle] at hs0 ht0
  cases axis
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
    rcases huv with hcase | hcase
    · have hy := congrArg Prod.snd hcase.1
      omega
    · have hy := congrArg Prod.snd hcase.1
      have hy0 : y0 = a.2 + (h : ℤ) := by omega
      have hσs := htop ⟨(x,y0), hsMem⟩ (by omega)
      have hσt := htop ⟨(x+1,y0), htMem⟩ (by omega)
      change σ ⟨(x,y0), hsMem⟩ != σ ⟨(x+1,y0), htMem⟩ at hdiff
      simp [hσs, hσt] at hdiff
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
    rcases huv with hcase | hcase
    · have hy := congrArg Prod.snd hcase.1
      omega
    · have hy := congrArg Prod.snd hcase.1
      omega

end
end PottsContinuity.FKC.FiniteFK
