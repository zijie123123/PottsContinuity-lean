-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverSideBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverGraph
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalk
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC

/-- The literal vertices inside the cover box whose actual cover graph has a
neighbor outside that box. Sheet endpoints are excluded, so this is the
exterior-neighbor boundary in the interior sheets. -/
noncomputable def parafermionicCoverExteriorNeighborBoundary (n : ℕ) :
    Finset ParafermionicCoverVertex := by
  classical
  exact (parafermionicCoverBoxFinset n).filter fun v =>
    -((n ^ 5 : ℕ) : ℤ) < v.2 ∧ v.2 < ((n ^ 5 : ℕ) : ℤ) ∧
      ∃ w : ParafermionicCoverVertex,
        parafermionicCoverGraph.Adj v w ∧ w ∉ parafermionicCoverBoxVertices n

/-- An exterior-neighbor boundary vertex in an interior sheet lies on one of
the four base-coordinate sides of the box. -/
theorem parafermionicCoverExteriorNeighborBoundary_coord
    (n : ℕ) {v : ParafermionicCoverVertex}
    (hv : v ∈ parafermionicCoverExteriorNeighborBoundary n) :
    v.1.1 = -(n : ℤ) ∨ v.1.1 = (n : ℤ) ∨
      v.1.2 = -(n : ℤ) ∨ v.1.2 = (n : ℤ) := by
  classical
  rcases Finset.mem_filter.mp hv with ⟨hbox, hfilter⟩
  rcases hfilter with ⟨hklo, hkhi, w, hadj, hout⟩
  have hb := (parafermionicCoverBoxVertices_mem n v).mp hbox
  by_contra hnot
  have hnotXm : v.1.1 ≠ -(n : ℤ) := by
    intro h
    exact hnot (Or.inl h)
  have hnotXp : v.1.1 ≠ (n : ℤ) := by
    intro h
    exact hnot (Or.inr (Or.inl h))
  have hnotYm : v.1.2 ≠ -(n : ℤ) := by
    intro h
    exact hnot (Or.inr (Or.inr (Or.inl h)))
  have hnotYp : v.1.2 ≠ (n : ℤ) := by
    intro h
    exact hnot (Or.inr (Or.inr (Or.inr h)))
  have hxi : -(n : ℤ) < v.1.1 ∧ v.1.1 < n := by omega
  have hyi : -(n : ℤ) < v.1.2 ∧ v.1.2 < n := by omega
  have hdx' : -(1 : ℤ) ≤ w.1.1 - v.1.1 ∧ w.1.1 - v.1.1 ≤ 1 := by
    have hb := (squareLattice_adj_iff v.1 w.1).mp hadj.1
    rcases hb with ⟨horiz, hy⟩ | ⟨hx, vert⟩
    · rcases horiz with h | h <;> constructor <;> omega
    · constructor <;> omega
  have hdy' : -(1 : ℤ) ≤ w.1.2 - v.1.2 ∧ w.1.2 - v.1.2 ≤ 1 := by
    have hb := (squareLattice_adj_iff v.1 w.1).mp hadj.1
    rcases hb with ⟨horiz, hy⟩ | ⟨hx, vert⟩
    · constructor <;> omega
    · rcases vert with h | h <;> constructor <;> omega
  have hdk := abs_le.mp (parafermionicCover_adj_sheet_abs_le_one hadj)
  have hwx : -(n : ℤ) ≤ w.1.1 ∧ w.1.1 ≤ n := by omega
  have hwy : -(n : ℤ) ≤ w.1.2 ∧ w.1.2 ≤ n := by omega
  have hwk : -((n ^ 5 : ℕ) : ℤ) ≤ w.2 ∧ w.2 ≤ ((n ^ 5 : ℕ) : ℤ) := by
    omega
  have hwin : w ∈ parafermionicCoverBoxVertices n := by
    rw [parafermionicCoverBoxVertices_mem]
    exact ⟨hwx.1, hwx.2, hwy.1, hwy.2, hwk.1, hwk.2⟩
  exact hout hwin

/-- One vertical side of the cover box, with all allowed y-coordinates and
sheets. -/
def parafermionicCoverBoxXSide (n : ℕ) (x : ℤ) :
    Finset ParafermionicCoverVertex :=
  (({x} : Finset ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ
    Finset.Icc (-((n ^ 5 : ℕ) : ℤ)) ((n ^ 5 : ℕ) : ℤ)

/-- One horizontal side of the cover box, with all allowed x-coordinates and
sheets. -/
def parafermionicCoverBoxYSide (n : ℕ) (y : ℤ) :
    Finset ParafermionicCoverVertex :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ {y}) ×ˢ
    Finset.Icc (-((n ^ 5 : ℕ) : ℤ)) ((n ^ 5 : ℕ) : ℤ)

def parafermionicCoverBoxBaseSides (n : ℕ) : Finset ParafermionicCoverVertex :=
  parafermionicCoverBoxXSide n (-(n : ℤ)) ∪
    parafermionicCoverBoxXSide n (n : ℤ) ∪
    parafermionicCoverBoxYSide n (-(n : ℤ)) ∪
    parafermionicCoverBoxYSide n (n : ℤ)

theorem parafermionicCoverExteriorNeighborBoundary_subset_baseSides (n : ℕ) :
    parafermionicCoverExteriorNeighborBoundary n ⊆ parafermionicCoverBoxBaseSides n := by
  classical
  intro v hv
  have hcoord := parafermionicCoverExteriorNeighborBoundary_coord n hv
  have hvbox := (Finset.mem_filter.mp hv).1
  have hb := (parafermionicCoverBoxVertices_mem n v).mp hvbox
  have hy : v.1.2 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := Finset.mem_Icc.mpr ⟨hb.2.2.1, hb.2.2.2.1⟩
  have hx : v.1.1 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := Finset.mem_Icc.mpr ⟨hb.1, hb.2.1⟩
  have hk : v.2 ∈ Finset.Icc (-((n ^ 5 : ℕ) : ℤ)) ((n ^ 5 : ℕ) : ℤ) :=
    Finset.mem_Icc.mpr ⟨hb.2.2.2.2.1, hb.2.2.2.2.2⟩
  rcases hcoord with hxm | hxp | hym | hyp
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    simp only [parafermionicCoverBoxXSide, Finset.mem_product, Finset.mem_singleton]
    exact ⟨⟨hxm, hy⟩, hk⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    simp only [parafermionicCoverBoxXSide, Finset.mem_product, Finset.mem_singleton]
    exact ⟨⟨hxp, hy⟩, hk⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    simp only [parafermionicCoverBoxYSide, Finset.mem_product, Finset.mem_singleton]
    exact ⟨⟨hx, hym⟩, hk⟩
  · apply Finset.mem_union_right
    simp only [parafermionicCoverBoxYSide, Finset.mem_product, Finset.mem_singleton]
    exact ⟨⟨hx, hyp⟩, hk⟩

private theorem card_int_Icc_neg_nat (m : ℕ) :
    (Finset.Icc (-(m : ℤ)) (m : ℤ)).card = 2 * m + 1 := by
  rw [Int.card_Icc]
  have h : (m : ℤ) + 1 - (-(m : ℤ)) = ((2 * m + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h]
  exact Int.toNat_natCast _


theorem parafermionicCoverBoxXSide_card (n : ℕ) (x : ℤ) :
    (parafermionicCoverBoxXSide n x).card = (2 * n + 1) * (2 * n ^ 5 + 1) := by
  classical
  simp only [parafermionicCoverBoxXSide, Finset.card_product, Finset.card_singleton]
  rw [card_int_Icc_neg_nat n, card_int_Icc_neg_nat (n ^ 5)]
  ring

theorem parafermionicCoverBoxYSide_card (n : ℕ) (y : ℤ) :
    (parafermionicCoverBoxYSide n y).card = (2 * n + 1) * (2 * n ^ 5 + 1) := by
  classical
  simp only [parafermionicCoverBoxYSide, Finset.card_product, Finset.card_singleton]
  rw [card_int_Icc_neg_nat n, card_int_Icc_neg_nat (n ^ 5)]
  ring

theorem parafermionicCoverExteriorNeighborBoundary_card_le (n : ℕ) (hn : 1 ≤ n) :
    (parafermionicCoverExteriorNeighborBoundary n).card ≤ 36 * n ^ 6 := by
  have hsub := parafermionicCoverExteriorNeighborBoundary_subset_baseSides n
  have hcard := Finset.card_le_card hsub
  have hunion : (parafermionicCoverBoxBaseSides n).card ≤
      4 * ((2 * n + 1) * (2 * n ^ 5 + 1)) := by
    let A := parafermionicCoverBoxXSide n (-(n : ℤ))
    let B := parafermionicCoverBoxXSide n (n : ℤ)
    let C := parafermionicCoverBoxYSide n (-(n : ℤ))
    let D := parafermionicCoverBoxYSide n (n : ℤ)
    have hAB : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le _ _
    have hABC : ((A ∪ B) ∪ C).card ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    have hABCD : (((A ∪ B) ∪ C) ∪ D).card ≤ ((A ∪ B) ∪ C).card + D.card :=
      Finset.card_union_le _ _
    have hca : A.card = (2 * n + 1) * (2 * n ^ 5 + 1) :=
      parafermionicCoverBoxXSide_card n _
    have hcb : B.card = (2 * n + 1) * (2 * n ^ 5 + 1) :=
      parafermionicCoverBoxXSide_card n _
    have hcc : C.card = (2 * n + 1) * (2 * n ^ 5 + 1) :=
      parafermionicCoverBoxYSide_card n _
    have hcd : D.card = (2 * n + 1) * (2 * n ^ 5 + 1) :=
      parafermionicCoverBoxYSide_card n _
    change (((A ∪ B) ∪ C) ∪ D).card ≤ _
    calc
      _ ≤ ((A ∪ B).card + C.card) + D.card :=
        hABCD.trans (Nat.add_le_add_right hABC _)
      _ ≤ (A.card + B.card) + C.card + D.card := by omega
      _ = 4 * ((2 * n + 1) * (2 * n ^ 5 + 1)) := by
        rw [hca, hcb, hcc, hcd]
        ring
  have hn1 : 2 * n + 1 ≤ 3 * n := by omega
  have hn5one : 1 ≤ n ^ 5 := Nat.one_le_pow 5 n (by omega)
  have hn5 : 2 * n ^ 5 + 1 ≤ 3 * n ^ 5 := by omega
  calc
    (parafermionicCoverExteriorNeighborBoundary n).card ≤
        (parafermionicCoverBoxBaseSides n).card := hcard
    _ ≤ 4 * ((2 * n + 1) * (2 * n ^ 5 + 1)) := hunion
    _ ≤ 4 * ((3 * n) * (3 * n ^ 5)) := by gcongr
    _ = 36 * n ^ 6 := by ring

end PottsContinuity.FKC
