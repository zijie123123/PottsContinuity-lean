-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRectangle.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverGraph
public import PottsContinuity.FKC.Rectangle
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC

/-- The finite rectangle in sheet `k`, with base rectangle `[-n,n] × [0,n]`. -/
def parafermionicCoverRectangleLift (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (v : RectangleVertex (-(n : ℤ), 0) (2 * n) n) : ParafermionicCoverBoxVertex n := by
  refine ⟨(v.1, k), ?_⟩
  change (v.1, k) ∈
    (latticeBox (0, 0) n ×ˢ Finset.Icc (-(n ^ 5 : ℕ) : ℤ) (n ^ 5 : ℤ))
  rw [Finset.mem_product]
  constructor
  · rw [mem_latticeBox]
    rcases (mem_latticeRectangle (-(n : ℤ), 0) v.1 (2 * n) n).mp v.2 with
      ⟨⟨hx₁,hx₂⟩,⟨hy₁,hy₂⟩⟩
    norm_num at hx₁ hx₂ hy₁ hy₂ ⊢
    constructor <;> omega
  · simpa using hk

@[simp] theorem parafermionicCoverRectangleLift_val (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (v : RectangleVertex (-(n : ℤ), 0) (2 * n) n) :
    (parafermionicCoverRectangleLift n k hk v).1 = (v.1, k) := rfl

theorem parafermionicCoverRectangleLift_injective (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)) :
    Function.Injective (parafermionicCoverRectangleLift n k hk) := by
  intro u v h
  apply Subtype.ext
  exact congrArg Prod.fst (congrArg Subtype.val h)

theorem parafermionicCoverRectangle_sheetShift_eq_zero (n : ℕ)
    (u v : RectangleVertex (-(n : ℤ), 0) (2 * n) n) :
    parafermionicCoverSheetShift u.1 v.1 = 0 := by
  have hu : 0 ≤ u.1.2 := by
    have h := (mem_latticeRectangle (-(n : ℤ), 0) u.1 (2 * n) n).mp u.2
    exact h.2.1
  unfold parafermionicCoverSheetShift
  split_ifs <;> omega

theorem parafermionicCoverRectangleLift_adj_iff (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (u v : RectangleVertex (-(n : ℤ), 0) (2 * n) n) :
    (parafermionicCoverBoxGraph n).Adj
      (parafermionicCoverRectangleLift n k hk u)
      (parafermionicCoverRectangleLift n k hk v) ↔
    (rectangleGraph (-(n : ℤ), 0) (2 * n) n).Adj u v := by
  change parafermionicCoverGraph.Adj (u.1, k) (v.1, k) ↔ _
  change (squareLattice.Adj u.1 v.1 ∧
    k = k + parafermionicCoverSheetShift u.1 v.1) ↔ squareLattice.Adj u.1 v.1
  rw [parafermionicCoverRectangle_sheetShift_eq_zero]
  simp

def parafermionicCoverRectangleEmbedding (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)) :
    rectangleGraph (-(n : ℤ), 0) (2 * n) n ↪g parafermionicCoverBoxGraph n where
  toFun := parafermionicCoverRectangleLift n k hk
  inj' := parafermionicCoverRectangleLift_injective n k hk
  map_rel_iff' := by
    intro u v
    exact parafermionicCoverRectangleLift_adj_iff n k hk u v

/-- An ambient neighbor of a lifted strip vertex which lies outside that
strip can only be immediately below its bottom side, in the same sheet. -/
theorem parafermionicCoverRectangle_neighbor_outside_is_bottom
    (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (u v : ParafermionicCoverBoxVertex n)
    (hu : ∃ r : RectangleVertex (-(n : ℤ), 0) (2 * n) n,
      u = parafermionicCoverRectangleLift n k hk r)
    (hadj : (parafermionicCoverBoxGraph n).Adj u v)
    (hvout : ∀ r : RectangleVertex (-(n : ℤ), 0) (2 * n) n,
      v ≠ parafermionicCoverRectangleLift n k hk r) :
    v.1.1.2 = -1 ∧ v.1.2 = k := by
  rcases hu with ⟨r, rfl⟩
  have hadj' : parafermionicCoverGraph.Adj (r.1, k) v.1 := hadj
  have hbase := hadj'.1
  change squareLattice.Adj r.1 v.1.1 at hbase
  rw [squareLattice_adj_iff] at hbase
  have hsheet := parafermionicCover_sheetShift_of_adj hadj'
  rcases (parafermionicCoverBoxVertices_mem n v.1).mp v.2 with
    ⟨hxlo, hxhi, hylo, hyhi, hklo, hkhi⟩
  rcases (mem_latticeRectangle (-(n : ℤ), 0) r.1 (2 * n) n).mp r.2 with
    ⟨⟨hrxlo, hrxhi⟩, ⟨hrylo, hryhi⟩⟩
  have hrY : 0 ≤ r.1.2 := by simpa using hrylo
  have hshift : parafermionicCoverSheetShift r.1 v.1.1 = 0 := by
    unfold parafermionicCoverSheetShift
    split_ifs <;> omega
  have hsheet' : v.1.2 = k := by
    rw [hshift] at hsheet
    simpa using hsheet
  have hyneg : v.1.1.2 < 0 := by
    by_contra hnot
    have hnonneg : 0 ≤ v.1.1.2 := by omega
    have hright : -(n : ℤ) + ((2 * n : ℕ) : ℤ) = (n : ℤ) := by
      push_cast
      ring
    have hmem : v.1.1 ∈ latticeRectangle (-(n : ℤ), 0) (2 * n) n := by
      rw [mem_latticeRectangle]
      constructor
      · constructor
        · exact hxlo
        · rw [hright]
          exact hxhi
      · constructor
        · simpa using hnonneg
        · norm_num at hyhi ⊢
          exact hyhi
    have heq : v = parafermionicCoverRectangleLift n k hk ⟨v.1.1, hmem⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl hsheet'
    exact hvout ⟨v.1.1, hmem⟩ heq
  have hybottom : v.1.1.2 = -1 := by
    rcases hbase with hhorizontal | hvertical
    · rcases hhorizontal with ⟨_, hysame⟩
      omega
    · rcases hvertical with ⟨_, hstep | hstep⟩ <;> omega
  exact ⟨hybottom, hsheet'⟩


/-- In the outside-neighbor case, the strip endpoint itself lies on the bottom
side of the rectangle. -/
theorem parafermionicCoverRectangle_neighbor_inside_endpoint_y_zero
    (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (u v : ParafermionicCoverBoxVertex n)
    (hu : ∃ r : RectangleVertex (-(n : ℤ), 0) (2 * n) n,
      u = parafermionicCoverRectangleLift n k hk r)
    (hadj : (parafermionicCoverBoxGraph n).Adj u v)
    (hvout : ∀ r : RectangleVertex (-(n : ℤ), 0) (2 * n) n,
      v ≠ parafermionicCoverRectangleLift n k hk r) :
    u.1.1.2 = 0 := by
  have hvbottom := parafermionicCoverRectangle_neighbor_outside_is_bottom
    n k hk u v hu hadj hvout
  rcases hu with ⟨r, rfl⟩
  have hrY : 0 ≤ r.1.2 := by
    have hrect := (mem_latticeRectangle (-(n : ℤ), 0) r.1 (2 * n) n).mp r.2
    exact hrect.2.1
  have hbase := hadj.1
  change squareLattice.Adj r.1 v.1.1 at hbase
  rw [squareLattice_adj_iff] at hbase
  change r.1.2 = 0
  rcases hbase with hhorizontal | hvertical
  · omega
  · rcases hvertical with ⟨_, hstep | hstep⟩ <;> omega

end PottsContinuity.FKC
