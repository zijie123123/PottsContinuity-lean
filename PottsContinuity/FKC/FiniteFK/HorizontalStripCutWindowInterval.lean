-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripCutWindowInterval.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutExploration
public import PottsContinuity.FKC.FiniteFK.RectangleEvents
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial

noncomputable section

local instance cutWindowIntervalEdgeFintype (n : ℕ) (lo hi : ℤ) :
    Fintype (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).edgeSet := Fintype.ofFinite _
local instance cutWindowOuterEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance cutWindowOuterEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

theorem horizontalStripCutWindowInterval_subset {N n : ℕ} {lo hi : ℤ}
    (hlo : -(N : ℤ) ≤ lo) (hhi : hi ≤ N) (hle : lo ≤ hi) :
    latticeRectangle (lo, 0) (hi - lo).toNat (2 * n) ⊆
      latticeRectangle (-(N : ℤ), 0) (2 * N) (2 * n) := by
  intro v hv
  rw [mem_latticeRectangle] at hv ⊢
  rcases hv with ⟨⟨hxlo, hxhi⟩, hy⟩
  constructor
  · constructor
    · omega
    · have hwidth : ((hi - lo).toNat : ℤ) = hi - lo := by
        rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
      omega
  · exact hy

def horizontalStripCutWindowIntervalEmbedding {N n : ℕ} {lo hi : ℤ}
    (hlo : -(N : ℤ) ≤ lo) (hhi : hi ≤ N) (hle : lo ≤ hi) :
    RectangleVertex (lo, 0) (hi - lo).toNat (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
  rectangleVertexEmbedding (horizontalStripCutWindowInterval_subset hlo hhi hle)

@[simp] theorem horizontalStripCutWindowIntervalEmbedding_val {N n : ℕ} {lo hi : ℤ}
    (hlo : -(N : ℤ) ≤ lo) (hhi : hi ≤ N) (hle : lo ≤ hi)
    (v : RectangleVertex (lo, 0) (hi - lo).toNat (2 * n)) :
    (horizontalStripCutWindowIntervalEmbedding hlo hhi hle v).val = v.val := rfl

theorem horizontalStripCutWindowIntervalEmbedding_range {N n : ℕ} {lo hi : ℤ}
    (hlo : -(N : ℤ) ≤ lo) (hhi : hi ≤ N) (hle : lo ≤ hi) :
    Set.range (horizontalStripCutWindowIntervalEmbedding (N := N) (n := n) hlo hhi hle) =
      horizontalStripCutWindow N n lo hi := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    change lo ≤ v.val.1 ∧ v.val.1 ≤ hi
    have hv := v.property
    rw [mem_latticeRectangle] at hv
    rcases hv with ⟨⟨hxlo, hxhi⟩, _⟩
    have hwidth : ((hi - lo).toNat : ℤ) = hi - lo := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
    constructor
    · exact hxlo
    · omega
  · intro hz
    change lo ≤ z.val.1 ∧ z.val.1 ≤ hi at hz
    rcases hz with ⟨hzlo, hzhi⟩
    refine ⟨⟨z.val, ?_⟩, ?_⟩
    · rw [mem_latticeRectangle]
      constructor
      · constructor
        · exact hzlo
        · have hwidth : ((hi - lo).toNat : ℤ) = hi - lo := by
            rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
          omega
      · have hzprop := z.property
        rw [mem_latticeRectangle] at hzprop
        exact hzprop.2
    · apply Subtype.ext
      rfl

theorem horizontalStripCutWindowInterval_map_le {N n : ℕ} {lo hi : ℤ}
    (hlo : -(N : ℤ) ≤ lo) (hhi : hi ≤ N) (hle : lo ≤ hi) :
    (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).map
      (horizontalStripCutWindowIntervalEmbedding hlo hhi hle) ≤
        horizontalStripCutRectangle N n :=
  rectangleGraph_map_rectangleVertexEmbedding (horizontalStripCutWindowInterval_subset hlo hhi hle)

theorem horizontalStripCutWindowInterval_map_eq_windowGraph {N n : ℕ} {lo hi : ℤ}
    (hlo : -(N : ℤ) ≤ lo) (hhi : hi ≤ N) (hle : lo ≤ hi) :
    (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).map
      (horizontalStripCutWindowIntervalEmbedding hlo hhi hle) =
        horizontalStripCutWindowGraph N n lo hi := by
  classical
  ext u v
  change ((rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).map
      (horizontalStripCutWindowIntervalEmbedding hlo hhi hle)).Adj u v ↔
    (((horizontalStripCutRectangle N n).induce (horizontalStripCutWindow N n lo hi)).map
      (Function.Embedding.subtype _)).Adj u v
  rw [SimpleGraph.map_adj, SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    refine ⟨⟨horizontalStripCutWindowIntervalEmbedding hlo hhi hle a, ?_⟩,
      ⟨horizontalStripCutWindowIntervalEmbedding hlo hhi hle b, ?_⟩, ?_, rfl, rfl⟩
    · rw [← horizontalStripCutWindowIntervalEmbedding_range hlo hhi hle]
      exact ⟨a, rfl⟩
    · rw [← horizontalStripCutWindowIntervalEmbedding_range hlo hhi hle]
      exact ⟨b, rfl⟩
    · exact (horizontalStripCutWindowInterval_map_le hlo hhi hle)
        ((SimpleGraph.map_adj_apply).2 hab)
  · rintro ⟨a, b, hab, rfl, rfl⟩
    have ha_window : lo ≤ a.val.val.1 ∧ a.val.val.1 ≤ hi := by
      exact a.property
    have hb_window : lo ≤ b.val.val.1 ∧ b.val.val.1 ≤ hi := by
      exact b.property
    let u₀ : RectangleVertex (lo, 0) (hi - lo).toNat (2 * n) := ⟨a.val.val, by
      rw [mem_latticeRectangle]
      constructor
      · constructor
        · exact ha_window.1
        · have hwidth : ((hi - lo).toNat : ℤ) = hi - lo := by
            rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
          have ha_outer := a.val.property
          rw [mem_latticeRectangle] at ha_outer
          omega
      · have ha_outer := a.val.property
        rw [mem_latticeRectangle] at ha_outer
        exact ha_outer.2⟩
    let v₀ : RectangleVertex (lo, 0) (hi - lo).toNat (2 * n) := ⟨b.val.val, by
      rw [mem_latticeRectangle]
      constructor
      · constructor
        · exact hb_window.1
        · have hwidth : ((hi - lo).toNat : ℤ) = hi - lo := by
            rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
          have hb_outer := b.val.property
          rw [mem_latticeRectangle] at hb_outer
          omega
      · have hb_outer := b.val.property
        rw [mem_latticeRectangle] at hb_outer
        exact hb_outer.2⟩
    have hab' : (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).Adj u₀ v₀ := by
      apply (rectangleGraph_adj_iff (lo, 0) (hi - lo).toNat (2 * n) u₀ v₀).2
      apply (rectangleGraph_adj_iff (-(N : ℤ), 0) (2 * N) (2 * n) a.val b.val).1
      exact hab
    refine ⟨u₀, v₀, hab', ?_, ?_⟩
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change v₀.val = b.val.val
      rfl

theorem horizontalStripCutWindowInterval_reveal_eq {N n : ℕ} {lo hi : ℤ}
    (hlo : -(N : ℤ) ≤ lo) (hhi : hi ≤ N) (hle : lo ≤ hi) :
    subgraphRemovedEdges
      ((rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).map
        (horizontalStripCutWindowIntervalEmbedding hlo hhi hle))
      (horizontalStripCutRectangle N n) =
    horizontalStripCutWindowReveal N n lo hi := by
  rw [horizontalStripCutWindowReveal,
    horizontalStripCutWindowInterval_map_eq_windowGraph hlo hhi hle]

end
end PottsContinuity.FKC.FiniteFK
