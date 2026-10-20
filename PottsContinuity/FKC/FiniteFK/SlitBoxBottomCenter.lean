-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxBottomCenter.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.AdjacentBoundaryConnectionLowerBound
public import PottsContinuity.FKC.FiniteFK.SlitBoxInteriorCoverLift
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open MeasureTheory

noncomputable section

/-- The literal retained vertex at the center of the bottom side of the slit box. -/
def slitBoxBottomCenterVertex (n : ℕ) : SlitBoxVertex n :=
  ⟨(0, -(n : ℤ)), by
    change (0, -(n : ℤ)) ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)
    rw [mem_latticeRectangle]
    constructor
    · constructor <;> omega
    · constructor <;> omega⟩

@[simp] theorem slitBoxBottomCenterVertex_val (n : ℕ) :
    (slitBoxBottomCenterVertex n).val = (0, -(n : ℤ)) := rfl

theorem slitBoxBottomCenterVertex_off_arc (n : ℕ) (hn : 1 ≤ n) :
    slitBoxBottomCenterVertex n ∉ slitBoxWiredArc n := by
  rw [mem_slitBoxWiredArc_iff]
  simp only [slitBoxBottomCenterVertex_val]
  omega

def slitBoxBottomCenterInteriorVertex (n : ℕ) (hn : 1 ≤ n) :
    SlitBoxInteriorVertex n :=
  ⟨slitBoxBottomCenterVertex n, slitBoxBottomCenterVertex_off_arc n hn⟩

@[simp] theorem slitBoxBottomCenterInteriorVertex_val (n : ℕ) (hn : 1 ≤ n) :
    (slitBoxBottomCenterInteriorVertex n hn).val = slitBoxBottomCenterVertex n := rfl

private theorem slitBoxBottomCenter_origin_adj :
    (slitBoxGraph 1).Adj (slitBoxBottomCenterVertex 1)
      ⟨(0, 0), by
        change (0, 0) ∈ latticeRectangle (-1, -1) 2 2
        rw [mem_latticeRectangle]
        norm_num⟩ := by
  rw [slitBoxGraph_adj_iff]
  constructor
  · exact (squareLattice_adj_iff _ _).2 (Or.inr ⟨by norm_num, Or.inl (by norm_num)⟩)
  · simp [slitBoxBottomCenterVertex_val]

/-- At the exceptional smallest scale, the actual wired slit arc-hit mass from
the bottom-center vertex has the one-edge finite-energy lower bound. -/
theorem slitBox_bottom_center_arc_hit_probability_lower_bound_at_one
    (q : ClusterWeight) :
    (1 / (1 + loopWeight q) : ℝ) ≤
      (measure (slitBoxGraph 1) q (slitBoxBoundary 1)
        (slitBoxWiredArcConnectionEvent 1 (slitBoxBottomCenterVertex 1))).toReal := by
  let o : SlitBoxVertex 1 := ⟨(0, 0), by
    change (0, 0) ∈ latticeRectangle (-1, -1) 2 2
    rw [mem_latticeRectangle]
    norm_num⟩
  have horigin : o ∈ slitBoxWiredArc 1 := by
    rw [mem_slitBoxWiredArc_iff]
    norm_num [o]
  have horiginEvent :
      {A : Configuration (slitBoxGraph 1) |
        ∃ z ∈ (slitBoxWiredArc 1 : Set (SlitBoxVertex 1)),
          ActualConnected (slitBoxGraph 1) A o z} = Set.univ := by
    ext A
    constructor
    · intro _
      simp
    · intro _
      refine ⟨o, horigin, ?_⟩
      change (openGraph (slitBoxGraph 1) A).Reachable o o
      exact SimpleGraph.Reachable.refl _
  have h := adjacent_boundary_connection_probability_lower_bound
    q (slitBoxBoundary 1) slitBoxBottomCenter_origin_adj
      (slitBoxWiredArc 1 : Set (SlitBoxVertex 1))
  rw [horiginEvent, measure_univ] at h
  simpa [slitBoxWiredArcConnectionEvent] using h

end
end PottsContinuity.FKC.FiniteFK
