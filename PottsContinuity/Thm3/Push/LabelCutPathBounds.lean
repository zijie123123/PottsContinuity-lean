module

public import PottsContinuity.PD.Duality.RectangleDualCrossing
public import PottsContinuity.PlanarTopology.DualWalkCurves
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PlanarTopology
noncomputable section

/-- Coordinate form of bottom-port membership. The proof follows the private
bottomPort_mem_of_coords in PD.Duality.RectangleDualCrossing. -/
theorem rectangleDualBottomPorts_of_coords (a : LatticeVertex) (w h : ℕ)
    (z : RectangleDualVertex a w h)
    (hx : a.1 ≤ z.val.1) (hxw : z.val.1 < a.1+(w : ℤ))
    (hy : z.val.2 = a.2-1) : z ∈ rectangleDualBottomPorts a w h := by
  let i := (z.val.1-a.1).toNat
  have hcast : (i : ℤ) = z.val.1-a.1 := Int.toNat_of_nonneg (by omega)
  have hi : i < w := by omega
  have hv : rectangleDualBottomPortVertex a w h i = z := by
    apply Subtype.ext
    rw [rectangleDualBottomPort_val_of_lt a w h i hi]
    exact Prod.ext (by omega) (by omega)
  rw [← hv]
  exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩

/-- A nontrivial label-cut walk cannot visit either isolated exterior side
column. The returned bounds apply to every original support vertex. -/
theorem labelCutDualWalk_support_x_bounds (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hleft : ∀ v : RectangleVertex a w h, v.val.1 = a.1 → σ v = true)
    (hright : ∀ v : RectangleVertex a w h, v.val.1 = a.1+(w : ℤ) → σ v = false)
    {u v : RectangleDualVertex a w h} (p : (rectangleLabelCutDualGraph a w h σ).Walk u v)
    (hp : ¬ p.Nil) (z : RectangleDualVertex a w h) (hz : z ∈ p.support) :
    a.1 ≤ z.val.1 ∧ z.val.1 < a.1+(w : ℤ) := by
  have hb := z.property
  change z.val ∈ latticeRectangle (a.1-1,a.2-1) (w+1) (h+1) at hb
  rw [mem_latticeRectangle] at hb
  have hneLeft : z.val.1 ≠ a.1-1 := by
    intro heq
    exact hp (SimpleGraph.Walk.nil_of_isIsolated_of_mem_support
      (rectangleDualLeftColumn_isolated a w h σ hleft z heq) hz)
  have hneRight : z.val.1 ≠ a.1+(w : ℤ) := by
    intro heq
    exact hp (SimpleGraph.Walk.nil_of_isIsolated_of_mem_support
      (rectangleDualRightColumn_isolated a w h σ hright z heq) hz)
  constructor <;> omega

/-- Labels on the dual graph change by at most one vertical coordinate per
step, including the genuine boundary-port edges. -/
theorem labelCutDual_adj_vertical_step (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (u v : RectangleDualVertex a w h)
    (huv : (rectangleLabelCutDualGraph a w h σ).Adj u v) : |u.val.2-v.val.2| ≤ 1 := by
  have hsquare : squareLattice.Adj u.val v.val :=
    (rectangleDualOpenGraphToSquare a w h
      (rectangleLabelCutDualConfiguration a w h σ)).map_rel huv
  rw [squareLattice_adj_iff] at hsquare
  rcases hsquare with ⟨_,heq⟩ | ⟨_,h⟩
  · rw [heq]
    norm_num
  · exact (abs_le).mpr (by omega)

end
end PottsContinuity.Push
