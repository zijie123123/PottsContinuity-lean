-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleDualRightBoundaryPath.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleDualRightBoundaryParity
public import PottsContinuity.FKC.FiniteFK.RectangleDualCrossing
public import PottsContinuity.FKC.FiniteFK.FiniteGraphBoundaryParity
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
open scoped BigOperators

noncomputable section

local instance rightPathDualFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualVertex a w h) := Fintype.ofFinite _

local instance rightPathDualAdjDecidable (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) :
    DecidableRel (rectangleLabelCutDualGraph a w h σ).Adj := Classical.decRel _

def rectangleDualLeftPortsForRightPath (a : LatticeVertex) (w h : ℕ) :
    Finset (RectangleDualVertex a w h) :=
  (Finset.range h).image (fun j => rectangleDualLeftPortVertex a w h j)

def rectangleDualRightPathTarget (a : LatticeVertex) (w h : ℕ) :
    Finset (RectangleDualVertex a w h) :=
  rectangleDualLeftPortsForRightPath a w h ∪ rectangleDualBottomPorts a w h

private theorem rectangleDualRightPath_mem_expanded_iff (a : LatticeVertex) (w h : ℕ)
    (z : LatticeVertex) :
    z ∈ rectangleDualExpanded a w h ↔
      a.1 - 1 ≤ z.1 ∧ z.1 ≤ a.1 + (w : ℤ) ∧
      a.2 - 1 ≤ z.2 ∧ z.2 ≤ a.2 + (h : ℤ) := by
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor <;> intro hz <;> omega

private theorem rightPath_left_port_mem (a : LatticeVertex) (w h : ℕ)
    (z : RectangleDualVertex a w h) (hy : a.2 ≤ z.1.2)
    (hyh : z.1.2 < a.2 + (h : ℤ)) (hx : z.1.1 = a.1 - 1) :
    z ∈ rectangleDualLeftPortsForRightPath a w h := by
  let j := (z.1.2 - a.2).toNat
  have hj0 : 0 ≤ z.1.2 - a.2 := by omega
  have hjcast : (j : ℤ) = z.1.2 - a.2 := by
    simp [j, Int.toNat_of_nonneg hj0]
  have hj : j < h := by omega
  have hval : (rectangleDualLeftPortVertex a w h j).1 = z.1 := by
    apply Prod.ext
    · simp [rectangleDualLeftPortVertex]
      omega
    · simp [rectangleDualLeftPortVertex,
        Nat.min_eq_left (Nat.le_of_lt hj)]
      omega
  have heq : rectangleDualLeftPortVertex a w h j = z := Subtype.ext hval
  rw [← heq]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

private theorem rightPath_bottom_port_mem (a : LatticeVertex) (w h : ℕ)
    (z : RectangleDualVertex a w h) (hx : a.1 ≤ z.1.1)
    (hxw : z.1.1 < a.1 + (w : ℤ)) (hy : z.1.2 = a.2 - 1) :
    z ∈ rectangleDualBottomPorts a w h := by
  let i := (z.1.1 - a.1).toNat
  have hi0 : 0 ≤ z.1.1 - a.1 := by omega
  have hcast : (i : ℤ) = z.1.1 - a.1 := by
    simp [i, Int.toNat_of_nonneg hi0]
  have hi : i < w := by omega
  have hval : (rectangleDualBottomPortVertex a w h i).1 = z.1 := by
    apply Prod.ext <;>
      simp [rectangleDualBottomPortVertex, Nat.min_eq_left (Nat.le_of_lt hi)] <;> omega
  have heq : rectangleDualBottomPortVertex a w h i = z := Subtype.ext hval
  rw [← heq]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

private theorem rectangleDualBottomCorner_isolated_for_rightPath
    (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool)
    (right : Bool) (z : RectangleDualVertex a w h)
    (hx : z.1.1 = if right then a.1 + (w : ℤ) else a.1 - 1)
    (hy : z.1.2 = a.2 - 1) :
    (rectangleLabelCutDualGraph a w h σ).IsIsolated z := by
  intro y hadj
  obtain ⟨b, hs, ht, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ z y).mp hadj
  rcases b with ⟨⟨x,y0⟩,axis⟩
  rw [mem_latticeRectangle] at hs ht
  have hx' : z.1.1 = a.1 + (w : ℤ) ∨ z.1.1 = a.1 - 1 := by
    by_cases right <;> simp_all
  cases axis
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
    rcases huv with hcase | hcase
    · rcases hcase with ⟨hface, _⟩
      have hy0 := congrArg Prod.snd hface
      have hx0 := congrArg Prod.fst hface
      rcases hx' with hright | hleft <;> omega
    · rcases hcase with ⟨hface, _⟩
      have hy0 := congrArg Prod.snd hface
      have hx0 := congrArg Prod.fst hface
      rcases hx' with hright | hleft <;> omega
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
    rcases huv with hcase | hcase
    · rcases hcase with ⟨hface, _⟩
      have hy0 := congrArg Prod.snd hface
      omega
    · rcases hcase with ⟨hface, _⟩
      have hy0 := congrArg Prod.snd hface
      omega

private theorem rightPath_right_port_mem (a : LatticeVertex) (w h : ℕ)
    (z : RectangleDualVertex a w h) (hy : a.2 ≤ z.1.2)
    (hyh : z.1.2 < a.2 + (h : ℤ)) (hx : z.1.1 = a.1 + (w : ℤ)) :
    z ∈ rectangleDualRightPorts a w h := by
  let j := (z.1.2 - a.2).toNat
  have hj0 : 0 ≤ z.1.2 - a.2 := by omega
  have hjcast : (j : ℤ) = z.1.2 - a.2 := by
    simp [j, Int.toNat_of_nonneg hj0]
  have hj : j < h := by omega
  have hval : (rectangleDualRightPortVertex a w h j).1 = z.1 := by
    rw [rectangleDualRightPort_val_of_lt a w h j hj]
    exact Prod.ext hx.symm (by omega)
  have heq : rectangleDualRightPortVertex a w h j = z := Subtype.ext hval
  rw [← heq]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

private theorem rectangleDualRightPath_ports_disjoint (a : LatticeVertex) (w h : ℕ) :
    Disjoint (rectangleDualRightPorts a w h) (rectangleDualRightPathTarget a w h) := by
  rw [Finset.disjoint_left]
  intro z hzB hzT
  rcases Finset.mem_image.mp hzB with ⟨i, hi, rfl⟩
  rcases Finset.mem_union.mp hzT with hzL | hzD
  · rcases Finset.mem_image.mp hzL with ⟨j, hj, heq⟩
    have hx := congrArg (fun v : RectangleDualVertex a w h => v.1.1) heq
    simp [rectangleDualRightPortVertex, rectangleDualLeftPortVertex] at hx
    omega
  · rcases Finset.mem_image.mp hzD with ⟨j, hj, heq⟩
    have hx := congrArg (fun v : RectangleDualVertex a w h => v.1.1) heq
    rw [rectangleDualRightPort_val_of_lt a w h i (Finset.mem_range.mp hi),
      rectangleDualBottomPort_val_of_lt a w h j (Finset.mem_range.mp hj)] at hx
    have hjlt : (j : ℤ) < (w : ℤ) := by exact_mod_cast (Finset.mem_range.mp hj)
    have hlt : a.1 + (j : ℤ) < a.1 + (w : ℤ) := by omega
    omega

private theorem rectangleDualRightPath_outside_degree_even
    (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool)
    (htop : ∀ v : RectangleVertex a w h, v.1.2 = a.2 + (h : ℤ) → σ v = true)
    (z : RectangleDualVertex a w h)
    (hzB : z ∉ rectangleDualRightPorts a w h)
    (hzT : z ∉ rectangleDualRightPathTarget a w h) :
    Even (((rectangleLabelCutDualGraph a w h σ).neighborSet z).ncard) := by
  rcases z with ⟨⟨x,y⟩, hz⟩
  rcases (rectangleDualRightPath_mem_expanded_iff a w h (x,y)).mp hz with
    ⟨hxl,hxr,hyl,hyr⟩
  by_cases htoprow : y = a.2 + (h : ℤ)
  · have hzero := (rectangleDualTopRow_isolated a w h σ true htop
        ⟨(x,y),hz⟩ htoprow).degree_eq_zero
    rw [← SimpleGraph.ncard_neighborSet] at hzero
    rw [hzero]
    exact ⟨0, rfl⟩
  · by_cases hbottom : y = a.2 - 1
    · by_cases hleft : x = a.1 - 1
      · have hiso := rectangleDualBottomCorner_isolated_for_rightPath
          a w h σ false ⟨(x,y),hz⟩ (by simp [hleft]) (by simp [hbottom])
        have hzero := hiso.degree_eq_zero
        rw [← SimpleGraph.ncard_neighborSet] at hzero
        rw [hzero]
        exact ⟨0, rfl⟩
      · by_cases hright : x = a.1 + (w : ℤ)
        · have hiso := rectangleDualBottomCorner_isolated_for_rightPath
            a w h σ true ⟨(x,y),hz⟩ (by simp [hright]) (by simp [hbottom])
          have hzero := hiso.degree_eq_zero
          rw [← SimpleGraph.ncard_neighborSet] at hzero
          rw [hzero]
          exact ⟨0, rfl⟩
        · have hx : a.1 ≤ x := by omega
          have hxw : x < a.1 + (w : ℤ) := by omega
          have hmem := rightPath_bottom_port_mem a w h ⟨(x,y),hz⟩ hx hxw hbottom
          have hnot : (⟨(x,y),hz⟩ : RectangleDualVertex a w h) ∉
              rectangleDualBottomPorts a w h := by
            intro hm
            exact hzT (Finset.mem_union_right _ hm)
          exact False.elim (hnot hmem)
    · by_cases hleft : x = a.1 - 1
      · have hy : a.2 ≤ y := by omega
        have hyh : y < a.2 + (h : ℤ) := by omega
        have hmem := rightPath_left_port_mem a w h ⟨(x,y),hz⟩ hy hyh hleft
        have hnot : (⟨(x,y),hz⟩ : RectangleDualVertex a w h) ∉
            rectangleDualLeftPortsForRightPath a w h := by
          intro hm
          exact hzT (Finset.mem_union_left _ hm)
        exact False.elim (hnot hmem)
      · by_cases hright : x = a.1 + (w : ℤ)
        · have hy : a.2 ≤ y := by omega
          have hyh : y < a.2 + (h : ℤ) := by omega
          have hmem := rightPath_right_port_mem a w h ⟨(x,y),hz⟩ hy hyh hright
          exact False.elim (hzB hmem)
        · have hx : a.1 ≤ x := by omega
          have hxw : x < a.1 + (w : ℤ) := by omega
          have hy : a.2 ≤ y := by omega
          have hyh : y < a.2 + (h : ℤ) := by omega
          have hpar := rectangleLabelCutDual_interior_degree_even a w h σ x y
            hx hxw hy hyh
          rw [← SimpleGraph.ncard_neighborSet] at hpar
          change Even (((rectangleLabelCutDualGraph a w h σ).neighborSet
            (⟨(x,y),hz⟩ : RectangleDualVertex a w h)).ncard) at hpar
          exact hpar

theorem rectangleDual_right_boundary_reachable
    (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool)
    (htop : ∀ v : RectangleVertex a w h, v.1.2 = a.2 + (h : ℤ) → σ v = true)
    (hbottomRight : rectangleClampedRightLabel a w h σ 0 = false)
    (htopRight : rectangleClampedRightLabel a w h σ h = true) :
    ∃ b ∈ rectangleDualRightPorts a w h,
      ∃ t ∈ rectangleDualRightPathTarget a w h,
        (rectangleLabelCutDualGraph a w h σ).Reachable b t := by
  let B := rectangleDualRightPorts a w h
  let T := rectangleDualRightPathTarget a w h
  have hends : rectangleClampedRightLabel a w h σ 0 !=
      rectangleClampedRightLabel a w h σ h := by simp [hbottomRight, htopRight]
  have hodd := rectangleDualRightPortsDegreeSum_odd a w h σ hends
  have heven : ∀ z, z ∉ B → z ∉ T →
      Even (((rectangleLabelCutDualGraph a w h σ).neighborSet z).ncard) := by
    intro z hzB hzT
    exact rectangleDualRightPath_outside_degree_even a w h σ htop z hzB hzT
  have hodd' := hodd
  simp_rw [← SimpleGraph.ncard_neighborSet] at hodd'
  exact @exists_reachable_between_of_odd_ncard_neighbor_sum
    (RectangleDualVertex a w h) (rightPathDualFintype a w h)
    (rectangleLabelCutDualGraph a w h σ) (Classical.decEq _)
    (rightPathDualAdjDecidable a w h σ) B T
    (rectangleDualRightPath_ports_disjoint a w h) heven hodd'

theorem rectangleDual_right_boundary_reachable_port_index_ge
    (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool)
    (m : ℕ)
    (hfalse : ∀ j ≤ m, rectangleClampedRightLabel a w h σ j = false)
    (b : RectangleDualVertex a w h) (hb : b ∈ rectangleDualRightPorts a w h)
    (t : RectangleDualVertex a w h) (ht : t ∈ rectangleDualRightPathTarget a w h)
    (hreach : (rectangleLabelCutDualGraph a w h σ).Reachable b t) :
    ∃ j, j < h ∧ rectangleDualRightPortVertex a w h j = b ∧ m ≤ j := by
  rcases Finset.mem_image.mp hb with ⟨j, hj, rfl⟩
  refine ⟨j, Finset.mem_range.mp hj, rfl, ?_⟩
  by_contra hjm
  have hjltm : j < m := by omega
  have hj1m : j + 1 ≤ m := by omega
  have hleft := hfalse j (by omega)
  have hright := hfalse (j + 1) hj1m
  have hne : rectangleDualRightPortVertex a w h j ≠ t := by
    intro heq
    have hdisj := Finset.disjoint_left.mp (rectangleDualRightPath_ports_disjoint a w h)
    exact hdisj (Finset.mem_image.mpr ⟨j, hj, rfl⟩) (heq ▸ ht)
  rcases hreach with ⟨p⟩
  have hlen : 0 < p.length := by
    by_contra hn
    have hz : p.length = 0 := by omega
    exact hne (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hadj := p.adj_getVert_succ (by omega : 0 < p.length)
  have hadj' : (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleDualRightPortVertex a w h j) (p.getVert 1) := by
    simpa using hadj
  have hflip := (rectangleDualRightPort_adj_iff_left_and_flip a w h σ j
    (Finset.mem_range.mp hj) (p.getVert 1)).mp hadj'
  simp [hleft, hright] at hflip

end
end PottsContinuity.FKC.FiniteFK
