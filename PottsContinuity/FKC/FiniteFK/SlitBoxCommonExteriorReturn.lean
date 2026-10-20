-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCommonExteriorReturn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCanonicalReturnEdges
public import PottsContinuity.FKC.FiniteFK.SlitBoxExteriorReturnSimple
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The top endpoint of the retained vertical wired arc. -/
def slitBoxTopArcVertex (n : ℕ) : SlitBoxVertex n :=
  ⟨(0, (n : ℤ)), by
    rw [mem_latticeRectangle]
    push_cast
    constructor <;> omega⟩

theorem slitBoxTopArcVertex_mem_wiredArc (n : ℕ) :
    slitBoxTopArcVertex n ∈ slitBoxWiredArc n := by
  apply (mem_slitBoxWiredArc_iff n _).2
  simp [slitBoxTopArcVertex]

theorem slitBoxCanonicalTopReturnWalk_isPath
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) :
    (slitBoxCanonicalReturnWalk n u huY huX (slitBoxTopArcVertex n)
      (slitBoxTopArcVertex_mem_wiredArc n)).IsPath := by
  exact slitBoxCanonicalReturnWalk_isPath n hn u huY huX
    (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)

theorem slitBoxCanonicalTopReturnWalk_right_edge_mem
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) :
    s(((n + 1 : ℤ), 0), ((n + 1 : ℤ), 1)) ∈
      (slitBoxCanonicalReturnWalk n u huY huX (slitBoxTopArcVertex n)
        (slitBoxTopArcVertex_mem_wiredArc n)).edges := by
  exact slitBoxCanonicalReturnWalk_right_edge_mem n u huY huX
    (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n) 0 (by omega) (by omega)

private theorem slitBoxCanonicalReturn_horizontal_bound_local
    (n : ℕ) (u : SlitBoxVertex n) (huX : 0 ≤ u.val.1) :
    u.val.1.toNat ≤ n := by
  have huBox := u.property
  rw [mem_latticeRectangle] at huBox
  have hx := huBox.1.2
  have hmax : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by
    push_cast
    omega
  rw [hmax] at hx
  have hxInt : (u.val.1.toNat : ℤ) ≤ (n : ℤ) := by
    rw [Int.toNat_of_nonneg huX]
    exact hx
  exact_mod_cast hxInt

private theorem slitBoxCanonicalReturn_vertical_bound_local
    (n : ℕ) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    t.val.2.toNat ≤ n := by
  have htArc := (mem_slitBoxWiredArc_iff n t).mp ht
  have htInt : (t.val.2.toNat : ℤ) ≤ (n : ℤ) := by
    rw [Int.toNat_of_nonneg htArc.2.1]
    exact htArc.2.2
  exact_mod_cast htInt

theorem slitBoxCanonicalTopReturnWalk_support_in_box
    (n : ℕ) (_hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    {z : LatticeVertex}
    (hz : z ∈ (slitBoxCanonicalReturnWalk n u huY huX (slitBoxTopArcVertex n)
      (slitBoxTopArcVertex_mem_wiredArc n)).support)
    (hzBox : z ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)) :
    z = u.val ∨ z = (0, (n : ℤ)) := by
  have hRight : z.1 ≤ (n : ℤ) := by
    rw [mem_latticeRectangle] at hzBox
    have h := hzBox.1.2
    have hmax : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by push_cast; omega
    omega
  have hBottom : -(n : ℤ) ≤ z.2 := by
    rw [mem_latticeRectangle] at hzBox
    exact hzBox.2.1
  have hTop : z.2 ≤ (n : ℤ) := by
    rw [mem_latticeRectangle] at hzBox
    have h := hzBox.2.2
    have hmax : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by push_cast; omega
    omega
  have ha := slitBoxCanonicalReturn_horizontal_bound_local n u huX
  have hstart : ((0 : ℤ), (n : ℤ)) = (slitBoxTopArcVertex n).val := rfl
  have hend : ((u.val.1.toNat : ℤ), -(n : ℤ)) = u.val := by
    apply Prod.ext
    · rw [Int.toNat_of_nonneg huX]
    · exact huY.symm
  have hzNat : z ∈ (slitBoxExteriorReturnWalkNat n u.val.1.toNat n ha (by omega)).val.support := by
    change z ∈ ((slitBoxExteriorReturnWalkNat n u.val.1.toNat n ha (by omega)).val.copy
      hstart hend).support at hz
    simpa only [SimpleGraph.Walk.support_copy] using hz
  unfold slitBoxExteriorReturnWalkNat at hzNat
  dsimp only at hzNat
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hzNat
  rcases hzNat with hz1 | hzRest
  · obtain ⟨hx, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds
      0 (n : ℤ) (n + 1 - n) (by simpa [SimpleGraph.Walk.support_copy] using hz1)
    have : z.2 = (n : ℤ) := by omega
    exact Or.inr (Prod.ext hx this)
  · rcases hzRest with hz2 | hzRest
    · obtain ⟨hy, hlo, hhi⟩ := slitReturnHorizontalRightWalk_support_bounds
        0 (n + 1 : ℤ) (n + 1) (by simpa [SimpleGraph.Walk.support_copy] using hz2)
      omega
    · rcases hzRest with hz3 | hzRest
      · obtain ⟨hx, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds
          (n + 1 : ℤ) (-(n + 1 : ℤ)) (2 * (n + 1)) (by
            simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hz3)
        omega
      · rcases hzRest with hz4 | hz5
        · obtain ⟨hy, hlo, hhi⟩ := slitReturnHorizontalRightWalk_support_bounds
            (u.val.1.toNat : ℤ) (-(n + 1 : ℤ)) (n + 1 - u.val.1.toNat) (by
              simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hz4)
          omega
        · obtain ⟨hx, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds
            (u.val.1.toNat : ℤ) (-(n + 1 : ℤ)) 1 (by
              simpa [SimpleGraph.Walk.support_copy] using hz5)
          have hxa : (u.val.1.toNat : ℤ) = u.val.1 := by
            rw [Int.toNat_of_nonneg huX]
          have hy : z.2 = -(n : ℤ) := by omega
          apply Or.inl
          apply Prod.ext
          · omega
          · exact hy.trans huY.symm

private theorem slitBoxExteriorReturnTop_edges_subset
    (n a k : ℕ) (ha : a ≤ n) (hk : k ≤ n) :
    ∀ e ∈ (slitBoxExteriorReturnWalkNat n a n ha (by omega)).val.edges,
      e ∈ (slitBoxExteriorReturnWalkNat n a k ha hk).val.edges := by
  intro e he
  simp only [slitBoxExteriorReturnWalkNat, SimpleGraph.Walk.edges_copy,
    SimpleGraph.Walk.edges_append, List.mem_append,
    SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he ⊢
  rcases he with h1 | h2 | h3 | h4 | h5
  · have hd : n + 1 - n = 1 := by omega
    rw [hd] at h1
    simp [slitReturnVerticalUpWalk] at h1
    have hrec := slitReturnVerticalUpWalk_edge_mem (0 : ℤ) (k : ℤ)
      (n + 1 - k) (n : ℤ) (by omega) (by omega)
    rw [h1]
    exact Or.inl hrec
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))

theorem slitBoxCanonicalTopReturnWalk_edges_subset_any_arc_return
    (n : ℕ) (u : SlitBoxVertex n) (huY : u.val.2 = -(n : ℤ))
    (huX : 0 ≤ u.val.1) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    ∀ e ∈ (slitBoxCanonicalReturnWalk n u huY huX (slitBoxTopArcVertex n)
      (slitBoxTopArcVertex_mem_wiredArc n)).edges,
      e ∈ (slitBoxCanonicalReturnWalk n u huY huX t ht).edges := by
  intro e he
  have ha := slitBoxCanonicalReturn_horizontal_bound_local n u huX
  have hk := slitBoxCanonicalReturn_vertical_bound_local n t ht
  have htopStart : ((0 : ℤ), (n : ℤ)) = (slitBoxTopArcVertex n).val := rfl
  have htopEnd : ((u.val.1.toNat : ℤ), -(n : ℤ)) = u.val := by
    apply Prod.ext
    · rw [Int.toNat_of_nonneg huX]
    · exact huY.symm
  have hstart : ((0 : ℤ), (t.val.2.toNat : ℤ)) = t.val := by
    have htArc := (mem_slitBoxWiredArc_iff n t).mp ht
    apply Prod.ext
    · exact htArc.1.symm
    · exact Int.toNat_of_nonneg htArc.2.1
  change e ∈ ((slitBoxExteriorReturnWalkNat n u.val.1.toNat n ha (by omega)).val.copy
    htopStart htopEnd).edges at he
  rw [SimpleGraph.Walk.edges_copy] at he
  have hNat := slitBoxExteriorReturnTop_edges_subset n u.val.1.toNat t.val.2.toNat ha hk e he
  change e ∈ ((slitBoxExteriorReturnWalkNat n u.val.1.toNat t.val.2.toNat ha hk).val.copy
    hstart htopEnd).edges
  rw [SimpleGraph.Walk.edges_copy]
  exact hNat

end PottsContinuity.FKC.FiniteFK
