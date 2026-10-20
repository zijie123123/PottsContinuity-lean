module

public import PottsContinuity.Thm3.RSW.FinitePathChain
public import PottsContinuity.Thm3.RSW.AnnulusPositivity
public import PottsContinuity.Thm3.RSW.AnnulusChainScale

/-! Genuine finite-scale positivity for the exact buffered P5 event. -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK

/-- The all-open row is an actual horizontal crossing, including width zero. -/
theorem all_true_horizontalCrossing_row (V : Finset (ℤ × ℤ)) (A n : ℕ)
    (hrow : ∀ k : ℕ, k ≤ A → ((k:ℤ),0) ∈ V) :
    horizontalCrossing V 0 (A:ℤ) 0 (n:ℤ) (fun _ => true) := by
  classical
  by_cases hA : A = 0
  · subst A
    let v : (V:Set (ℤ × ℤ)) := ⟨(0,0),hrow 0 le_rfl⟩
    refine ⟨v,v,SimpleGraph.Walk.nil,?_,?_,?_⟩
    · simp [v]
    · simp [v]
    · intro z hz
      simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hz
      subst z
      simp [v]
  let S := latticeRectangle 0 A 0 0
  let u (k : ℕ) : ℤ × ℤ := ((k:ℤ),0)
  have hpaths : ∀ k : ℕ, k < A → (fun _ => true) ∈ finitePathEvent V S (u k) (u (k+1)) := by
    intro k hk
    have hx := hrow k hk.le
    have hy := hrow (k+1) (by omega)
    have hadj : (rcOpenGraph V (fun _ => true)).Adj ⟨u k,hx⟩ ⟨u (k+1),hy⟩ := by
      rw [rcOpenGraph_all_true]
      change |(k:ℤ)-((k+1:ℕ):ℤ)|+|(0:ℤ)-0|=1
      have heq : (k:ℤ)-((k+1:ℕ):ℤ) = -1 := by push_cast; ring
      rw [heq]
      norm_num
    refine ⟨hx,hy,SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil,?_⟩
    intro z hz
    simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
      List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl
    all_goals simp only [S,u,latticeRectangle,Finset.mem_product,Finset.mem_Icc]; omega
  have hp := finitePathEvent_chain V S u (fun _ => true) A (by omega) hpaths
  apply finitePathEvent_implies_horizontalCrossing V S (u 0) (u A) 0 A 0 n
    (by omega) le_rfl le_rfl (fun z hz => ?_) (fun _ => true) hp
  simp only [S,latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hz
  change 0 ≤ z.2 ∧ z.2 ≤ n
  omega

/-- The exact frozen P5 probability is positive at every positive scale and
real positive aspect, for all interior FK parameters and real q≥1. -/
theorem bufferedCrossingProbability_pos (θ : Parameters) (α : ℝ) (hα : 0 < α)
    (n : ℕ) (hn : 1 ≤ n) : 0 < bufferedCrossingProbability θ.toP θ.toQ α n := by
  let V := latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ))
  have hfloor0 : (0:ℤ) ≤ ⌊α*(n:ℝ)⌋ := Int.floor_nonneg.mpr (mul_nonneg hα.le (Nat.cast_nonneg n))
  let A := (⌊α*(n:ℝ)⌋).toNat
  have hA : (A:ℤ) = ⌊α*(n:ℝ)⌋ := Int.toNat_of_nonneg hfloor0
  have hrow : ∀ k : ℕ, k ≤ A → ((k:ℤ),0) ∈ V := by
    intro k hk
    have hkR : (k:ℤ) ≤ A := by exact_mod_cast hk
    simp only [V,latticeRectangle,Finset.mem_product,Finset.mem_Icc,buffered_right_floor_eq]
    omega
  have hopen := all_true_horizontalCrossing_row V A n hrow
  rw [hA] at hopen
  have hpos := (finiteBoundaryEventProbability_pos_iff V θ (frozenBoundaryCondition V 0)
    (horizontalCrossing V 0 ⌊α*(n:ℝ)⌋ 0 n)).mpr ⟨fun _ => true,hopen⟩
  rw [finiteBoundaryEventProbability_frozen] at hpos
  exact hpos

end PottsContinuity.RSW
