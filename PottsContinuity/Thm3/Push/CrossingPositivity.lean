module

public import PottsContinuity.Thm3.Push.RectangleGeometry
public import PottsContinuity.Thm3.RSW.AnnulusPositivity

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
noncomputable section

/-- The all-open sample has a literal horizontal walk along the free bottom
row. This includes zero-width rectangles and scale zero. -/
theorem topWiredCrossing_all_true (k ℓ : ℝ) (n : ℕ)
    (hk : 0 ≤ k) (hℓ : 0 ≤ ℓ) :
    horizontalCrossing (topWiredRectangle k ℓ n) (-⌊k*n⌋) ⌊k*n⌋ 0 n (fun _ => true) := by
  let a := -⌊k*n⌋
  let b := ⌊k*n⌋
  have hb : 0 ≤ b := Int.floor_nonneg.mpr (mul_nonneg hk (Nat.cast_nonneg n))
  have hh : 0 ≤ ⌊ℓ*n⌋ := Int.floor_nonneg.mpr (mul_nonneg hℓ (Nat.cast_nonneg n))
  let R := PottsContinuity.latticeRectangle a b 0 0
  let row (i : ℕ) (hi : i ≤ (b-a).toNat) : (R : Set (ℤ × ℤ)) :=
    ⟨(a+i,0), by
      change (a+(i : ℤ), (0 : ℤ)) ∈ R
      simp only [R, PottsContinuity.latticeRectangle, Finset.mem_product, Finset.mem_Icc]
      have hba : a ≤ b := by dsimp [a, b] at *; omega
      have hcast : ((b-a).toNat : ℤ) = b-a := Int.toNat_of_nonneg (by omega)
      exact ⟨⟨by omega, by omega⟩, le_rfl, le_rfl⟩⟩
  let G := squareLattice.induce (R : Set (ℤ × ℤ))
  have hreach : ∀ i (hi : i ≤ (b-a).toNat), G.Reachable (row 0 (by omega)) (row i hi) := by
    intro i
    induction i with
    | zero => intro hi; exact SimpleGraph.Reachable.rfl
    | succ i ih =>
      intro hi
      have hi' : i ≤ (b-a).toNat := by omega
      have hadj : G.Adj (row i hi') (row (i+1) hi) := by
        change |(a+(i : ℤ))-(a+((i+1 : ℕ) : ℤ))| + |(0 : ℤ)-0| = 1
        push_cast
        have heq : a+(i : ℤ)-(a+(i+1)) = -1 := by ring
        rw [heq]
        norm_num
      exact (ih hi').trans hadj.reachable
  have hRV : (R : Set (ℤ × ℤ)) ⊆ (topWiredRectangle k ℓ n : Set (ℤ × ℤ)) := by
    intro z hz
    change z ∈ R at hz
    have hz' : a ≤ z.1 ∧ z.1 ≤ b ∧ z.2=0 := by
      simp only [R, PottsContinuity.latticeRectangle, Finset.mem_product,
        Finset.mem_Icc] at hz
      exact ⟨hz.1.1, hz.1.2, by omega⟩
    exact (mem_topWiredRectangle_iff k ℓ n z).mpr
      ⟨hz'.1, hz'.2.1, by omega, by omega⟩
  let j := squareLattice.induceHomOfLE hRV
  let jo : G →g rcOpenGraph (topWiredRectangle k ℓ n) (fun _ => true) := {
    toFun := j
    map_rel' := by
      intro u v huv
      rw [rcOpenGraph_all_true]
      exact j.map_rel_iff'.mpr huv
  }
  obtain ⟨w⟩ := hreach (b-a).toNat le_rfl
  rw [horizontalCrossing]
  refine ⟨jo (row 0 (by omega)), jo (row (b-a).toNat le_rfl), w.map jo, ?_, ?_, ?_⟩
  · change (a+(0 : ℤ),0) ∈ ({a} : Set ℤ) ×ˢ Set.Icc 0 (n : ℤ)
    simp
  · change (a+((b-a).toNat : ℤ),0) ∈ ({b} : Set ℤ) ×ˢ Set.Icc 0 (n : ℤ)
    rw [Int.toNat_of_nonneg (by dsimp [a,b]; omega)]
    simp
  · intro z hz
    have hzR : z.val ∈ R := by
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
      exact t.property
    simp only [R, PottsContinuity.latticeRectangle, Finset.mem_product,
      Finset.mem_Icc] at hzR
    exact ⟨hzR.1, by omega, by omega⟩

/-- Fixed-scale positivity under arbitrary interior FK parameters. This
supplies finite exceptional scales; it does not assert a uniform RSW bound. -/
theorem topWiredCrossing_probability_pos (θ : Parameters) (k ℓ : ℝ) (n : ℕ)
    (hk : 0 ≤ k) (hℓ : 0 ≤ ℓ) :
    0 < finiteBoundaryEventProbability (topWiredRectangle k ℓ n) θ
      (topWiredRectangleBoundary k ℓ n)
      (horizontalCrossing (topWiredRectangle k ℓ n) (-⌊k*n⌋) ⌊k*n⌋ 0 n) :=
  (finiteBoundaryEventProbability_pos_iff _ θ _ _).mpr
    ⟨fun _ => true, topWiredCrossing_all_true k ℓ n hk hℓ⟩

end
end PottsContinuity.Push
