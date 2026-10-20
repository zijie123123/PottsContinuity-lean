module

public import PottsContinuity.PlanarTopology.GridSignBalance

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section

/-- The balanced-cell construction works on arbitrary rectangular integer
grids. Clamping a larger square grid retains unit coordinate displacements. -/
theorem rectangle_grid_two_signs_balanced_cell (W H : ℕ)
    (X Y : Fin (W+1) × Fin (H+1) → Prop)
    (hX0 : ∀ v, v.1 = 0 → ¬X v) (hXW : ∀ v, v.1.val = W → X v)
    (hY0 : ∀ v, v.2 = 0 → ¬Y v) (hYH : ∀ v, v.2.val = H → Y v) :
    ∃ v, ¬X v ∧ ¬Y v ∧
      ∃ x, X x ∧ (x.1.val ≤ v.1.val+1 ∧ v.1.val ≤ x.1.val+1) ∧
        (x.2.val ≤ v.2.val+1 ∧ v.2.val ≤ x.2.val+1) ∧
      ∃ y, Y y ∧ (y.1.val ≤ v.1.val+1 ∧ v.1.val ≤ y.1.val+1) ∧
        (y.2.val ≤ v.2.val+1 ∧ v.2.val ≤ y.2.val+1) := by
  let p := max W H
  let f : (Fin 2 → Fin (p+1)) → Fin (W+1) × Fin (H+1) := fun v =>
    (⟨min (v 0).val W,Nat.lt_succ_of_le (min_le_right _ _)⟩,
     ⟨min (v 1).val H,Nat.lt_succ_of_le (min_le_right _ _)⟩)
  have hw : W ≤ p := le_max_left _ _
  have hh : H ≤ p := le_max_right _ _
  have h₀ (v : Fin 2 → Fin (p+1)) (hv : v 0 = 0) : ¬X (f v) := by
    apply hX0
    apply Fin.ext
    simp [f,hv]
  have h₁ (v : Fin 2 → Fin (p+1)) (hv : (v 0).val = p) : X (f v) := by
    apply hXW
    change min (v 0).val W = W
    rw [hv,min_eq_right hw]
  have h₂ (v : Fin 2 → Fin (p+1)) (hv : v 1 = 0) : ¬Y (f v) := by
    apply hY0
    apply Fin.ext
    simp [f,hv]
  have h₃ (v : Fin 2 → Fin (p+1)) (hv : (v 1).val = p) : Y (f v) := by
    apply hYH
    change min (v 1).val H = H
    rw [hv,min_eq_right hh]
  obtain ⟨v,hvX,hvY,x,hx,hcx,y,hy,hcy⟩ :=
    grid_two_signs_balanced_cell p (fun v => X (f v)) (fun v => Y (f v)) h₀ h₁ h₂ h₃
  have hclose (a b : Fin 2 → Fin (p+1))
      (hc : ∀ i : Fin 2, (a i).val ≤ (b i).val+1 ∧ (b i).val ≤ (a i).val+1) :
      ((f a).1.val ≤ (f b).1.val+1 ∧ (f b).1.val ≤ (f a).1.val+1) ∧
      ((f a).2.val ≤ (f b).2.val+1 ∧ (f b).2.val ≤ (f a).2.val+1) := by
    have h0 := hc 0
    have h1 := hc 1
    dsimp [f]
    omega
  exact ⟨f v,hvX,hvY,f x,hx,(hclose x v hcx).1,(hclose x v hcx).2,
    f y,hy,(hclose y v hcy).1,(hclose y v hcy).2⟩

end
end PottsContinuity.PlanarTopology
