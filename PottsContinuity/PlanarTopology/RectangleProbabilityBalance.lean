module

public import PottsContinuity.PlanarTopology.RectangleGridSignBalance

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section

/-- Weak opposite boundary comparisons give a balanced rectangle-grid anchor
and reverse-comparison witnesses within one in each coordinate. Ties are
resolved toward the top and right boundary in the Sperner labelling. -/
theorem rectangle_probability_profiles_balanced_cell (W H : ℕ) (hW : 0 < W) (hH : 0 < H)
    (L R B T : Fin (W+1) × Fin (H+1) → ℝ)
    (hL : ∀ v, v.1 = 0 → R v ≤ L v) (hR : ∀ v, v.1.val = W → L v ≤ R v)
    (hB : ∀ v, v.2 = 0 → T v ≤ B v) (hT : ∀ v, v.2.val = H → B v ≤ T v) :
    ∃ v, R v ≤ L v ∧ T v ≤ B v ∧
      ∃ x, L x ≤ R x ∧ (x.1.val ≤ v.1.val+1 ∧ v.1.val ≤ x.1.val+1) ∧
        (x.2.val ≤ v.2.val+1 ∧ v.2.val ≤ x.2.val+1) ∧
      ∃ y, B y ≤ T y ∧ (y.1.val ≤ v.1.val+1 ∧ v.1.val ≤ y.1.val+1) ∧
        (y.2.val ≤ v.2.val+1 ∧ v.2.val ≤ y.2.val+1) := by
  let X := fun v => L v < R v ∨ (v.1.val = W ∧ L v ≤ R v)
  let Y := fun v => B v < T v ∨ (v.2.val = H ∧ B v ≤ T v)
  have hX0 (v : Fin (W+1) × Fin (H+1)) (hv : v.1 = 0) : ¬X v := by
    have h := hL v hv
    have hz : v.1.val = 0 := congrArg Fin.val hv
    rintro (hx | ⟨hvw,_⟩)
    · exact (not_lt_of_ge h) hx
    · omega
  have hXW (v : Fin (W+1) × Fin (H+1)) (hv : v.1.val = W) : X v :=
    Or.inr ⟨hv,hR v hv⟩
  have hY0 (v : Fin (W+1) × Fin (H+1)) (hv : v.2 = 0) : ¬Y v := by
    have h := hB v hv
    have hz : v.2.val = 0 := congrArg Fin.val hv
    rintro (hy | ⟨hvh,_⟩)
    · exact (not_lt_of_ge h) hy
    · omega
  have hYH (v : Fin (W+1) × Fin (H+1)) (hv : v.2.val = H) : Y v :=
    Or.inr ⟨hv,hT v hv⟩
  obtain ⟨v,hvX,hvY,x,hx,hcx,hcy,y,hy,hdx,hdy⟩ :=
    rectangle_grid_two_signs_balanced_cell W H X Y hX0 hXW hY0 hYH
  have hvL : R v ≤ L v := le_of_not_gt (fun h => hvX (Or.inl h))
  have hvB : T v ≤ B v := le_of_not_gt (fun h => hvY (Or.inl h))
  have hxR : L x ≤ R x := hx.elim le_of_lt (fun h => h.2)
  have hyT : B y ≤ T y := hy.elim le_of_lt (fun h => h.2)
  exact ⟨v,hvL,hvB,x,hxR,hcx,hcy,y,hyT,hdx,hdy⟩

end
end PottsContinuity.PlanarTopology
