module

public import PottsContinuity.Thm3.RSW.FiniteBoundary

/-! Finite products of increasing events on the exact Boolean finite carrier. -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory
noncomputable section

/-- Finite positive association for arbitrary finite wiring and actual Boolean
events. No conditioning on a mixed increasing/decreasing event is used. -/
theorem finiteBoundaryEventProbability_fkg_finset
    (V : Finset (ℤ × ℤ)) (θ : PD.FK.Parameters)
    (ξ : PD.FK.BoundaryCondition (V:Set (ℤ × ℤ)))
    {ι : Type*} (s : Finset ι)
    (E : ι → ((squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool) → Prop)
    (hE : ∀ j ∈ s, IsUpperSet {ω | E j ω}) :
    (∏ j ∈ s, finiteBoundaryEventProbability V θ ξ (E j)) ≤
      finiteBoundaryEventProbability V θ ξ (fun ω => ∀ j ∈ s, E j ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteBoundaryEventProbability,finiteBoolEvent]
  | @insert j s hjs ih =>
    have hs := ih (fun k hk => hE k (Finset.mem_insert_of_mem hk))
    rw [Finset.prod_insert hjs]
    calc
      _ ≤ finiteBoundaryEventProbability V θ ξ (E j) *
          finiteBoundaryEventProbability V θ ξ (fun ω => ∀ k ∈ s, E k ω) :=
        mul_le_mul_of_nonneg_left hs ENNReal.toReal_nonneg
      _ ≤ finiteBoundaryEventProbability V θ ξ
          (fun ω => E j ω ∧ ∀ k ∈ s, E k ω) :=
        finiteBoundaryEventProbability_fkg V θ ξ _ _
          (hE j (Finset.mem_insert_self _ _))
          (fun _ _ h hω k hk => hE k (Finset.mem_insert_of_mem hk) h (hω k hk))
      _ = _ := by
        congr 1
        funext ω
        simp only [Finset.mem_insert, forall_eq_or_imp]

/-- An actual finite inclusion allows finite FKG local bounds to be multiplied. -/
theorem finiteBoundaryEventProbability_lower_of_finite_gluing
    (V : Finset (ℤ × ℤ)) (θ : PD.FK.Parameters)
    (ξ : PD.FK.BoundaryCondition (V:Set (ℤ × ℤ)))
    {ι : Type*} (s : Finset ι)
    (E : ι → ((squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool) → Prop)
    (H : ((squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool) → Prop)
    (b : ℝ) (hb : 0 ≤ b)
    (hE : ∀ j ∈ s, IsUpperSet {ω | E j ω})
    (hlocal : ∀ j ∈ s, b ≤ finiteBoundaryEventProbability V θ ξ (E j))
    (hglue : ∀ ω, (∀ j ∈ s, E j ω) → H ω) :
    b^s.card ≤ finiteBoundaryEventProbability V θ ξ H := by
  calc
    b^s.card = ∏ _j ∈ s, b := (Finset.prod_const b).symm
    _ ≤ ∏ j ∈ s, finiteBoundaryEventProbability V θ ξ (E j) :=
      Finset.prod_le_prod₀ (fun _ _ => hb) hlocal
    _ ≤ finiteBoundaryEventProbability V θ ξ (fun ω => ∀ j ∈ s, E j ω) :=
      finiteBoundaryEventProbability_fkg_finset V θ ξ s E hE
    _ ≤ _ := measureReal_mono (fun _ h => hglue _ h)

end
end PottsContinuity.RSW
