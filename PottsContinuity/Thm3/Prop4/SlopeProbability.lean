module

public import PottsContinuity.Thm3.Prop4.SlopeComparison

/-!
# Exact finite-law invariance inside a slope cell

Both the induced vertex carrier and its digital wired arc are unchanged.
The generic congruence theorem compares literal original-edge touch events;
it introduces no virtual connections through the wired block.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Actual root-to-wired-set probability on an arbitrary finite induced lattice domain. -/
noncomputable def finiteWiredTouchProbability (θ : PD.FK.Parameters)
    (V : Finset (ℤ × ℤ)) (root : (V : Set (ℤ × ℤ)))
    (W : Set (V : Set (ℤ × ℤ))) : ℝ :=
  RSW.finiteBoundaryEventProbability V θ (PD.FK.BoundaryCondition.wired W)
    (fun ω => ∃ z ∈ W, (rcOpenGraph V ω).Reachable root z)

/-- Exact domain, root and wired-set agreement gives equality of the actual probabilities. -/
theorem finiteWiredTouchProbability_congr (θ : PD.FK.Parameters)
    (V W : Finset (ℤ × ℤ)) (hVW : V = W)
    (rV : (V : Set (ℤ × ℤ))) (rW : (W : Set (ℤ × ℤ))) (hroot : rV.1 = rW.1)
    (P : Set (V : Set (ℤ × ℤ))) (Q : Set (W : Set (ℤ × ℤ)))
    (hPQ : ∀ v : (V : Set (ℤ × ℤ)), ∀ w : (W : Set (ℤ × ℤ)),
      v.1 = w.1 → (v ∈ P ↔ w ∈ Q)) :
    finiteWiredTouchProbability θ V rV P = finiteWiredTouchProbability θ W rW Q := by
  subst W
  have hr : rV = rW := Subtype.ext hroot
  have hP : P = Q := Set.ext (fun v => hPQ v v rfl)
  rw [hr,hP]

/-- The generic probability specializes exactly to the existing tilted finite law. -/
theorem tiltedTouchProbability_eq_finiteWiredTouchProbability
    (θ : PD.FK.Parameters) (n m : ℕ) (t : ℝ) :
    tiltedTouchProbability θ n m t = finiteWiredTouchProbability θ (tiltedWindow n m t)
      (tiltedWindowOrigin n m t) (tiltedWindowWiredVertices n m t 1) := rfl

/-- Same-cell slopes have identical finite touch probabilities, at every
independent FK parameter and all real q≥1. -/
theorem same_cell_tiltedTouchProbability_eq (θ : PD.FK.Parameters) (n m : ℕ) (t s : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hcell : ∀ b ∈ slopeBreakpoints m, (t<b ↔ s<b) ∧ (t≤b ↔ s≤b)) :
    tiltedTouchProbability θ n m t = tiltedTouchProbability θ n m s := by
  rw [tiltedTouchProbability_eq_finiteWiredTouchProbability,
    tiltedTouchProbability_eq_finiteWiredTouchProbability]
  apply finiteWiredTouchProbability_congr θ _ _ (same_cell_tiltedWindow_eq n m t s ht hs hcell)
    _ _ rfl
  intro v w hvw
  have hx := ((Foundations.mem_box_iff_abs_le m v.1).mp
    ((mem_tiltedWindow n m t v.1).mp v.2).1).1
  change (tiltedTop n t v.1 ∨ (1 : Fin 2) = 1 ∧ v.1 ∈ vertexBoundary (box m)) ↔
    (tiltedTop n s w.1 ∨ (1 : Fin 2) = 1 ∧ w.1 ∈ vertexBoundary (box m))
  rw [← hvw]
  exact or_congr (same_cell_tiltedTop_iff n m t s ht hs hcell v.1 hx) Iff.rfl

/-- Every finite tilted touch probability is exactly represented by a slope
whose positive denominator is at most 2m. No approximation or limit is taken. -/
theorem tiltedTouchProbability_bounded_denominator_representative
    (θ : PD.FK.Parameters) (n m : ℕ) (hm : 1 ≤ m)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ (d : ℕ) (a : ℤ), 1 ≤ d ∧ d ≤ 2*m ∧ (a : ℝ)/(d : ℝ) ∈ Set.Icc (-1 : ℝ) 1 ∧
      tiltedTouchProbability θ n m t = tiltedTouchProbability θ n m ((a : ℝ)/(d : ℝ)) := by
  obtain ⟨d, a, hd, hdm, hs, hcell⟩ := exists_bounded_denominator_same_cell m hm t ht
  exact ⟨d, a, hd, hdm, hs, same_cell_tiltedTouchProbability_eq θ n m t _ ht hs hcell⟩

end PottsContinuity.Thm3.Prop4
