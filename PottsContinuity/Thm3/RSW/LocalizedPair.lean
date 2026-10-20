module

public import PottsContinuity.Thm3.RSW.SquareSymmetry

/-!
# The localized pair bound of Lemma 5

This is the free-boundary estimate underlying source eq. (17), proved by
exterior-seed cluster exploration rather than outermost dual circuits.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- Translation and coordinate exchange send the anchor to the left-side
vertex with the first indexed height. -/
theorem localizationSquareIso_anchor {m : ℕ} (t : SquareLocalizationIndex m) :
    (localizationSquareIso t ⟨t.1.val, (localization_endpoints_mem t).1⟩).val =
      (0, (t.2.2.1.val : ℤ)) := by
  obtain ⟨a, o, i, j⟩ := t
  cases o <;> apply Prod.ext <;>
    simp [localizationSquareIso, localizationCorner]

/-- The opposite indexed endpoint maps to the right-side vertex with the
second indexed height. -/
theorem localizationSquareIso_partner {m : ℕ} (t : SquareLocalizationIndex m) :
    (localizationSquareIso t ⟨localizationPartner t, (localization_endpoints_mem t).2⟩).val =
      ((m : ℤ), (t.2.2.2.val : ℤ)) := by
  obtain ⟨a, o, i, j⟩ := t
  cases o <;> apply Prod.ext <;>
    simp [localizationSquareIso, localizationCorner, localizationPartner]

/-- An indexed free square pair has precisely the corresponding standard
square-pair probability, for every independent interior edge parameter and q≥1. -/
theorem localizationSquare_pair_probability (θ : Parameters) {m : ℕ}
    (t : SquareLocalizationIndex m) :
    finiteBoundaryEventProbability (localizationSquare t) θ
      (frozenBoundaryCondition (localizationSquare t) 0)
      (fun ω => ω ∈ finiteConnectionEvent (localizationSquare t)
        t.1.val (localizationPartner t)) =
      squarePairProbability θ m t.2.2.1 t.2.2.2 := by
  let a := (⟨t.1.val, (localization_endpoints_mem t).1⟩ :
    (localizationSquare t : Set (ℤ × ℤ)))
  let b := (⟨localizationPartner t, (localization_endpoints_mem t).2⟩ :
    (localizationSquare t : Set (ℤ × ℤ)))
  have ha := localizationSquareIso_anchor t
  have hb := localizationSquareIso_partner t
  have hai : (0, (t.2.2.1.val : ℤ)) ∈ latticeRectangle 0 m 0 m := by
    rw [← ha]
    exact (localizationSquareIso t a).property
  have hbi : ((m : ℤ), (t.2.2.2.val : ℤ)) ∈ latticeRectangle 0 m 0 m := by
    rw [← hb]
    exact (localizationSquareIso t b).property
  have haeq : localizationSquareIso t a = ⟨(0, (t.2.2.1.val : ℤ)), hai⟩ := Subtype.ext ha
  have hbeq : localizationSquareIso t b = ⟨((m : ℤ), (t.2.2.2.val : ℤ)), hbi⟩ := Subtype.ext hb
  unfold squarePairProbability
  rw [finite_free_connection_probability_eq θ _ _ _ (localization_endpoints_mem t).1
      (localization_endpoints_mem t).2,
    finite_free_connection_probability_eq θ _ _ _ hai hbi]
  have h := free_connection_probability_eq_of_iso θ (localizationSquareIso t) a b
  rw [haeq, hbeq] at h
  exact h

/-- The exact indexed version of the free localized-pair bound eq. (17).
There is no exterior-domain, mixed-RSW or exploration premise. -/
theorem finite_localizedPair_probability_le_max (θ : Parameters)
    (V : Finset (ℤ × ℤ)) {m : ℕ} (t : SquareLocalizationIndex m) :
    finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
      (fun ω => ω ∈ finiteConfinedConnectionEvent V (localizationSquare t)
        t.1.val (localizationPartner t)) ≤ maxSquarePairProbability θ m := by
  classical
  by_cases ha : t.1.val ∈ V
  · by_cases hb : localizationPartner t ∈ V
    · calc
        _ ≤ finiteBoundaryEventProbability (localizationSquare t) θ
            (frozenBoundaryCondition (localizationSquare t) 0)
            (fun ω => ω ∈ finiteConnectionEvent (localizationSquare t)
              t.1.val (localizationPartner t)) :=
          finite_free_confinedConnection_probability_le θ V (localizationSquare t)
            t.1.val (localizationPartner t) ha hb
            (localization_endpoints_mem t).1 (localization_endpoints_mem t).2
        _ = squarePairProbability θ m t.2.2.1 t.2.2.2 := localizationSquare_pair_probability θ t
        _ ≤ _ := squarePairProbability_le_max θ m _ _
    · have hE : finiteBoolEvent V (fun ω => ω ∈ finiteConfinedConnectionEvent V
          (localizationSquare t) t.1.val (localizationPartner t)) = ∅ := by
        ext A
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, h, _⟩, _⟩
        exact hb h
      unfold finiteBoundaryEventProbability
      rw [hE, measure_empty, ENNReal.toReal_zero]
      exact maxSquarePairProbability_nonneg θ m
  · have hE : finiteBoolEvent V (fun ω => ω ∈ finiteConfinedConnectionEvent V
        (localizationSquare t) t.1.val (localizationPartner t)) = ∅ := by
      ext A
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨h, _, _⟩, _⟩
      exact ha h
    unfold finiteBoundaryEventProbability
    rw [hE, measure_empty, ENNReal.toReal_zero]
    exact maxSquarePairProbability_nonneg θ m

end
end PottsContinuity.RSW
