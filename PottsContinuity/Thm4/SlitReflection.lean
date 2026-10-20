module

public import PottsContinuity.Thm4.SlitBottomWitness
public import PottsContinuity.FKC.FiniteFK.SlitBoxHorizontalReflection

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK
noncomputable section

/-- Closed-range version of finite-volume endpoint passage. -/
theorem continuous_le_on_closed_range (f g : Set.Ici (1 : ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ q : Set.Ici (1 : ℝ), q.val < 4 → f q ≤ g q)
    (q : Set.Icc (1 : ℝ) 4) : f ⟨q, q.2.1⟩ ≤ g ⟨q, q.2.1⟩ := by
  by_cases hq : q.val = 4
  · have heq : q = ⟨4, by norm_num⟩ := Subtype.ext hq
    subst q
    exact continuous_le_at_four f g hf hg h
  · exact h ⟨q, q.2.1⟩ (lt_of_le_of_ne q.2.2 hq)

/-- Actual simultaneous arc connection probability for a bottom vertex and
its reflected vertex, with the full literal slit boundary partition. -/
def slitPairConnectionProbability (n : ℕ) (q : Set.Ici (1 : ℝ))
    (u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex n) : ℝ :=
  (measure (PottsContinuity.FKC.FiniteFK.slitBoxGraph n) (selfDualParameters q)
    (fkcBoundaryToPD (PottsContinuity.FKC.FiniteFK.slitBoxBoundary n))
    (PottsContinuity.FKC.FiniteFK.slitBoxWiredArcConnectionEvent n u ∩
      PottsContinuity.FKC.FiniteFK.slitBoxWiredArcConnectionEvent n
        (PottsContinuity.FKC.FiniteFK.slitBoxGraphHorizontalReflectionIso n u))).toReal

theorem continuous_slitPairConnectionProbability (n : ℕ)
    (u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex n) :
    Continuous (fun q => slitPairConnectionProbability n q u) :=
  continuous_selfDual_eventProbability _ _ _

/-- Reflection invariance of the genuine slit law throughout [1,4]. -/
theorem slitArcConnectionProbability_reflection (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
    (u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex n) :
    slitArcConnectionProbability n ⟨q, q.2.1⟩ u =
      slitArcConnectionProbability n ⟨q, q.2.1⟩
        (PottsContinuity.FKC.FiniteFK.slitBoxGraphHorizontalReflectionIso n u) := by
  have heq : ∀ r : Set.Ici (1 : ℝ), r.val < 4 →
      slitArcConnectionProbability n r u =
        slitArcConnectionProbability n r
          (PottsContinuity.FKC.FiniteFK.slitBoxGraphHorizontalReflectionIso n u) := by
    intro r hr
    have h := congrArg ENNReal.toReal
      (PottsContinuity.FKC.FiniteFK.measure_slitBoxWiredArcConnectionEvent_horizontalReflection
        n ⟨r.val, r.property, hr⟩ u)
    erw [fkc_measure_eq] at h
    exact h
  apply le_antisymm
  · exact continuous_le_on_closed_range _ _ (continuous_slitArcConnectionProbability n u)
      (continuous_slitArcConnectionProbability n _) (fun r hr => (heq r hr).le) q
  · exact continuous_le_on_closed_range _ _ (continuous_slitArcConnectionProbability n _)
      (continuous_slitArcConnectionProbability n u) (fun r hr => (heq r hr).ge) q

/-- The FKG square bound for the actual pair event, including q=4. -/
theorem slitPairConnectionProbability_ge_square (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
    (u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex n) :
    slitArcConnectionProbability n ⟨q, q.2.1⟩ u ^ 2 ≤
      slitPairConnectionProbability n ⟨q, q.2.1⟩ u := by
  apply continuous_le_on_closed_range _ _
    ((continuous_slitArcConnectionProbability n u).pow 2)
    (continuous_slitPairConnectionProbability n u) _ q
  intro r hr
  have h := PottsContinuity.FKC.FiniteFK.slitBoxWiredArcConnectionEvent_fkg_square_lower_bound
    n ⟨r.val, r.property, hr⟩ u
  erw [fkc_measure_eq] at h
  exact h

end
end PottsContinuity.Thm4
