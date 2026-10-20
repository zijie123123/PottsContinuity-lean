module

public import PottsContinuity.Thm3.RSW.Lemma4WiredAnnuli

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section

/-- The actual source ambient graph at every scale, including scale zero. -/
abbrev lemma4AmbientGraph (n : ℕ) :=
  squareLattice.induce (box (56*n) : Set LatticeVertex)

/-- The two source annulus circuits at centers z-plus and z-minus, on their
original finite sampled bonds and with genuine Jordan enclosure. -/
def lemma4AnnulusPairEvent (n : ℕ) : Set (Configuration (lemma4AmbientGraph n)) :=
  finiteBoolEvent (box (56*n))
    (fun ω => ω ∈ annulusCircuitEvent (box (56*n)) (5*(n:ℤ),0) n ∧
      ω ∈ annulusCircuitEvent (box (56*n)) (-5*(n:ℤ),0) n)

/-- The actual larger annulus circuit conditioning event in source eq9. -/
def lemma4OuterAnnulusEvent (n : ℕ) : Set (Configuration (lemma4AmbientGraph n)) :=
  finiteBoolEvent (box (56*n)) (fun ω => ω ∈ annulusCircuitEvent (box (56*n)) (0,0) (7*n))

/-- Opening bonds preserves the original two sampled annulus witnesses. -/
theorem lemma4AnnulusPairEvent_isUpperSet (n : ℕ) : IsUpperSet (lemma4AnnulusPairEvent n) :=
  finiteBoolEvent_isUpperSet _ _ (fun _ _ h hA =>
    ⟨annulusCircuitEvent_isUpperSet _ _ _ h hA.1,annulusCircuitEvent_isUpperSet _ _ _ h hA.2⟩)

/-- The source larger-annulus mass is precisely a-seven-n in its actual free
box, with no change of finite law or source event. -/
theorem lemma4OuterAnnulusProbability_eq (θ : Parameters) (n : ℕ) :
    (measure (lemma4AmbientGraph n) θ (frozenBoundaryCondition (box (56*n)) 0)
      (lemma4OuterAnnulusEvent n)).toReal = annulusProbability θ 8 (7*n) := by
  simp only [annulusProbability,finiteBoundaryEventProbability,lemma4OuterAnnulusEvent,
    lemma4AmbientGraph]
  rw [show 8*(7*n) = 56*n by omega]

/-- The uniform wired source two-annulus coefficient, before all positive
scales and independently of any chosen source exploration records. -/
theorem selfDual_lemma4_wired_two_annuli_lower_named (q : Set.Ici (1:ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ (measure (lemma4AmbientGraph n) (selfDualParameters q)
        (frozenBoundaryCondition (box (56*n)) 1) (lemma4AnnulusPairEvent n)).toReal := by
  simpa only [finiteBoundaryEventProbability,lemma4AnnulusPairEvent,lemma4AmbientGraph] using
    selfDual_lemma4_wired_two_annuli_lower q

end
end PottsContinuity.RSW
