module

public import PottsContinuity.Thm3.RSW.FinitePath

/-! Literal original-edge restriction and free comparison for arbitrary actual
Boolean events, including the local annulus events in the P5b chain. -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- Read the ambient state of each embedded original edge. -/
def finiteBoolRestriction (U V : Finset (ℤ × ℤ))
    (f : (U:Set (ℤ × ℤ)) ↪ (V:Set (ℤ × ℤ)))
    (hUV : (squareLattice.induce (U:Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (V:Set (ℤ × ℤ)))
    (ω : (squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool) :
    (squareLattice.induce (U:Set (ℤ × ℤ))).edgeSet → Bool :=
  fun e => ω (embeddedEdgeEmbedding _ _ f hUV e)

/-- Original-edge restriction is monotone in all sampled edge states. -/
theorem finiteBoolRestriction_monotone (U V : Finset (ℤ × ℤ))
    (f : (U:Set (ℤ × ℤ)) ↪ (V:Set (ℤ × ℤ)))
    (hUV : (squareLattice.induce (U:Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (V:Set (ℤ × ℤ))) : Monotone (finiteBoolRestriction U V f hUV) := by
  intro ω η h e
  exact h _

/-- Literal edge restriction agrees exactly with PD's finite-set restriction. -/
theorem finiteBoolRestriction_equiv (U V : Finset (ℤ × ℤ))
    (f : (U:Set (ℤ × ℤ)) ↪ (V:Set (ℤ × ℤ)))
    (hUV : (squareLattice.induce (U:Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (V:Set (ℤ × ℤ)))
    (A : Configuration (squareLattice.induce (V:Set (ℤ × ℤ)))) :
    finiteBoolRestriction U V f hUV ((boolConfigurationEquiv _).symm A) =
      (boolConfigurationEquiv _).symm (embeddedConfigurationRestriction _ _ f hUV A) := by
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [finiteBoolRestriction,← mem_boolConfigurationEquiv,
    Equiv.apply_symm_apply,mem_embeddedConfigurationRestriction]

/-- A local increasing event under the small free law is dominated by the
same original-edge event in the ambient free law. No geometric substitute
or conditioning premise occurs. -/
theorem finite_free_restriction_probability_le (U V : Finset (ℤ × ℤ))
    (f : (U:Set (ℤ × ℤ)) ↪ (V:Set (ℤ × ℤ)))
    (hUV : (squareLattice.induce (U:Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (V:Set (ℤ × ℤ))) (θ : Parameters)
    (E : ((squareLattice.induce (U:Set (ℤ × ℤ))).edgeSet → Bool) → Prop)
    (hE : IsUpperSet {ω | E ω}) :
    finiteBoundaryEventProbability U θ (frozenBoundaryCondition U 0) E ≤
      finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
        (fun ω => E (finiteBoolRestriction U V f hUV ω)) := by
  have h := embedded_free_probability_le _ _ f hUV θ (finiteBoolEvent U E)
    (finiteBoolEvent_isUpperSet U E hE)
  have hevent : {A | embeddedConfigurationRestriction _ _ f hUV A ∈ finiteBoolEvent U E} =
      finiteBoolEvent V (fun ω => E (finiteBoolRestriction U V f hUV ω)) := by
    ext A
    change E ((boolConfigurationEquiv _).symm (embeddedConfigurationRestriction _ _ f hUV A)) ↔
      E (finiteBoolRestriction U V f hUV ((boolConfigurationEquiv _).symm A))
    rw [finiteBoolRestriction_equiv]
  rw [hevent] at h
  have hfree (W : Finset (ℤ × ℤ)) :
      law (squareLattice.induce (W:Set (ℤ × ℤ))) θ (frozenBoundaryCondition W 0) =
        law _ θ (BoundaryCondition.free ∅) :=
    law_eq_of_boundary_partition_eq θ _ _ (by simp [frozenBoundaryCondition,BoundaryCondition.free])
  unfold finiteBoundaryEventProbability PD.FK.measure
  rw [hfree U,hfree V]
  exact h

end
end PottsContinuity.RSW
