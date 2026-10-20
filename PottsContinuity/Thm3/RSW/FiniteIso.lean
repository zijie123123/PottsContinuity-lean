module

public import PottsContinuity.Thm3.RSW.FinitePath
public import PottsContinuity.PD.FK.BoxTranslation

/-! Free finite laws and actual Boolean paths under graph isomorphisms. -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Exact free event transport; arbitrary events are allowed, with no upper
bound on the cluster weight. -/
theorem free_probability_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (θ : Parameters) (e : G ≃g H)
    (S : Set (Configuration H)) :
    (PD.FK.measure H θ (BoundaryCondition.free ∅) S).toReal =
      (PD.FK.measure G θ (BoundaryCondition.free ∅)
        {A | configurationIso e A ∈ S}).toReal := by
  have hlaw := law_configurationIso_map θ e (BoundaryCondition.free ∅)
  rw [boundaryConditionIso_free_empty] at hlaw
  unfold PD.FK.measure
  rw [← hlaw,PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top]
  rfl

/-- Relabel a finite Boolean configuration by the literal graph isomorphism. -/
def finiteBoolIso (V W : Finset (ℤ × ℤ))
    (e : (squareLattice.induce (V:Set (ℤ × ℤ))) ≃g
      squareLattice.induce (W:Set (ℤ × ℤ))) :
    ((squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool) ≃
      ((squareLattice.induce (W:Set (ℤ × ℤ))).edgeSet → Bool) :=
  (boolConfigurationEquiv _).trans
    ((configurationIso e).trans (boolConfigurationEquiv _).symm)

/-- Its original-edge open graphs are genuinely isomorphic. -/
def finiteBoolOpenIso (V W : Finset (ℤ × ℤ))
    (e : (squareLattice.induce (V:Set (ℤ × ℤ))) ≃g
      squareLattice.induce (W:Set (ℤ × ℤ)))
    (ω : (squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool) :
    rcOpenGraph V ω ≃g rcOpenGraph W (finiteBoolIso V W e ω) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro u v
    change (rcOpenGraph W ((boolConfigurationEquiv _).symm
      (configurationIso e (boolConfigurationEquiv _ ω)))).Adj (e u) (e v) ↔
        (rcOpenGraph V ω).Adj u v
    have hleft := rcOpenGraph_boolConfigurationEquiv_symm V (boolConfigurationEquiv _ ω)
    simp only [Equiv.symm_apply_apply] at hleft
    rw [rcOpenGraph_boolConfigurationEquiv_symm,hleft]
    exact (openGraphIso e (boolConfigurationEquiv _ ω)).map_rel_iff

/-- The exact Boolean free probability transported by the actual relabeling. -/
theorem finite_free_probability_iso (V W : Finset (ℤ × ℤ))
    (e : (squareLattice.induce (V:Set (ℤ × ℤ))) ≃g
      squareLattice.induce (W:Set (ℤ × ℤ))) (θ : Parameters)
    (E : ((squareLattice.induce (W:Set (ℤ × ℤ))).edgeSet → Bool) → Prop) :
    finiteBoundaryEventProbability W θ (frozenBoundaryCondition W 0) E =
      finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
        (fun ω => E (finiteBoolIso V W e ω)) := by
  unfold finiteBoundaryEventProbability
  have hfree (U : Finset (ℤ × ℤ)) :
      law (squareLattice.induce (U:Set (ℤ × ℤ))) θ (frozenBoundaryCondition U 0) =
        law _ θ (BoundaryCondition.free ∅) :=
    law_eq_of_boundary_partition_eq θ _ _ (by simp [frozenBoundaryCondition,BoundaryCondition.free])
  unfold PD.FK.measure
  rw [hfree W,hfree V]
  have hE : finiteBoolEvent V (fun ω => E (finiteBoolIso V W e ω)) =
      {A | configurationIso e A ∈ finiteBoolEvent W E} := by
    ext A
    simp only [finiteBoolEvent,finiteBoolIso,Set.mem_ofPred_eq,
      Equiv.trans_apply,Equiv.apply_symm_apply]
  rw [hE]
  exact free_probability_iso θ e (finiteBoolEvent W E)

end
end PottsContinuity.RSW
