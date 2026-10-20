module

public import PottsContinuity.Thm3.RSW.OneArm
public import PottsContinuity.PD.FK.IncreasingEvents
public import PottsContinuity.PD.FK.Events

/-!
# Finite mixed-boundary probabilities on the frozen Boolean carrier

General boundary partitions modify FK weights only. Events are transported by
`boolConfigurationEquiv`, so wired vertices do not create virtual open paths.
This module supplies finite-law infrastructure, not the mixed-square RSW bound.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.RSW

/-- A frozen Boolean event, read on PD's finite-set configuration carrier. -/
def finiteBoolEvent (V : Finset (ℤ × ℤ))
    (E : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop) :
    Set (PD.FK.Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :=
  {A | E ((PD.FK.boolConfigurationEquiv _).symm A)}

/-- The actual finite FK probability with an arbitrary boundary partition,
expressed on the frozen Boolean configuration carrier. -/
noncomputable def finiteBoundaryEventProbability (V : Finset (ℤ × ℤ))
    (θ : PD.FK.Parameters) (ξ : PD.FK.BoundaryCondition (V : Set (ℤ × ℤ)))
    (E : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop) : ℝ :=
  (PD.FK.measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ ξ
    (finiteBoolEvent V E)).toReal

/-- Transport of arbitrary events agrees exactly with frozen free/wired
finite probabilities. The boundary convention is the PD frozen convention,
which Foundations.Bridges identifies with the frozen one. -/
theorem finiteBoundaryEventProbability_frozen (V : Finset (ℤ × ℤ))
    (θ : PD.FK.Parameters) (i : Fin 2)
    (E : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop) :
    finiteBoundaryEventProbability V θ (PD.FK.frozenBoundaryCondition V i) E =
      rcEventProb V θ.toP θ.toQ i E := by
  classical
  unfold finiteBoundaryEventProbability
  rw [PD.FK.measure_toReal_eq_indicator_sum]
  symm
  unfold rcEventProb
  refine Finset.sum_bij (fun ω _ => PD.FK.boolConfigurationEquiv _ ω) ?_ ?_ ?_ ?_
  · intro ω _
    simp only [Finset.mem_univ]
  · intro ω _ η _ h
    exact (PD.FK.boolConfigurationEquiv _).injective h
  · intro A _
    refine ⟨(PD.FK.boolConfigurationEquiv _).symm A, ?_,
      (PD.FK.boolConfigurationEquiv _).apply_symm_apply A⟩
    simp only [Finset.mem_univ]
  intro ω _
  have hprob := PD.FK.configurationProbability_eq_rcProb θ V i ω
  rw [← Foundations.rcProb_eq_PD] at hprob
  simp only [finiteBoolEvent, Set.indicator, Set.mem_ofPred_eq,
    Equiv.symm_apply_apply]
  by_cases hE : E ω
  · simp only [hE, ite_true, mul_one]
    exact hprob.symm
  · simp only [hE, ite_false, mul_zero]

/-- An arbitrary nonempty Boolean event has positive probability under every
finite boundary partition at interior FK parameters. -/
theorem finiteBoundaryEventProbability_pos_iff (V : Finset (ℤ × ℤ))
    (θ : PD.FK.Parameters) (ξ : PD.FK.BoundaryCondition (V : Set (ℤ × ℤ)))
    (E : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop) :
    0 < finiteBoundaryEventProbability V θ ξ E ↔ ∃ ω, E ω := by
  rw [finiteBoundaryEventProbability, ENNReal.toReal_pos_iff]
  have hfinite : PD.FK.measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ ξ
      (finiteBoolEvent V E) < ⊤ := measure_lt_top _ _
  rw [and_iff_left hfinite, PD.FK.measure_pos_iff]
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨(PD.FK.boolConfigurationEquiv _).symm A, hA⟩
  · rintro ⟨ω, hω⟩
    refine ⟨PD.FK.boolConfigurationEquiv _ ω, ?_⟩
    simpa only [finiteBoolEvent, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using hω

/-- The inverse transport also preserves the order. -/
theorem boolConfigurationEquiv_symm_mono (V : Finset (ℤ × ℤ)) :
    Monotone (PD.FK.boolConfigurationEquiv
      (squareLattice.induce (V : Set (ℤ × ℤ)))).symm := by
  intro A B h e
  apply Bool.le_iff_imp.mpr
  intro he
  have hA : e ∈ A := by
    simpa only [PD.FK.mem_boolConfigurationEquiv, Equiv.apply_symm_apply] using
      (PD.FK.mem_boolConfigurationEquiv _
        ((PD.FK.boolConfigurationEquiv _).symm A) e).mpr he
  have hB := h hA
  simpa only [PD.FK.mem_boolConfigurationEquiv, Equiv.apply_symm_apply] using
    (PD.FK.mem_boolConfigurationEquiv _
      ((PD.FK.boolConfigurationEquiv _).symm B) e).mp
      (by simpa only [Equiv.apply_symm_apply] using hB)

/-- An increasing Boolean event remains increasing on the FK carrier. -/
theorem finiteBoolEvent_isUpperSet (V : Finset (ℤ × ℤ))
    (E : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop)
    (hE : IsUpperSet {ω | E ω}) : IsUpperSet (finiteBoolEvent V E) := by
  intro A B h hA
  exact hE (boolConfigurationEquiv_symm_mono V h) hA

/-- Finite FKG for two actual increasing Boolean events under arbitrary wiring. -/
theorem finiteBoundaryEventProbability_fkg (V : Finset (ℤ × ℤ))
    (θ : PD.FK.Parameters) (ξ : PD.FK.BoundaryCondition (V : Set (ℤ × ℤ)))
    (E F : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop)
    (hE : IsUpperSet {ω | E ω}) (hF : IsUpperSet {ω | F ω}) :
    finiteBoundaryEventProbability V θ ξ E * finiteBoundaryEventProbability V θ ξ F ≤
      finiteBoundaryEventProbability V θ ξ (fun ω => E ω ∧ F ω) := by
  exact PD.FK.measure_positive_association θ ξ (finiteBoolEvent V E) (finiteBoolEvent V F)
    (finiteBoolEvent_isUpperSet V E hE) (finiteBoolEvent_isUpperSet V F hF)

/-- Increasing open-edge states enlarge the frozen actual open graph. -/
theorem rcOpenGraph_mono (V : Finset (ℤ × ℤ))
    {ω η : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool} (h : ω ≤ η) :
    rcOpenGraph V ω ≤ rcOpenGraph V η := by
  apply SimpleGraph.fromEdgeSet_mono
  rintro e ⟨he, hω⟩
  refine ⟨he, ?_⟩
  have hh := h ⟨e, he⟩
  rw [hω] at hh
  exact (Bool.le_iff_imp.mp hh) rfl

/-- Frozen horizontal crossings are increasing, preserving the same path and
its rectangle support when extra edges are opened. -/
theorem horizontalCrossing_isUpperSet (V : Finset (ℤ × ℤ)) (a b c d : ℤ) :
    IsUpperSet {ω | horizontalCrossing V a b c d ω} := by
  intro ω η h hω
  obtain ⟨x, y, w, hx, hy, hw⟩ := hω
  refine ⟨x, y, w.mapLe (rcOpenGraph_mono V h), hx, hy, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
  exact hw v hv

end PottsContinuity.RSW
