module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ResidualPrimalWindows

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Exploration Push RSW
noncomputable section
local instance routeSevenNativePrimalEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- Read the actual unqueried sample on its edge-defined carrier. -/
def nativeUnqueriedRead {V : Type*} [Finite V] (G : SimpleGraph V)
    (R : Configuration G) (A : Configuration G) : Configuration (edgeRestriction G R) :=
  (edgeRestrictionConfigurationEquiv G R).symm (configurationSplitEquiv G R A).1

theorem nativeUnqueriedRead_original_edges {V : Type*} [Finite V] (G : SimpleGraph V)
    (R A : Configuration G) :
    (edgeRestrictionConfigurationEquiv G R (nativeUnqueriedRead G R A)).val=A \ R := by
  rw [nativeUnqueriedRead,Equiv.apply_symm_apply]
  rfl

/-- The stopped law is FK on precisely the native primal carrier, with no
restored variables or carrier-identification premise. -/
theorem actual_record_native_primal_law {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters) (ξ : BoundaryCondition V)
    (reveal : RevealMap (G := G))
    (hstable : ∀ A B, B ∩ reveal A=A ∩ reveal A → reveal B=reveal A)
    (record : Configuration G) :
    ((law G θ ξ).filter (revealRecordEvent reveal record) (by
      rw [revealRecordEvent_eq_frozenStateEvent reveal hstable record]
      exact frozenStateEvent_support θ ξ _ (revealRecordConfiguration reveal record))).map
        (nativeUnqueriedRead G (reveal record)) =
      law (edgeRestriction G (reveal record)) θ
        (frozenBoundary ξ (revealRecordConfiguration reveal record).val) := by
  have h := congrArg (fun ρ => ρ.map (edgeRestrictionConfigurationEquiv G (reveal record)).symm)
    (law_filter_revealRecord_map_remaining θ ξ reveal hstable record)
  rw [PMF.map_comp] at h
  change _ = _ at h
  rw [← law_edgeRestriction_map,PMF.map_comp] at h
  simp only [Function.comp_def,Equiv.symm_apply_apply] at h
  change _ = PMF.map id (law (edgeRestriction G (reveal record)) θ
    (frozenBoundary ξ (revealRecordConfiguration reveal record).val)) at h
  rw [PMF.map_id] at h
  exact h

/-- The exact source record, including both source annuli, supplies the
native primal law at every admissible self-dual parameter. -/
theorem lemma4_actual_record_native_primal_law
    (n : ℕ) (q : Set.Ici (1:ℝ)) (record : Configuration (lemma4AmbientGraph n)) :
    ((law (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (lemma4JointSourceReveal n) record) (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (lemma4JointSourceReveal_stable n) record]
        exact frozenStateEvent_support (selfDualParameters q) (BoundaryCondition.free ∅)
          _ (revealRecordConfiguration _ record))).map
        (nativeUnqueriedRead (lemma4AmbientGraph n) (lemma4JointSourceReveal n record)) =
      law (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n record))
        (selfDualParameters q) (frozenBoundary (BoundaryCondition.free ∅)
          (revealRecordConfiguration (lemma4JointSourceReveal n) record).val) :=
  actual_record_native_primal_law _ _ _ _ (lemma4JointSourceReveal_stable n) record

/-- Event identification uses the native read only. -/
theorem nativePrimalWindowNoncrossing_unqueriedRead_iff (V : Finset (ℤ × ℤ))
    (R A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) (l r b t : ℤ) :
    nativeUnqueriedRead _ R A ∈ nativePrimalWindowNoncrossing V R l r b t ↔
      A ∈ residualPrimalWindowNoncrossing V R l r b t := by
  change (edgeRestrictionConfigurationEquiv _ R _).val ∈ primalWindowNoncrossing V Set.univ l r b t ↔
    A \ R ∈ primalWindowNoncrossing V Set.univ l r b t
  rw [nativeUnqueriedRead_original_edges]

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
