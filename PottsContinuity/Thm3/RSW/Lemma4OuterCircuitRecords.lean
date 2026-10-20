module

public import PottsContinuity.Thm3.RSW.Lemma4SourceEvents
public import PottsContinuity.Thm3.RSW.StoppedCircuitInteriorComparison

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance lemma4CircuitRecordsEdgeEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _
local instance lemma4CircuitRecordsEdgeFintype (n : ℕ) :
    Fintype (lemma4AmbientGraph n).edgeSet := Fintype.ofFinite _

/-- Source eq10 with a coefficient chosen before scales and stopping records.
All residual graph, boundary partition and event geometry is explicit. -/
theorem selfDual_lemma4_two_annuli_lower_of_circuitRecords (q : Set.Ici (1:ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀
      (reveal : RevealMap (G := (lemma4AmbientGraph n)))
    (_hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (T : Set (StoppingObservationRange reveal))
    (X : Configuration (lemma4AmbientGraph n) → Type*) [_hX : ∀ C₀, Finite (X C₀)]
    (G : (C₀ : Configuration (lemma4AmbientGraph n)) → SimpleGraph (X C₀))
    (f : (C₀ : Configuration (lemma4AmbientGraph n)) → X C₀ ↪ {z : LatticeVertex // z ∈ box (56*n)})
    (hGH : ∀ C₀, (G C₀).map (f C₀) ≤ (lemma4AmbientGraph n))
    (B : (C₀ : Configuration (lemma4AmbientGraph n)) → Set (X C₀))
    (Ein : (C₀ : Configuration (lemma4AmbientGraph n)) → Set (Configuration (G C₀)))
    (_hEin : ∀ C₀, IsUpperSet (Ein C₀))
    (_hremoved : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      reveal C₀ = subgraphRemovedEdges ((G C₀).map (f C₀)) (lemma4AmbientGraph n))
    (_hclosed : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      ∀ ⦃x : X C₀⦄, x ∉ B C₀ → ∀ ⦃y : {z : LatticeVertex // z ∈ box (56*n)}⦄, (lemma4AmbientGraph n).Adj (f C₀ x) y →
        ∃ z : X C₀, f C₀ z = y ∧ (G C₀).Adj x z)
    (_havoid : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      ∀ ⦃x : X C₀⦄, x ∉ B C₀ → f C₀ x ∉ (frozenBoundaryCondition (box (56*n)) 1).boundary)
    (_hwire : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      (BoundaryCondition.wired (B C₀)).partition ≤
        (isolatedExtensionPullbackBoundary (f C₀)
          (frozenBoundary (frozenBoundaryCondition (box (56*n)) 0) (C₀ ∩ subgraphRemovedEdges ((G C₀).map (f C₀)) (lemma4AmbientGraph n)))).partition)
    (_hevent : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      {A | embeddedConfigurationRestriction (G C₀) (lemma4AmbientGraph n) (f C₀) (hGH C₀) A ∈ Ein C₀} = lemma4AnnulusPairEvent n)
    (_hsource : (stoppingObservationMap reveal) ⁻¹' T = lemma4OuterAnnulusEvent n),
      c * annulusProbability (selfDualParameters q) 8 (7*n) ≤
        (measure (lemma4AmbientGraph n) (selfDualParameters q)
          (frozenBoundaryCondition (box (56*n)) 0) (lemma4AnnulusPairEvent n)).toReal := by
  obtain ⟨c,hc,hbound⟩ := selfDual_lemma4_wired_two_annuli_lower_named q
  refine ⟨c,hc,?_⟩
  intro n hn reveal hstable T X hX G f hGH B Ein hEin hremoved hclosed havoid hwire hevent hsource
  have h := stopped_reference_lower_of_circuitRecords (lemma4AmbientGraph n)
    (selfDualParameters q) (frozenBoundaryCondition (box (56*n)) 0)
    (frozenBoundaryCondition (box (56*n)) 1) reveal hstable T X G f hGH B Ein hEin
    (lemma4AnnulusPairEvent n) hremoved hclosed havoid (by
      intro C₀ hC₀
      convert hwire C₀ hC₀ using 1; congr 2
      congr 1
      ext e
      simp only [Finset.mem_inter]) hevent
  rw [hsource,lemma4OuterAnnulusProbability_eq] at h
  exact (mul_le_mul_of_nonneg_right (hbound n hn) (by
    exact ENNReal.toReal_nonneg)).trans h

end
end PottsContinuity.RSW
