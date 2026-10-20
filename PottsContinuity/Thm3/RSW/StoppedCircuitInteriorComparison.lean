module

public import PottsContinuity.Thm3.RSW.FrozenCircuitInteriorComparison
public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance stoppedCircuitComparisonEdgeEq {Y : Type*} (H : SimpleGraph Y) :
    DecidableEq H.edgeSet := Classical.decEq _
local instance stoppedCircuitComparisonEdgeFintype {Y : Type*} [Finite Y] (H : SimpleGraph Y) :
    Fintype H.edgeSet := Fintype.ofFinite _

/-- Actual circuit records give a reference-law lower estimate after averaging.
The residual carrier and graph may vary with the record, and observed circuit
edges may be absent from that graph. All boundary and event geometry is explicit. -/
theorem stopped_reference_lower_of_circuitRecords
    {Y : Type*} [Finite Y] (H : SimpleGraph Y) (θ : Parameters)
    (ξ η : BoundaryCondition Y) (reveal : RevealMap (G := H))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (T : Set (StoppingObservationRange reveal))
    (X : Configuration H → Type*) [hX : ∀ C₀, Finite (X C₀)]
    (G : (C₀ : Configuration H) → SimpleGraph (X C₀))
    (f : (C₀ : Configuration H) → X C₀ ↪ Y)
    (hGH : ∀ C₀, (G C₀).map (f C₀) ≤ H)
    (B : (C₀ : Configuration H) → Set (X C₀))
    (Ein : (C₀ : Configuration H) → Set (Configuration (G C₀)))
    (hEin : ∀ C₀, IsUpperSet (Ein C₀)) (E : Set (Configuration H))
    (hremoved : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      reveal C₀ = subgraphRemovedEdges ((G C₀).map (f C₀)) H)
    (hclosed : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      ∀ ⦃x : X C₀⦄, x ∉ B C₀ → ∀ ⦃y : Y⦄, H.Adj (f C₀ x) y →
        ∃ z : X C₀, f C₀ z = y ∧ (G C₀).Adj x z)
    (havoid : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      ∀ ⦃x : X C₀⦄, x ∉ B C₀ → f C₀ x ∉ η.boundary)
    (hwire : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      (BoundaryCondition.wired (B C₀)).partition ≤
        (isolatedExtensionPullbackBoundary (f C₀)
          (frozenBoundary ξ (C₀ ∩ subgraphRemovedEdges ((G C₀).map (f C₀)) H))).partition)
    (hevent : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      {A | embeddedConfigurationRestriction (G C₀) H (f C₀) (hGH C₀) A ∈ Ein C₀} = E) :
    (measure H θ η E).toReal *
      (measure H θ ξ ((stoppingObservationMap reveal) ⁻¹' T)).toReal ≤
        (measure H θ ξ E).toReal := by
  apply stopped_event_lower_of_record_bounds θ ξ reveal hstable E T
  intro C₀ hC₀
  let Q := subgraphRemovedEdges ((G C₀).map (f C₀)) H
  let K : RemovedConfiguration H Q := ⟨C₀ ∩ Q,Finset.inter_subset_right⟩
  have href := frozen_reference_lower_of_wiredCircuitPartition
    (G C₀) H (f C₀) (hGH C₀) θ ξ η (B C₀)
    (hclosed C₀ hC₀) (havoid C₀ hC₀) K (hwire C₀ hC₀) (Ein C₀) (hEin C₀)
  rw [hevent C₀ hC₀] at href
  have hrec : revealRecordEvent reveal C₀ = frozenStateEvent Q K := by
    rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
    ext A
    change A ∩ reveal C₀ = C₀ ∩ reveal C₀ ↔ A ∩ Q = C₀ ∩ Q
    rw [show reveal C₀ = Q from hremoved C₀ hC₀]
  have hsRecord : ∃ A ∈ revealRecordEvent reveal C₀, A ∈ (law H θ ξ).support := by
    rw [hrec]
    exact frozenStateEvent_support θ ξ Q K
  have hfilter : (law H θ ξ).filter (revealRecordEvent reveal C₀) hsRecord =
      (law H θ ξ).filter (frozenStateEvent Q K) (frozenStateEvent_support θ ξ Q K) := by
    ext A
    simp only [PMF.filter_apply,hrec]
  rw [hfilter]
  exact href

end
end PottsContinuity.RSW
