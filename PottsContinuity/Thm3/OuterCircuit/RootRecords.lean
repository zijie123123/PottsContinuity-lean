module

public import PottsContinuity.Thm3.OuterCircuit.ResidualAnnulusSupport
public import PottsContinuity.Thm3.OuterCircuit.LiftedResidual
public import PottsContinuity.Thm3.RSW.Lemma4SourceEvents
public import PottsContinuity.Thm3.RSW.FrozenCircuitInteriorComparison
public import PottsContinuity.Thm3.RSW.StoppingJointAverage
public import Mathlib.Probability.ConditionalProbability
public import PottsContinuity.Thm3.RSW.FrozenCircuitWiring
public import PottsContinuity.Thm3.RSW.Lemma4OuterCircuitRecords

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Exploration
open MeasureTheory

universe u

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance outerCircuitRootRecordsAmbientEdgeDecidableEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _

local instance outerCircuitRootRecordsAmbientEdgeFintype (n : ℕ) :
    Fintype (lemma4AmbientGraph n).edgeSet := Fintype.ofFinite _

local instance outerCircuitRootRecordsResidualEdgeDecidableEq {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    DecidableEq (outerCircuitResidualGraph C).edgeSet := Classical.decEq _

local instance outerCircuitRootRecordsResidualEdgeFintype {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    Fintype (outerCircuitResidualGraph C).edgeSet := Fintype.ofFinite _

private theorem outerCircuitSelectedCandidate_of_observation {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (hobs : stoppingObservationMap (outerCircuitSelectorReveal (n := n)) C ∈
      outerCircuitSelectedObservationSet (n := n)) :
    ∃ p : OuterCircuitPolygonCode n,
      outerCircuitMaximumCandidate C = some (.inl p) ∧
      outerCircuitCandidateValid C p := by
  have hpre : C ∈ (stoppingObservationMap (outerCircuitSelectorReveal (n := n))) ⁻¹'
      outerCircuitSelectedObservationSet (n := n) := hobs
  rw [lemma4OuterAnnulusEvent_observation_preimage] at hpre
  exact outerCircuitMaximumCandidate_selected_of_outer_event C hpre

/-- Exact root-path record family for the source outermost open circuit
exploration in equation (9). -/
theorem lemma4_outer_open_circuit_root_records (n : ℕ) (hn : 1 ≤ n) :
    ∃ (reveal : RevealMap (G := (lemma4AmbientGraph n))),
    ∃ (T : Set (StoppingObservationRange reveal)),
    ∃ (X : Configuration (lemma4AmbientGraph n) → Type u),
    ∃ (G : (C₀ : Configuration (lemma4AmbientGraph n)) → SimpleGraph (X C₀)),
    ∃ (f : (C₀ : Configuration (lemma4AmbientGraph n)) → X C₀ ↪ {z : LatticeVertex // z ∈ box (56*n)}),
    ∃ (hGH : ∀ C₀, (G C₀).map (f C₀) ≤ (lemma4AmbientGraph n)),
    ∃ (B : (C₀ : Configuration (lemma4AmbientGraph n)) → Set (X C₀)),
    ∃ (Ein : (C₀ : Configuration (lemma4AmbientGraph n)) → Set (Configuration (G C₀))),
    ∃ (r : Configuration (lemma4AmbientGraph n) → {z : LatticeVertex // z ∈ box (56*n)}),
    (∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C) ∧
    (∀ C₀, Finite (X C₀)) ∧
    (∀ C₀, IsUpperSet (Ein C₀)) ∧
    (∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      reveal C₀ = subgraphRemovedEdges ((G C₀).map (f C₀)) (lemma4AmbientGraph n)) ∧
    (∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      ∀ ⦃x : X C₀⦄, x ∉ B C₀ → ∀ ⦃y : {z : LatticeVertex // z ∈ box (56*n)}⦄,
        (lemma4AmbientGraph n).Adj (f C₀ x) y →
        ∃ z : X C₀, f C₀ z = y ∧ (G C₀).Adj x z) ∧
    (∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      ∀ ⦃x : X C₀⦄, x ∉ B C₀ →
        f C₀ x ∉ (frozenBoundaryCondition (box (56*n)) 1).boundary) ∧
    (∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      ∀ x ∈ B C₀, ActualConnected (lemma4AmbientGraph n)
        (C₀ ∩ subgraphRemovedEdges ((G C₀).map (f C₀)) (lemma4AmbientGraph n))
        (f C₀ x) (r C₀)) ∧
    (∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      {A | embeddedConfigurationRestriction (G C₀) (lemma4AmbientGraph n)
        (f C₀) (hGH C₀) A ∈ Ein C₀} = lemma4AnnulusPairEvent n) ∧
    ((stoppingObservationMap reveal) ⁻¹' T = lemma4OuterAnnulusEvent n) := by
  let X : Configuration (lemma4AmbientGraph n) → Type u :=
    fun C₀ => ULift.{u,0} (OuterCircuitResidualVertices n C₀)
  let G : (C₀ : Configuration (lemma4AmbientGraph n)) → SimpleGraph (X C₀) :=
    outerCircuitLiftedResidualGraph
  let f : (C₀ : Configuration (lemma4AmbientGraph n)) → X C₀ ↪
      {z : LatticeVertex // z ∈ box (56*n)} := outerCircuitLiftedResidualEmbedding
  let B : (C₀ : Configuration (lemma4AmbientGraph n)) → Set (X C₀) :=
    outerCircuitLiftedResidualBoundarySet
  let Ein : (C₀ : Configuration (lemma4AmbientGraph n)) → Set (Configuration (G C₀)) :=
    outerCircuitLiftedResidualAnnulusPairEvent
  let r : Configuration (lemma4AmbientGraph n) →
      {z : LatticeVertex // z ∈ box (56*n)} := outerCircuitSelectedRoot
  have hAdjLift (C₀ : Configuration (lemma4AmbientGraph n)) (x y : X C₀) :
      (G C₀).Adj x y ↔ (outerCircuitResidualGraph C₀).Adj x.down y.down := by
    have hx : outerCircuitLiftedResidualGraphIso C₀ x.down = x := by
      apply ULift.ext
      rfl
    have hy : outerCircuitLiftedResidualGraphIso C₀ y.down = y := by
      apply ULift.ext
      rfl
    have h := (outerCircuitLiftedResidualGraphIso C₀).map_adj_iff
      (v := x.down) (w := y.down)
    rw [hx, hy] at h
    exact h
  have hmap (C₀ : Configuration (lemma4AmbientGraph n)) :
      (G C₀).map (f C₀) = (outerCircuitResidualGraph C₀).map
        (outerCircuitResidualEmbedding C₀) := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    rw [SimpleGraph.map_adj, SimpleGraph.map_adj]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      refine ⟨a.down, b.down, (hAdjLift C₀ a b).mp hab, ?_, ?_⟩
      · change outerCircuitResidualEmbedding C₀ a.down = x at ha
        exact ha
      · change outerCircuitResidualEmbedding C₀ b.down = y at hb
        exact hb
    · rintro ⟨a, b, hab, ha, hb⟩
      refine ⟨ULift.up a, ULift.up b, (hAdjLift C₀ _ _).mpr hab, ?_, ?_⟩
      · change outerCircuitResidualEmbedding C₀ a = x
        exact ha
      · change outerCircuitResidualEmbedding C₀ b = y
        exact hb
  let hGH : ∀ C₀, (G C₀).map (f C₀) ≤ lemma4AmbientGraph n := by
    intro C₀
    rw [hmap C₀]
    exact outerCircuitResidualGraph_map_le C₀
  refine ⟨outerCircuitSelectorReveal, outerCircuitSelectedObservationSet,
    X, G, f, hGH, B, Ein, r, ?_⟩
  refine ⟨outerCircuitSelectorReveal_stable, ?_⟩
  constructor
  · intro C₀
    exact Finite.of_injective ULift.down ULift.down_injective
  constructor
  · intro C₀
    exact outerCircuitLiftedResidualAnnulusPairEvent_isUpperSet C₀
  constructor
  · intro C₀ hobs
    simpa only [G, f, hmap C₀] using
      (outerCircuitResidual_removedEdges_eq_reveal C₀).symm
  constructor
  · intro C₀ hobs x hxnotB y hxy
    obtain ⟨p, hselected, _⟩ := outerCircuitSelectedCandidate_of_observation C₀ hobs
    have hdown : (outerCircuitLiftedResidualGraphIso C₀).symm x = x.down := by
      rfl
    have hnotB : ¬ outerCircuitResidualBoundaryVertex C₀ x.down.val := by
      change ¬ ((outerCircuitLiftedResidualGraphIso C₀).symm x ∈
        outerCircuitResidualBoundarySet C₀) at hxnotB
      rw [hdown] at hxnotB
      simpa [outerCircuitResidualBoundarySet] using hxnotB
    obtain ⟨z, hzy, hxz⟩ := outerCircuitResidualVertex_closed_of_selected
      C₀ p hselected hn x.down.property hnotB
      (by
        change (lemma4AmbientGraph n).Adj
          (outerCircuitResidualEmbedding C₀ x.down) y at hxy
        exact hxy)
    refine ⟨ULift.up z, ?_, (hAdjLift C₀ x (ULift.up z)).mpr hxz⟩
    change outerCircuitResidualEmbedding C₀ z = y
    exact hzy
  constructor
  · intro C₀ hobs x hxnotB
    obtain ⟨p, hselected, _⟩ := outerCircuitSelectedCandidate_of_observation C₀ hobs
    have hdown : (outerCircuitLiftedResidualGraphIso C₀).symm x = x.down := by
      rfl
    have hnotB : ¬ outerCircuitResidualBoundaryVertex C₀ x.down.val := by
      change ¬ ((outerCircuitLiftedResidualGraphIso C₀).symm x ∈
        outerCircuitResidualBoundarySet C₀) at hxnotB
      rw [hdown] at hxnotB
      simpa [outerCircuitResidualBoundarySet] using hxnotB
    have havoid := outerCircuitResidualVertex_avoids_outerBoundary_of_selected
      C₀ p hselected hn x.down.property hnotB
    change outerCircuitResidualEmbedding C₀ x.down ∉
      (frozenBoundaryCondition (box (56*n)) 1).boundary
    exact havoid
  constructor
  · intro C₀ hobs x hxB
    obtain ⟨p, hselected, hvalid⟩ := outerCircuitSelectedCandidate_of_observation C₀ hobs
    have hremoved : outerCircuitSelectorReveal C₀ =
        subgraphRemovedEdges ((outerCircuitResidualGraph C₀).map
          (outerCircuitResidualEmbedding C₀)) (lemma4AmbientGraph n) :=
      (outerCircuitResidual_removedEdges_eq_reveal C₀).symm
    have hdown : (outerCircuitLiftedResidualGraphIso C₀).symm x = x.down := by
      rfl
    have hxB' : x.down ∈ outerCircuitResidualBoundarySet C₀ := by
      change (outerCircuitLiftedResidualGraphIso C₀).symm x ∈
        outerCircuitResidualBoundarySet C₀ at hxB
      rw [hdown] at hxB
      exact hxB
    have hpath := outerCircuitResidualBoundary_actualConnected_of_removed C₀ p
      hselected hvalid hremoved hxB'
    rw [hmap C₀]
    change ActualConnected (lemma4AmbientGraph n)
      (C₀ ∩ subgraphRemovedEdges
        ((outerCircuitResidualGraph C₀).map (outerCircuitResidualEmbedding C₀))
        (lemma4AmbientGraph n))
      (outerCircuitResidualEmbedding C₀ x.down) (outerCircuitSelectedRoot C₀)
    exact hpath
  constructor
  · intro C₀ hobs
    obtain ⟨p, hselected, hvalid⟩ := outerCircuitSelectedCandidate_of_observation C₀ hobs
    ext A
    have hrest : outerCircuitLiftedResidualConfigurationToBase C₀
        (embeddedConfigurationRestriction (G C₀) (lemma4AmbientGraph n)
          (f C₀) (hGH C₀) A) =
      embeddedConfigurationRestriction (outerCircuitResidualGraph C₀)
        (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C₀)
        (outerCircuitResidualGraph_map_le C₀) A := by
      ext e
      rw [outerCircuitLiftedResidualConfigurationToBase_mem_iff,
        mem_embeddedConfigurationRestriction,
        mem_embeddedConfigurationRestriction]
      have hedge : embeddedEdgeEmbedding (G C₀) (lemma4AmbientGraph n)
          (f C₀) (hGH C₀) ((outerCircuitLiftedResidualGraphIso C₀).mapEdgeSet e) =
        embeddedEdgeEmbedding (outerCircuitResidualGraph C₀) (lemma4AmbientGraph n)
          (outerCircuitResidualEmbedding C₀) (outerCircuitResidualGraph_map_le C₀) e := by
        have heval : ((outerCircuitLiftedResidualGraphIso C₀).mapEdgeSet e).val =
            Sym2.map (Equiv.ulift.{u,0}.symm) e.val := by
          rfl
        apply Subtype.ext
        rw [embeddedEdgeEmbedding_coe, embeddedEdgeEmbedding_coe, heval]
        change Sym2.map (fun x : X C₀ => f C₀ x)
            (Sym2.map (Equiv.ulift.{u,0}.symm) e.val) =
          Sym2.map (outerCircuitResidualEmbedding C₀) e.val
        rw [Sym2.map_map]
        congr 1
      rw [hedge]
    change outerCircuitLiftedResidualConfigurationToBase C₀
        (embeddedConfigurationRestriction (G C₀) (lemma4AmbientGraph n)
          (f C₀) (hGH C₀) A) ∈ outerCircuitResidualAnnulusPairEvent C₀ ↔
      A ∈ lemma4AnnulusPairEvent n
    rw [hrest]
    exact (outerCircuitSelectedResidualAnnulusPairEvent_iff C₀ p hselected
      hvalid hn A).symm
  · exact lemma4OuterAnnulusEvent_observation_preimage

/-- The source eq. (10) bound with the outermost open-circuit records supplied
by this module. -/
theorem selfDual_lemma4_two_annuli_lower (q : Set.Ici (1:ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * annulusProbability (selfDualParameters q) 8 (7*n) ≤
        (measure (lemma4AmbientGraph n) (selfDualParameters q)
          (frozenBoundaryCondition (box (56*n)) 0)
          (lemma4AnnulusPairEvent n)).toReal := by
  obtain ⟨c, hc, hbound⟩ :=
    RSW.selfDual_lemma4_two_annuli_lower_of_circuitRecords q
  refine ⟨c, hc, ?_⟩
  intro n hn
  obtain ⟨reveal, T, X, G, f, hGH, B, Ein, r,
      hstable, hX, hEin, hremoved, hclosed, havoid, hpath, hevent, hsource⟩ :=
    lemma4_outer_open_circuit_root_records.{0} n hn
  have hwire : ∀ C₀, stoppingObservationMap reveal C₀ ∈ T →
      (BoundaryCondition.wired (V := X C₀) (B C₀)).partition ≤
        (isolatedExtensionPullbackBoundary (f C₀)
          (frozenBoundary (frozenBoundaryCondition (box (56*n)) 0)
            (C₀ ∩ subgraphRemovedEdges ((G C₀).map (f C₀))
              (lemma4AmbientGraph n)))).partition := by
    intro C₀ hC₀
    apply wiredCircuitPartition_le_frozen_of_recordedRootPaths
      (lemma4AmbientGraph n) (f C₀)
      (frozenBoundaryCondition (box (56*n)) 0) _ (B C₀) (r C₀)
    intro x hx
    exact actualConnected_mono (by
      intro e he
      simpa only [Finset.mem_inter] using he) (hpath C₀ hC₀ x hx)
  exact hbound n hn reveal hstable T X G f hGH B Ein hEin hremoved
    hclosed havoid hwire hevent hsource

end
end PottsContinuity.OuterCircuit
