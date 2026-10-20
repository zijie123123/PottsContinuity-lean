-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/SubgraphProbability.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.Cylinders
public import PottsContinuity.PD.RCInfinite.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

open MeasureTheory Set

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical
attribute [local instance] configurationMeasurableSpace

/-- Extend a finite induced-subgraph configuration to the whole lattice. Free
extensions close unsampled edges; wired extensions open them. -/
def finiteSubgraphConfiguration (S : Finset LatticeVertex) (i : Fin 2)
    (A : Configuration (finiteLatticeGraph S)) : LatticeConfiguration := by
  classical
  by_cases hi : i = 0
  · exact fun e => decide (e ∈ A.map (frozenEdgeEmbedding S))
  · exact fun e => decide (∀ f, frozenEdgeEmbedding S f = e → f ∈ A)

/-- The finite FK law on an arbitrary induced vertex set, extended to the
whole-lattice edge carrier with the boundary-condition convention. -/
def finiteSubgraphProbabilityMeasure (θ : Parameters) (S : Finset LatticeVertex)
    (i : Fin 2) : ProbabilityMeasure LatticeConfiguration :=
  frozenExtendedProbabilityMeasure θ S i (finiteSubgraphConfiguration S i)

private theorem finiteSubgraphConfiguration_open_iff (S : Finset LatticeVertex)
    (i : Fin 2) (A : Configuration (finiteLatticeGraph S)) (e : squareLattice.edgeSet)
    (he : e ∈ Set.range (frozenEdgeEmbedding S)) :
    finiteSubgraphConfiguration S i A e = true ↔ e ∈ A.map (frozenEdgeEmbedding S) := by
  classical
  by_cases hi : i = 0
  · simp [finiteSubgraphConfiguration, hi]
  · obtain ⟨f, hf⟩ := Set.mem_range.mp he
    constructor
    · intro hopen
      have hforall : ∀ g, frozenEdgeEmbedding S g = e → g ∈ A := by
        simpa [finiteSubgraphConfiguration, hi, decide_eq_true_eq] using hopen
      apply Finset.mem_map.mpr
      exact ⟨f, hforall f hf, hf⟩
    · intro hopen
      obtain ⟨g, hg, hge⟩ := Finset.mem_map.mp hopen
      have hforall : ∀ f, frozenEdgeEmbedding S f = e → f ∈ A := by
        intro f hfe
        have hfg : f = g := (frozenEdgeEmbedding S).injective (hfe.trans hge.symm)
        exact hfg ▸ hg
      simpa [finiteSubgraphConfiguration, hi, decide_eq_true_eq] using hforall

/-- A supported all-open event under the extended finite law is exactly its
finite random-cluster event on the induced subgraph. -/
theorem finiteSubgraphProbabilityMeasure_allOpen (θ : Parameters)
    (S : Finset LatticeVertex) (i : Fin 2) (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding S)) :
    (finiteSubgraphProbabilityMeasure θ S i : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F) =
      measure (finiteLatticeGraph S) θ (frozenBoundaryCondition S i)
        (finiteSubgraphOpenEvent S F) := by
  classical
  let ext := finiteSubgraphConfiguration S i
  change ((law (finiteLatticeGraph S) θ (frozenBoundaryCondition S i)).map ext).toMeasure
      (LatticeConfiguration.allOpen F) = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  have hpre : ext ⁻¹' LatticeConfiguration.allOpen F = finiteSubgraphOpenEvent S F := by
    ext A
    change (∀ e ∈ F, ext A e = true) ↔
      F ⊆ A.map (frozenEdgeEmbedding S)
    simp only [Finset.subset_iff]
    constructor
    · intro h e he
      exact (finiteSubgraphConfiguration_open_iff S i A e (hF e he)).mp (h e he)
    · intro h e he
      exact (finiteSubgraphConfiguration_open_iff S i A e (hF e he)).mpr (h he)
  rw [hpre]
  rfl

/-- On a centered square, the general finite-subgraph law agrees with the
existing common-carrier free or wired box law on supported all-open events. -/
theorem finiteSubgraphProbabilityMeasure_box_allOpen (θ : Parameters) (i : Fin 2)
    (r : ℕ) (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding (latticeBox (0, 0) r))) :
    (finiteSubgraphProbabilityMeasure θ (latticeBox (0, 0) r) i :
      Measure LatticeConfiguration).real (LatticeConfiguration.allOpen F) =
    (boxMeasure θ i (0, 0) r : Measure LatticeConfiguration).real
      (LatticeConfiguration.allOpen F) := by
  classical
  fin_cases i
  · change ENNReal.toReal ((finiteSubgraphProbabilityMeasure θ
        (latticeBox (0, 0) r) (0 : Fin 2) : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F)) =
      ENNReal.toReal ((boxMeasure θ (0 : Fin 2) (0, 0) r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F))
    rw [finiteSubgraphProbabilityMeasure_allOpen θ (latticeBox (0, 0) r) 0 F hF]
    rw [boxMeasure_free, boxProbabilityMeasure_allOpen]
    have hboundary :
        (frozenBoundaryCondition (latticeBox (0, 0) r) 0).partition =
          (BoundaryCondition.free (∅ : Set (BoxVertex (0, 0) r))).partition := by
      simp [frozenBoundaryCondition, BoundaryCondition.free]
    have hlaw :
        law (finiteLatticeGraph (latticeBox (0, 0) r)) θ
          (frozenBoundaryCondition (latticeBox (0, 0) r) 0) =
        law (boxGraph (0, 0) r) θ (BoundaryCondition.free ∅) := by
      exact law_eq_of_boundary_partition_eq θ
        (frozenBoundaryCondition (latticeBox (0, 0) r) 0)
        (BoundaryCondition.free (∅ : Set (BoxVertex (0, 0) r))) hboundary
    have hEmbed : frozenEdgeEmbedding (latticeBox (0, 0) r) =
        boxEdgeEmbedding (0, 0) r := rfl
    have hevent : finiteSubgraphOpenEvent (latticeBox (0, 0) r) F =
        {A | F ⊆ A.map (boxEdgeEmbedding (0, 0) r)} := by
      ext A
      rw [finiteSubgraphOpenEvent, hEmbed]
      rfl
    unfold FK.measure
    change ENNReal.toReal ((law (finiteLatticeGraph (latticeBox (0, 0) r)) θ
        (frozenBoundaryCondition (latticeBox (0, 0) r) 0)).toMeasure
          (finiteSubgraphOpenEvent (latticeBox (0, 0) r) F)) =
      ENNReal.toReal ((law (boxGraph (0, 0) r) θ (BoundaryCondition.free ∅)).toMeasure
        {A | F ⊆ A.map (boxEdgeEmbedding (0, 0) r)})
    rw [hlaw, hevent]
    rfl
  · change ENNReal.toReal ((finiteSubgraphProbabilityMeasure θ
        (latticeBox (0, 0) r) (1 : Fin 2) : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F)) =
      ENNReal.toReal ((boxMeasure θ (1 : Fin 2) (0, 0) r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F))
    rw [finiteSubgraphProbabilityMeasure_allOpen θ (latticeBox (0, 0) r) 1 F hF]
    rw [boxMeasure_wired, wiredBoxProbabilityMeasure_allOpen]
    have hevent : finiteSubgraphOpenEvent (latticeBox (0, 0) r) F =
        wiredBoxCylinderEvent (0, 0) r F := by
      ext A
      change (F ⊆ A.map (frozenEdgeEmbedding (latticeBox (0, 0) r))) ↔
        (∀ e ∈ F, ∀ f, boxEdgeEmbedding (0, 0) r f = e → f ∈ A)
      have hEmbed : frozenEdgeEmbedding (latticeBox (0, 0) r) =
          boxEdgeEmbedding (0, 0) r := rfl
      rw [hEmbed]
      constructor
      · intro h e he f hf
        obtain ⟨g, hg, hge⟩ := Finset.mem_map.mp (h he)
        have hfg : f = g := (frozenEdgeEmbedding (latticeBox (0, 0) r)).injective
          (hf.trans hge.symm)
        exact hfg ▸ hg
      · intro h e he
        obtain ⟨f, hf⟩ := Set.mem_range.mp (hF e he)
        rw [hEmbed] at hf
        apply Finset.mem_map.mpr
        exact ⟨f, h e he f hf, hf⟩
    have hboundary : frozenVertexBoundary (latticeBox (0, 0) r) =
        boxVertexBoundary (0, 0) r := rfl
    have hlaw :
        law (finiteLatticeGraph (latticeBox (0, 0) r)) θ
          (frozenBoundaryCondition (latticeBox (0, 0) r) 1) =
        law (boxGraph (0, 0) r) θ
          (BoundaryCondition.wired (boxVertexBoundary (0, 0) r)) := by
      exact law_eq_of_boundary_partition_eq θ
        (frozenBoundaryCondition (latticeBox (0, 0) r) 1)
        (BoundaryCondition.wired (frozenVertexBoundary (latticeBox (0, 0) r)))
        (by simp [frozenBoundaryCondition, hboundary])
    unfold FK.measure
    change ENNReal.toReal ((law (finiteLatticeGraph (latticeBox (0, 0) r)) θ
        (frozenBoundaryCondition (latticeBox (0, 0) r) 1)).toMeasure
          (finiteSubgraphOpenEvent (latticeBox (0, 0) r) F)) =
      ENNReal.toReal ((law (boxGraph (0, 0) r) θ
        (BoundaryCondition.wired (boxVertexBoundary (0, 0) r))).toMeasure
          (wiredBoxCylinderEvent (0, 0) r F))
    rw [hlaw, hevent]
    rfl

end
end PottsContinuity.PD.RCInfinite
