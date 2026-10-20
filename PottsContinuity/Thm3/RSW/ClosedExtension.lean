module

public import PottsContinuity.Thm3.RSW.ArmOpen
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion

/-!
# Actual connections under closed finite-domain extension

The free finite-domain configuration closes every unsampled edge. Its infinite
open graph is exactly the injective image of the finite open graph, including
all isolated lattice vertices. Connections between sampled vertices are unchanged.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Closed extension creates exactly the image of the finite actual open graph. -/
theorem finiteClosedExtension_openGraph (V : Finset (ℤ × ℤ))
    (A : Configuration (PD.FK.squareLattice.induce (V : Set (ℤ × ℤ)))) :
    PD.rcInfiniteOpenGraph (finiteSubgraphConfiguration V 0 A) =
      (openGraph (PD.FK.squareLattice.induce (V : Set (ℤ × ℤ))) A).map
        (⟨Subtype.val, Subtype.val_injective⟩ : (V : Set (ℤ × ℤ)) ↪ (ℤ × ℤ)) := by
  classical
  have hinf : PD.rcInfiniteOpenGraph (finiteSubgraphConfiguration V 0 A) =
      openGraph PD.FK.squareLattice (A.map (frozenEdgeEmbedding V)) := by
    change SimpleGraph.fromEdgeSet _ = SimpleGraph.fromEdgeSet _
    congr 1
    ext e
    constructor
    · rintro ⟨he, hω⟩
      have hmem : (⟨e, he⟩ : PD.FK.squareLattice.edgeSet) ∈ A.map (frozenEdgeEmbedding V) := by
        simpa [finiteSubgraphConfiguration] using hω
      exact ⟨⟨e, he⟩, hmem, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.property, by simpa [finiteSubgraphConfiguration] using he⟩
  rw [hinf]
  apply SimpleGraph.edgeSet_injective
  rw [openGraph_edgeSet, SimpleGraph.edgeSet_map, openGraph_edgeSet]
  simp only [openEdges]
  change Subtype.val '' (↑(A.map (frozenEdgeEmbedding V)) : Set PD.FK.squareLattice.edgeSet) = _
  rw [Finset.coe_map, Set.image_image]
  simp only [Set.image_image]
  rfl

/-- Actual connectivity between finite-domain vertices is preserved by closing
all exterior edges, with no boundary identifications in the event. -/
theorem finiteClosedExtension_connection_iff (V : Finset (ℤ × ℤ))
    (A : Configuration (PD.FK.squareLattice.induce (V : Set (ℤ × ℤ))))
    (x y : V) :
    (PD.rcInfiniteOpenGraph (finiteSubgraphConfiguration V 0 A)).Reachable x.val y.val ↔
      ActualConnected (PD.FK.squareLattice.induce (V : Set (ℤ × ℤ))) A x y := by
  rw [finiteClosedExtension_openGraph]
  exact reachable_isolatedExtension_apply _ _ x y

/-- On boxes containing the target boundary, the closed finite-domain extension
has exactly the original finite arm event as its whole-plane arm preimage. -/
theorem finiteClosedExtension_arm_preimage (N k : ℕ) (hkN : k ≤ N) :
    (finiteSubgraphConfiguration (box N) 0) ⁻¹' infiniteArmEvent k =
      finiteBoolEvent (box N) (fun ω => ω ∈ finiteArmEvent N k) := by
  ext A
  change (∃ y ∈ vertexBoundary (box k), _) ↔ _
  have h0 : (0, 0) ∈ box N := by
    simp only [box, Finset.mem_product, Finset.mem_Icc]
    constructor <;> constructor <;> omega
  have hyN (y : ℤ × ℤ) (hy : y ∈ vertexBoundary (box k)) : y ∈ box N := by
    have hky := hy.1
    simp only [box, Finset.mem_product, Finset.mem_Icc] at hky ⊢
    constructor <;> constructor <;> omega
  constructor
  · rintro ⟨y, hy, hconn⟩
    refine ⟨y, hy, ?_⟩
    apply (finiteConnectionEvent_bool_iff (box N) (0, 0) y h0 (hyN y hy) A).mpr
    exact (finiteClosedExtension_connection_iff (box N) A ⟨(0, 0), h0⟩ ⟨y, hyN y hy⟩).mp hconn
  · rintro ⟨y, hy, hconn⟩
    refine ⟨y, hy, ?_⟩
    apply (finiteClosedExtension_connection_iff (box N) A ⟨(0, 0), h0⟩ ⟨y, hyN y hy⟩).mpr
    exact (finiteConnectionEvent_bool_iff (box N) (0, 0) y h0 (hyN y hy) A).mp hconn

/-- The exact finite law of the whole-plane arm under closed extension. -/
theorem finiteClosedExtension_arm_probability (θ : Parameters) (N k : ℕ) (hkN : k ≤ N) :
    (finiteSubgraphProbabilityMeasure θ (box N) 0).toMeasure
        (infiniteArmEvent k) = ENNReal.ofReal (finiteArmProbability θ N k) := by
  let E : Set LatticeConfiguration := infiniteArmEvent k
  have hE : MeasurableSet E := (infiniteArmEvent_isOpen k).measurableSet
  have hpre : (finiteSubgraphConfiguration (box N) 0) ⁻¹' E =
      finiteBoolEvent (box N) (fun ω => ω ∈ finiteArmEvent N k) :=
    finiteClosedExtension_arm_preimage N k hkN
  change ((law _ θ (frozenBoundaryCondition (box N) 0)).map
    (finiteSubgraphConfiguration (box N) 0)).toMeasure E = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hE, hpre]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

end
end PottsContinuity.RSW
