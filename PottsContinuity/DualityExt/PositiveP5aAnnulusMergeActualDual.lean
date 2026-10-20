module

public import PottsContinuity.DualityExt.PositiveAnnulusDualTransfer
public import PottsContinuity.DualityExt.PositiveP5aAnnulusActualDualJordan
public import PottsContinuity.DualityExt.PositiveGraphRelabeling
public import PottsContinuity.DualityExt.PositivePDLawBridge

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

private theorem positiveFKLaw_map_cast_of_graph_eq
    {V : Type*} [Finite V] {G H : SimpleGraph V} (hGH : G = H)
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) :
    (positiveFKLaw G q p hq hp hp1 ξ).map
        (Equiv.cast (congrArg Configuration hGH)) =
      positiveFKLaw H q p hq hp hp1 ξ := by
  cases hGH
  change (positiveFKLaw G q p hq hp hp1 ξ).map id = _
  exact PMF.map_id _

local instance p5aMergeActualTargetConfigFintype
    {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (hK : K ≤ rectangleGraph a w h) :
    Fintype (Configuration
      (rectangleSubgraphDualGraph hK)) := Fintype.ofFinite _

/-- The configuration map induced by an exact graph identification with the
edge-deleted annulus dual graph. -/
noncomputable def annulusCandidateToActualDualConfigurationEquiv
    (N : ℕ) {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (f : RectangleVertex a w h ≃
      RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N))
    (hIso : K.map f.toEmbedding =
      rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)) :
    Configuration K ≃
      Configuration (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)) :=
  (isolatedExtensionConfigurationEquiv K f.toEmbedding).trans
    (Equiv.cast (congrArg Configuration hIso))

/-- An exact graph identification transports the free FK law to the free law
on the edge-deleted annulus dual graph. -/
theorem annulusCandidate_freeLaw_map_eq_actualDual_freeLaw
    (N : ℕ) {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (f : RectangleVertex a w h ≃
      RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N))
    (hIso : K.map f.toEmbedding =
      rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
    (q : Set.Ici (1 : ℝ)) :
    (law K (criticalParameters q) (BoundaryCondition.free ∅)).map
        (annulusCandidateToActualDualConfigurationEquiv N f hIso) =
      law (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
        (criticalParameters q) (BoundaryCondition.free ∅) := by
  let θ := criticalParameters q
  let ξ := positiveBoundaryTransport f (BoundaryCondition.free ∅)
  let c := Equiv.cast (congrArg Configuration hIso)
  let r := isolatedExtensionConfigurationEquiv K f.toEmbedding
  have hpart : ξ.partition = (BoundaryCondition.free ∅).partition := by
    simp only [ξ, positiveBoundaryTransport, BoundaryCondition.free, Setoid.comap]
    apply Setoid.ext
    intro u v
    simp
  have hpositive := positiveFKLaw_relabel_map
    (G := K) (clusterWeight_pos θ) (edgeParameter_pos θ)
    (edgeParameter_lt_one θ) (BoundaryCondition.free ∅) f
  have hrename := positiveFKLaw_eq_of_partition_eq
    (G := K.map f.toEmbedding) (clusterWeight_pos θ) (edgeParameter_pos θ)
    (edgeParameter_lt_one θ) ξ (BoundaryCondition.free ∅) hpart
  have hcast :
      (positiveFKLaw (K.map f.toEmbedding) θ.val
        (edgeParameter θ) (clusterWeight_pos θ) (edgeParameter_pos θ)
        (edgeParameter_lt_one θ) (BoundaryCondition.free ∅)).map c =
      positiveFKLaw (rectangleSubgraphDualGraph
        (annulusSourceGraph_map_le_host N)) θ.val
        (edgeParameter θ) (clusterWeight_pos θ) (edgeParameter_pos θ)
        (edgeParameter_lt_one θ) (BoundaryCondition.free ∅) := by
    exact positiveFKLaw_map_cast_of_graph_eq hIso
      (clusterWeight_pos θ) (edgeParameter_pos θ) (edgeParameter_lt_one θ)
      (BoundaryCondition.free ∅)
  have hpositiveMap :
      (positiveFKLaw K θ.val (edgeParameter θ)
        (clusterWeight_pos θ) (edgeParameter_pos θ) (edgeParameter_lt_one θ)
        (BoundaryCondition.free ∅)).map
          (annulusCandidateToActualDualConfigurationEquiv N f hIso) =
      positiveFKLaw (rectangleSubgraphDualGraph
        (annulusSourceGraph_map_le_host N)) θ.val
        (edgeParameter θ) (clusterWeight_pos θ) (edgeParameter_pos θ)
        (edgeParameter_lt_one θ) (BoundaryCondition.free ∅) := by
    change (positiveFKLaw K θ.val (edgeParameter θ)
        (clusterWeight_pos θ) (edgeParameter_pos θ) (edgeParameter_lt_one θ)
        (BoundaryCondition.free ∅)).map (r.trans c) = _
    calc
      _ = ((positiveFKLaw K θ.val (edgeParameter θ)
          (clusterWeight_pos θ) (edgeParameter_pos θ) (edgeParameter_lt_one θ)
          (BoundaryCondition.free ∅)).map r).map c := by
            rw [PMF.map_comp]
            rfl
      _ = (positiveFKLaw (K.map f.toEmbedding) θ.val
          (edgeParameter θ) (clusterWeight_pos θ) (edgeParameter_pos θ)
          (edgeParameter_lt_one θ) ξ).map c := congrArg (fun μ => μ.map c) hpositive
      _ = (positiveFKLaw (K.map f.toEmbedding) θ.val
          (edgeParameter θ) (clusterWeight_pos θ) (edgeParameter_pos θ)
          (edgeParameter_lt_one θ) (BoundaryCondition.free ∅)).map c :=
            congrArg (fun μ => μ.map c) hrename
      _ = _ := hcast
  rw [← positiveFKLaw_eq_PD_law (θ := θ) (ξ := BoundaryCondition.free ∅)]
  rw [← positiveFKLaw_eq_PD_law
    (G := rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N))
    (θ := θ) (ξ := BoundaryCondition.free ∅)]
  exact hpositiveMap

end
end PottsContinuity.DualityExt
