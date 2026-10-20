module

public import PottsContinuity.DualityExt.GeneralFiniteDuality
public import PottsContinuity.PD.FK.IsolatedBoundaryComponents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Isolated-vertex carrier changes for positive-`q` FK laws

When a graph is embedded into a larger vertex carrier and the added vertices
are isolated, an arbitrary boundary partition on the larger carrier pulls
back to the smaller graph. Boundary classes wholly outside the embedded graph
contribute one common power of `q`, which cancels in the normalized law.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
variable (G : SimpleGraph V)

/-- Vertices incident to at least one edge of a graph. -/
noncomputable def positiveActiveVertexSet (H : SimpleGraph W) : Set W := by
  classical
  exact {v | ∃ e : H.edgeSet, v ∈ e.1.toFinset}

/-- The endpoint-only graph obtained by removing isolated vertices. -/
def positiveActiveGraph (H : SimpleGraph W) : SimpleGraph (positiveActiveVertexSet H) :=
  H.induce (positiveActiveVertexSet H)

def positiveActiveInclusion (H : SimpleGraph W) : positiveActiveVertexSet H ↪ W :=
  ⟨Subtype.val, Subtype.val_injective⟩

omit [Finite W] in
/-- Mapping the endpoint-only graph back to the original carrier restores the
same edge relation; all omitted vertices were isolated. -/
theorem positiveActiveGraph_map_subtype (H : SimpleGraph W) :
    (positiveActiveGraph H).map (positiveActiveInclusion H) = H := by
  classical
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    exact hxy
  · intro huv
    have hu : u ∈ positiveActiveVertexSet H := by
      refine ⟨⟨s(u, v), H.mem_edgeSet.mpr huv⟩, ?_⟩
      simp
    have hv : v ∈ positiveActiveVertexSet H := by
      refine ⟨⟨s(u, v), H.mem_edgeSet.mpr huv⟩, ?_⟩
      simp
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, huv, rfl, rfl⟩

/-- Configuration equivalence from the endpoint-only graph to the original
carrier, including the canonical equality of the mapped graph with `H`. -/
noncomputable def positiveActiveConfigurationEquiv (H : SimpleGraph W) :
    Configuration (positiveActiveGraph H) ≃ Configuration H :=
  (isolatedExtensionConfigurationEquiv (positiveActiveGraph H)
    (positiveActiveInclusion H)).trans
    (Equiv.cast (congrArg Configuration (positiveActiveGraph_map_subtype H)))

local instance positiveIsolatedInnerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveIsolatedExtendedEdgeFintype (f : V ↪ W) :
    Fintype (G.map f).edgeSet := Fintype.ofFinite _
local instance positiveIsolatedInnerConfigFintype : Fintype (Configuration G) := Fintype.ofFinite _
local instance positiveIsolatedExtendedConfigFintype (f : V ↪ W) :
    Fintype (Configuration (G.map f)) := Fintype.ofFinite _

private theorem positiveFKWeight_pos_for_isolatedExtension
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (H : SimpleGraph W) (ξ : BoundaryCondition W) (A : Configuration H) :
    0 < positiveFKWeight H q p ξ A := by
  unfold positiveFKWeight
  exact mul_pos
    (mul_pos (pow_pos hp _) (pow_pos (sub_pos.mpr hp1) _))
    (pow_pos hq _)

/-- The unnormalized positive-`q` weight acquires precisely the power of `q`
from boundary classes wholly outside the embedded vertex range. -/
theorem positiveFKWeight_isolatedExtension_boundary_pullback
    (f : V ↪ W) {q p : ℝ} (ξ : BoundaryCondition W)
    (A : Configuration G) :
    positiveFKWeight (G.map f) q p ξ (isolatedExtensionConfigurationEquiv G f A) =
      positiveFKWeight G q p (isolatedExtensionPullbackBoundary f ξ) A *
        q ^ Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  rw [positiveFKWeight, positiveFKWeight,
    card_isolatedExtensionConfigurationEquiv, isolatedExtension_edge_card,
    componentCount_isolatedExtension_boundary_pullback G f ξ A, pow_add]
  simp only [mul_assoc]

/-- An arbitrary positive-`q` FK law is unchanged, after the natural
configuration embedding, when isolated vertices and an arbitrary boundary
partition are added. The boundary condition on the original graph is the
exact pullback partition; exterior boundary classes contribute only a common
normalizing factor. -/
theorem positiveFKLaw_isolatedExtension_map_boundary_pullback
    (f : V ↪ W) {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition W) :
    (positiveFKLaw G q p hq hp hp1 (isolatedExtensionPullbackBoundary f ξ)).map
        (isolatedExtensionConfigurationEquiv G f) =
      positiveFKLaw (G.map f) q p hq hp hp1 ξ := by
  let d : ℝ := q ^ Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ)
  let c : ℝ := d⁻¹
  have hd : 0 < d := by dsimp [d]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hweight (A : Configuration G) :
      positiveFKWeight G q p (isolatedExtensionPullbackBoundary f ξ) A =
        c * positiveFKWeight (G.map f) q p ξ
          (isolatedExtensionConfigurationEquiv G f A) := by
    have h := positiveFKWeight_isolatedExtension_boundary_pullback
      G f (q := q) (p := p) ξ A
    rw [h]
    dsimp [c, d]
    field_simp
  unfold positiveFKLaw
  exact FiniteProbability.pmf_map_equiv_of_common_factor
    (isolatedExtensionConfigurationEquiv G f) c _ _ hc
    (positiveFKWeight_pos_for_isolatedExtension hq hp hp1 G
      (isolatedExtensionPullbackBoundary f ξ))
    (positiveFKWeight_pos_for_isolatedExtension hq hp hp1 (G.map f) ξ)
    hweight

private theorem positiveFKLaw_eq_of_graph_eq
    {H K : SimpleGraph W} (hHK : H = K)
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition W) :
    (positiveFKLaw H q p hq hp hp1 ξ).map
        (Equiv.cast (congrArg (fun J => Configuration J) hHK)) =
      positiveFKLaw K q p hq hp hp1 ξ := by
  cases hHK
  rw [Equiv.cast_refl]
  change (positiveFKLaw H q p hq hp hp1 ξ).map id = _
  rw [PMF.map_id]

/-- The law on a graph is the pushforward of the law on its endpoint-only
induced graph, with the boundary partition pulled back to those endpoints. -/
theorem positiveFKLaw_activeGraph_map_boundary_pullback
    (H : SimpleGraph W) {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition W) :
    (positiveFKLaw (positiveActiveGraph H) q p hq hp hp1
      (isolatedExtensionPullbackBoundary (positiveActiveInclusion H) ξ)).map
        ((isolatedExtensionConfigurationEquiv (positiveActiveGraph H)
          (positiveActiveInclusion H)).trans
          (Equiv.cast (congrArg (fun K => Configuration K)
            (positiveActiveGraph_map_subtype H)))) =
      positiveFKLaw H q p hq hp hp1 ξ := by
  let e := isolatedExtensionConfigurationEquiv (positiveActiveGraph H)
    (positiveActiveInclusion H)
  let c := Equiv.cast (congrArg (fun K => Configuration K)
    (positiveActiveGraph_map_subtype H))
  have hbase := positiveFKLaw_isolatedExtension_map_boundary_pullback
    (positiveActiveGraph H) (positiveActiveInclusion H) hq hp hp1 ξ
  have hcast :
      (positiveFKLaw
        ((positiveActiveGraph H).map (positiveActiveInclusion H)) q p hq hp hp1 ξ).map c =
      positiveFKLaw H q p hq hp hp1 ξ := by
    exact positiveFKLaw_eq_of_graph_eq (positiveActiveGraph_map_subtype H)
      hq hp hp1 ξ
  calc
    _ = ((positiveFKLaw (positiveActiveGraph H) q p hq hp hp1
        (isolatedExtensionPullbackBoundary (positiveActiveInclusion H) ξ)).map e).map c := by
          rw [PMF.map_comp]
          rfl
    _ = positiveFKLaw H q p hq hp hp1 ξ := by rw [hbase, hcast]

end
end PottsContinuity.DualityExt
