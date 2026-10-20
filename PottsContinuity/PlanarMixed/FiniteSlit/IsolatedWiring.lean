module

public import PottsContinuity.PlanarMixed.FiniteSlit.BoundaryIsolation
public import PottsContinuity.PD.FK.IsolatedBoundaryLaw

/-! Removing the irrelevant exterior wiring on isolated reflected vertices.
The normalized finite law depends only on the boundary relation at vertices
incident to sampled edges. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12
noncomputable section

/-- Boundary relations need agree only on vertices incident to a graph edge.
All remaining vertices can be removed by the exact isolated-extension law. -/
theorem law_eq_of_boundary_agrees_on_incident
    {V : Type*} [Finite V] (G : SimpleGraph V) (θ : Parameters)
    (ξ η : BoundaryCondition V)
    (h : ∀ u v, (∃ z, G.Adj u z) → (∃ z, G.Adj v z) →
      (ξ.partition.r u v ↔ η.partition.r u v)) : law G θ ξ = law G θ η := by
  let S : Set V := {u | ∃ z, G.Adj u z}
  let H := G.induce S
  let i : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hG : H.map i = G := by
    ext u v
    constructor
    · intro huv
      obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
      exact hab
    · intro huv
      exact (SimpleGraph.map_adj _ _ _ _).mpr
        ⟨⟨u,⟨v,huv⟩⟩,⟨v,⟨u,huv.symm⟩⟩,huv,rfl,rfl⟩
  have hpart : (isolatedExtensionPullbackBoundary i ξ).partition =
      (isolatedExtensionPullbackBoundary i η).partition := by
    apply Setoid.ext
    intro u v
    exact h u.val v.val u.property v.property
  have hlaw := law_eq_of_boundary_partition_eq (G := H) θ _ _ hpart
  have hm := congrArg (fun ρ => ρ.map (isolatedExtensionConfigurationEquiv H i)) hlaw
  rw [law_isolatedExtension_map_boundary_pullback,
    law_isolatedExtension_map_boundary_pullback] at hm
  change law (H.map i) θ ξ = law (H.map i) θ η at hm
  rw [hG] at hm
  exact hm

/-- Joining arbitrary isolated vertices into an existing wired set does not
change any sampled-configuration probability, even when the set is empty. -/
theorem law_wired_union_isolated_eq
    {V : Type*} [Finite V] (G : SimpleGraph V) (θ : Parameters) (A I : Set V)
    (hI : ∀ u ∈ I, ∀ v, ¬ G.Adj u v) :
    law G θ (BoundaryCondition.wired (A ∪ I)) = law G θ (BoundaryCondition.wired A) := by
  apply law_eq_of_boundary_agrees_on_incident G θ
  intro u v hu hv
  have huI : u ∉ I := by rintro hi; obtain ⟨z,hz⟩ := hu; exact hI u hi z hz
  have hvI : v ∉ I := by rintro hi; obtain ⟨z,hz⟩ := hv; exact hI v hi z hz
  rw [BoundaryCondition.wired_rel,BoundaryCondition.wired_rel]
  simp only [Set.mem_union,huI,hvI,or_false]

/-- These extra rectangle-exterior faces are isolated in the actual dual graph. -/
def irrelevantExterior (M : ℕ) (x : ℤ) : Set (Vertex M x) :=
  {u | u.val.1 = x-(M : ℤ) ∨ (u.val.2 = 0 ∧ u ∉ dualBottom M x)}

/-- The rectangle may wire precisely these additional exterior faces into
B' and K'; their complete normalized law is the stated canonical dual law. -/
theorem dual_law_extra_exterior_wiring_eq (θ : Parameters)
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) :
    law (dualGraph M x y) θ
      (BoundaryCondition.wired ((dualBottom M x ∪ dualRay M x y) ∪ irrelevantExterior M x)) =
    law (dualGraph M x y) θ (dualBoundary M x y) := by
  apply law_wired_union_isolated_eq
  intro u hu
  rcases hu with hl | hb
  · exact dualGraph_left_column_isolated M x y hM u hl
  · exact dualGraph_unmarked_bottom_isolated M x y hM u hb.1 hb.2

end
end PottsContinuity.PlanarMixed.FiniteSlit
