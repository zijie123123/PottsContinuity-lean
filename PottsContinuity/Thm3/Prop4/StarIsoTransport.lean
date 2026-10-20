module

public import PottsContinuity.Thm3.Prop4.VertexStarArms
public import PottsContinuity.PD.FK.Isomorphism

/-!
# Sampled star surgery under a graph isomorphism

The transported star consists of the same original incident bonds. Closure,
configuration inclusion and endpoint connectivity keep their literal meanings.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
variable {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
local instance starIsoSourceEdgeEq : DecidableEq G.edgeSet := Classical.decEq _
local instance starIsoTargetEdgeEq : DecidableEq H.edgeSet := Classical.decEq _

/-- Relabeling retains exactly all original incident sampled bonds. -/
theorem configurationIso_vertexStarEdges (e : G ≃g H) (z : V) :
    configurationIso e (vertexStarEdges G z) = vertexStarEdges H (e z) := by
  classical
  apply Finset.ext
  intro f
  change f ∈ (vertexStarEdges G z).map (configurationIsoEdgeEquiv e).toEmbedding ↔ _
  obtain ⟨g,rfl⟩ := (configurationIsoEdgeEquiv e).surjective f
  rw [Finset.mem_map_equiv,Equiv.symm_apply_apply,mem_vertexStarEdges,mem_vertexStarEdges]
  change z ∈ g.val ↔ e z ∈ Sym2.map e g.val
  constructor
  · intro hz
    exact Sym2.mem_map.mpr ⟨z,hz,rfl⟩
  · intro hz
    obtain ⟨x,hx,he⟩ := Sym2.mem_map.mp hz
    exact e.injective he ▸ hx

omit [Finite V] [Finite W] in
/-- Inclusion of sampled open original bonds is preserved by relabeling. -/
theorem configurationIso_monotone (e : G ≃g H) : Monotone (configurationIso e) := by
  intro A B hAB
  exact Finset.map_subset_map.mpr hAB

/-- Closing a sampled star commutes with graph relabeling, including corners. -/
theorem configurationIso_close_star (e : G ≃g H) (A : Configuration G) (z : V) :
    configurationIso e (A \ vertexStarEdges G z) =
      configurationIso e A \ vertexStarEdges H (e z) := by
  change (A \ vertexStarEdges G z).map (configurationIsoEdgeEquiv e).toEmbedding = _
  rw [Finset.map_sdiff]
  change configurationIso e A \ configurationIso e (vertexStarEdges G z) = _
  rw [configurationIso_vertexStarEdges]

end
end PottsContinuity.Thm3.Prop4
