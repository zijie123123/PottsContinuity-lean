module

public import PottsContinuity.Thm3.Prop4.TubeRevealedEdges

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Restriction to the induced edge mask preserves any walk already confined
to its vertices, and every vertex of the resulting walk is an original one. -/
theorem masked_walk_of_confined {V : Type*} [Finite V] (G : SimpleGraph V)
    (B : Configuration G) (S : Set V) {u v : V}
    (p : (openGraph G B).Walk u v) (hp : ∀ z ∈ p.support, z ∈ S) :
    ∃ q : (openGraph G (RSW.inducedConfigurationErasure S B)).Walk u v,
      ∀ z ∈ q.support, z ∈ p.support := by
  classical
  let f : (openGraph G B).induce S →g openGraph G (RSW.inducedConfigurationErasure S B) :=
    ⟨Subtype.val,fun {x y} hxy =>
      (RSW.openGraph_inducedConfigurationErasure_adj S B x.val y.val).mpr
        ⟨hxy,x.property,y.property⟩⟩
  refine ⟨(p.induce S hp).map f,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
  rw [p.support_induce hp,List.mem_attachWith] at hx
  exact hx

end
end PottsContinuity.Thm3.Prop4
