module

public import PottsContinuity.PlanarMixed.CutExteriorReveals
public import PottsContinuity.PD.FK.Graph

@[expose] public section

namespace PottsContinuity.Push
open PlanarMixed PD.FK

/-- Every edge from an unseeded component into the closed seeded exterior
attaches at the cut itself. This holds for arbitrary graphs and cut sets. -/
theorem cutComponent_attachment_mem_cut {V : Type*}
    (G : SimpleGraph V) (cut seeds : Set V) {x y : V}
    (hx : x ∉ closedCutExterior G cut seeds)
    (hy : y ∈ closedCutExterior G cut seeds) (hxy : G.Adj x y) : y ∈ cut := by
  rcases hy with hy | hy
  · by_contra hycut
    have hxcut : x ∉ cut := fun h => hx (Or.inr h)
    obtain ⟨a,ha,p,hp⟩ := hy
    apply hx
    left
    refine ⟨a,ha,p.concat hxy.symm,?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hp z hz
    · exact hxcut
  · exact hy

end PottsContinuity.Push
