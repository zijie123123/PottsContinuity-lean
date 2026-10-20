module

public import PottsContinuity.Thm3.Push.SideCollarBarrierTrace

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.FK.Medial PlanarMixed.FiniteSlit

/-- On original embedded source vertices the entire closed collar barrier
has exactly the source tip trace. No discarded auxiliary return can add a
new original source vertex. -/
theorem sideCollar_barrier_original_vertex_mem_trace
    (w h M : ℕ) (hNM : sideCollarSize w h ≤ M) (b y : ℤ)
    (q : squareLattice.Walk (b,0) (2,y))
    (p : squareLattice.Walk (b,0) (b,0))
    (hallowed : ∀ e ∈ p.edges, e ∈ slitBarrierEdges M 2 y b q)
    (u : RectangleVertex (0,0) w h)
    (hu : (sideCollarEmbedding w h u).val ∈ p.support) :
    (sideCollarEmbedding w h u).val ∈ q.support := by
  have hbounds := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
  simp only [zero_add] at hbounds
  have hN : (4:ℤ) ≤ (M:ℤ) := by dsimp [sideCollarSize] at hNM; omega
  rcases SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mp hu with hroot | ⟨e,he,hue⟩
  · exact hroot.symm ▸ q.start_mem_support
  · rcases hallowed e he with hq | hroot | ⟨htip,_⟩ | ⟨a,c,hac,hout⟩
    · exact SimpleGraph.Walk.mem_support_of_mem_edges hq hue
    · rw [hroot] at hue
      rcases Sym2.mem_iff'.mp hue with heq | heq
      · have hy := congrArg Prod.snd heq
        change u.val.2 = -1 at hy
        omega
      · exact heq.symm ▸ q.start_mem_support
    · rw [htip] at hue
      rcases Sym2.mem_iff'.mp hue with heq | heq
      · have hx := congrArg Prod.fst heq
        change u.val.1+2=1 at hx
        omega
      · exact heq.symm ▸ q.end_mem_support
    · rw [hac] at hue
      rcases Sym2.mem_iff'.mp hue with heq | heq <;>
        have hx := congrArg Prod.fst heq <;> have hy := congrArg Prod.snd heq <;>
        change u.val.1+2 = _ at hx <;> change u.val.2 = _ at hy <;>
        rcases hout with hcol | hbottom | htop | hleft | hright <;>
        dsimp [sideCollarSize] at hNM <;> omega

end PottsContinuity.Push
