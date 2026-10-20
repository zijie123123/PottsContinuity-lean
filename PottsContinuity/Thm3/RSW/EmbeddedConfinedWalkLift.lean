module

public import PottsContinuity.Thm3.RSW.ThreeSideWalkExit

@[expose] public section

namespace PottsContinuity.RSW
noncomputable section

/-- A sampled walk confined to a graph embedding's actual image lifts to its
original graph, retaining all source constraints through the mapped trace. -/
theorem walk_lift_of_support_in_embedding_range
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G ↪g H)
    {u v : V} (p : H.Walk (f u) (f v))
    (hp : ∀ z ∈ p.support, z ∈ Set.range f) :
    ∃ q : G.Walk u v, ∀ z ∈ q.support, f z ∈ p.support := by
  let e := f.isoInduceRange
  let pI := p.induce (Set.range f) hp
  have hstart : e.symm ⟨f u,hp _ p.start_mem_support⟩ = u := by
    have hval : e u = ⟨f u,hp _ p.start_mem_support⟩ := Subtype.ext rfl
    rw [← hval]
    exact e.symm_apply_apply u
  have hend : e.symm ⟨f v,hp _ p.end_mem_support⟩ = v := by
    have hval : e v = ⟨f v,hp _ p.end_mem_support⟩ := Subtype.ext rfl
    rw [← hval]
    exact e.symm_apply_apply v
  let q := (pI.map e.symm.toHom).copy hstart hend
  have hsupport : pI.support.map Subtype.val = p.support := by
    have h := congrArg SimpleGraph.Walk.support (p.map_induce hp)
    simp only [SimpleGraph.Walk.support_map] at h
    change pI.support.map Subtype.val = p.support at h
    exact h
  refine ⟨q,?_⟩
  intro z hz
  change z ∈ ((pI.map e.symm.toHom).copy hstart hend).support at hz
  rw [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map,List.mem_map] at hz
  obtain ⟨w,hw,rfl⟩ := hz
  have he : f (e.symm w) = w.val := congrArg Subtype.val (e.apply_symm_apply w)
  change f (e.symm w) ∈ p.support
  rw [he,← hsupport]
  exact List.mem_map.mpr ⟨w,hw,rfl⟩

end
end PottsContinuity.RSW
