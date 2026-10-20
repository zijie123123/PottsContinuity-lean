module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.Push

/-- A confined walk in the range of a graph embedding lifts to the original
sampled graph, preserving its entire vertex support. -/
theorem exists_walk_pullback_support {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (j : G ↪g H) {u v : V} (w : H.Walk (j u) (j v))
    (hw : ∀ z ∈ w.support, z ∈ Set.range j) :
    ∃ w' : G.Walk u v, ∀ z ∈ w'.support, j z ∈ w.support := by
  let iso := j.isoInduceRange
  let wi := w.induce (Set.range j) hw
  have hu : (⟨j u, hw _ w.start_mem_support⟩ : Set.range j) = iso u := by
    apply Subtype.ext
    rfl
  have hv : (⟨j v, hw _ w.end_mem_support⟩ : Set.range j) = iso v := by
    apply Subtype.ext
    rfl
  have hiu : iso.symm.toHom (⟨j u, hw _ w.start_mem_support⟩ : Set.range j) = u := by
    rw [hu]
    exact iso.symm_apply_apply u
  have hiv : iso.symm.toHom (⟨j v, hw _ w.end_mem_support⟩ : Set.range j) = v := by
    rw [hv]
    exact iso.symm_apply_apply v
  let wp := wi.map iso.symm.toHom
  let wr := wp.copy hiu hiv
  refine ⟨wr, ?_⟩
  intro z hz
  have hz' : z ∈ wp.support := by simpa only [wr, SimpleGraph.Walk.support_copy] using hz
  rw [SimpleGraph.Walk.support_map] at hz'
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz'
  have ht' : t.val ∈ w.support := by
    simpa only [wi, SimpleGraph.Walk.support_induce, List.mem_attachWith] using ht
  have heq : j (iso.symm.toHom t) = t.val := by
    have h := congrArg Subtype.val (iso.apply_symm_apply t)
    exact h
  simpa only [heq] using ht'

end PottsContinuity.Push
