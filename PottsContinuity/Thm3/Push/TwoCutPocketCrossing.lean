module

public import PottsContinuity.Thm3.Push.TwoCutPocketGeometry
public import PottsContinuity.PlanarTopology.BoundaryWalkClipping
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.Push
open PlanarMixed
noncomputable section

private theorem walk_avoiding_cut_stays_in_exterior {V : Type*}
    (G H : SimpleGraph V) (hHG : H ≤ G) (A seeds : Set V) {u v : V}
    (p : H.Walk u v) (hp : ∀ z ∈ p.support, z ∉ A)
    (hv : v ∈ closedCutExterior G A seeds) :
    ∀ z ∈ p.support, z ∈ closedCutExterior G A seeds := by
  induction p with
  | nil =>
    intro z hz
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hz
    subst z
    exact hv
  | @cons u t v hut p ih =>
    have htail := ih (fun z hz => hp z (List.mem_cons_of_mem _ hz)) hv
    have ht := htail t p.start_mem_support
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · by_contra hu
      have htA := cutComponent_attachment_mem_cut G A seeds hu ht (hHG hut)
      exact hp t (List.mem_cons_of_mem _ p.start_mem_support) htA
    · exact htail z hz

private theorem simple_walk_with_unique_cut_start_stays_in_exterior {V : Type*}
    (G H : SimpleGraph V) (hHG : H ≤ G) (A seeds : Set V) {u v : V}
    (p : H.Walk u v) (hpath : p.IsPath) (hu : u ∈ closedCutExterior G A seeds)
    (hv : v ∈ closedCutExterior G A seeds)
    (hunique : ∀ z ∈ p.support, z ∈ A → z = u) :
    ∀ z ∈ p.support, z ∈ closedCutExterior G A seeds := by
  cases p with
  | nil => simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using fun z (hz : z = u) => hz ▸ hu
  | @cons u t v hut p =>
    have hnot : u ∉ p.support := (SimpleGraph.Walk.cons_isPath_iff _ _).mp hpath |>.2
    have havoid : ∀ z ∈ p.support, z ∉ A := by
      intro z hz hzA
      have he := hunique z (List.mem_cons_of_mem _ hz) hzA
      exact hnot (he ▸ hz)
    have htail := walk_avoiding_cut_stays_in_exterior G H hHG A seeds p havoid hv
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hu
    · exact htail z hz

/-- The confined sampled segment is retained on the original carrier when
its geometry is checked through an injective graph map. -/
theorem twoCutPockets_crossing_segment_map {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : H →g G) (hf : Function.Injective f)
    (A C seeds : Set V) (hAC : A ⊆ closedCutExterior G C seeds)
    (hCA : C ⊆ closedCutExterior G A seeds)
    {u v : W} (p : H.Walk u v) (hu : f u ∈ A) (hv : f v ∈ C) :
    ∃ a, f a ∈ A ∧ ∃ b, f b ∈ C ∧ ∃ q : H.Walk a b,
      ∀ z ∈ q.support, f z ∈ closedCutExterior G A seeds ∩ closedCutExterior G C seeds := by
  classical
  obtain ⟨a,ha,b,hb,q,_,hA,hC⟩ := PlanarTopology.walk_subwalk_between_sets p
    (f ⁻¹' A) (f ⁻¹' C) hu hv
  let Q := q.toPath
  have hQs : ∀ z ∈ Q.val.support, z ∈ q.support := q.support_toPath_subset_support
  have hleft := simple_walk_with_unique_cut_start_stays_in_exterior G G le_rfl A seeds
    (Q.val.map f) (Q.property.map hf) (Or.inr ha) (hCA hb) (by
      intro z hz hzA
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
      exact congrArg f (hA t (hQs t ht) hzA))
  have hright := simple_walk_with_unique_cut_start_stays_in_exterior G G le_rfl C seeds
    ((Q.val.map f).reverse) ((Q.property.map hf).reverse) (Or.inr hb) (hAC ha) (by
      intro z hz hzC
      rw [SimpleGraph.Walk.support_reverse,List.mem_reverse,SimpleGraph.Walk.support_map] at hz
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
      exact congrArg f (hC t (hQs t ht) hzC))
  refine ⟨a,ha,b,hb,Q.val,?_⟩
  intro z hz
  have hm : f z ∈ (Q.val.map f).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  exact ⟨hleft _ hm,hright _ (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hm)⟩

end
end PottsContinuity.Push
