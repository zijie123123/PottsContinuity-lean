module

public import PottsContinuity.Thm3.Prop4.ArcIsolationLocality
public import PottsContinuity.PD.FK.IsolatedExtension
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Exact isolation-event transport when all exterior edges are closed -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
variable {V U : Type*} {G : SimpleGraph V}

/-- Every walk starting in the embedded graph lifts, with its full vertex support. -/
theorem walk_lift_from_embedded_graph (f : V ↪ U) {u v : U} (p : (G.map f).Walk u v)
    (x : V) (hx : f x = u) :
    ∃ y : V, f y = v ∧ ∃ q : G.Walk x y, q.support.map f = p.support := by
  have hwalk : ∀ {a b : U} (r : (G.map f).Walk a b), ∀ z : V, f z = a →
      ∃ y : V, f y = b ∧ ∃ q : G.Walk z y, q.support.map f = r.support := by
    intro a b r
    induction r with
    | nil =>
      intro z hz
      refine ⟨z,hz,.nil,?_⟩
      change [f z] = [_]
      rw [hz]
    | @cons a b c hab r ih =>
      intro z hz
      obtain ⟨a',b',ha'b',ha',hb'⟩ := (SimpleGraph.map_adj f G a b).mp hab
      have ha'z : a' = z := f.injective (ha'.trans hz.symm)
      subst a'
      obtain ⟨y,hy,q,hq⟩ := ih b' hb'
      refine ⟨y,hy,.cons ha'b' q,?_⟩
      change f z :: q.support.map f = a :: r.support
      rw [hz,hq]
  exact hwalk p x hx

/-- Closed exterior vertices add no paths or no-escape failures from an embedded root. -/
theorem graphArcIsolation_map_iff (f : V ↪ U) (D W : Set U)
    (hW : W ⊆ Set.range f) (x : V) :
    graphArcIsolation (G.map f) D W (f x) ↔
      graphArcIsolation G (f ⁻¹' D) (f ⁻¹' W) x := by
  let hom := (SimpleGraph.Embedding.map f G).toHom
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · obtain ⟨y,hy,hxy⟩ := h.1
      obtain ⟨z,hz⟩ := hW hy
      refine ⟨z,?_,?_⟩
      · change f z ∈ W
        rw [hz]
        exact hy
      · have hreach : (G.map f).Reachable (f x) (f z) := by rw [hz]; exact hxy
        exact (PD.FK.reachable_isolatedExtension_apply G f x z).mp hreach
    · intro y hy p
      obtain ⟨z,hz,hzW⟩ := h.2 (f y) hy (p.map hom)
      have hs : (p.map hom).support = p.support.map f := SimpleGraph.Walk.support_map hom p
      have hz' : z ∈ p.support.map f := hs ▸ hz
      obtain ⟨a,ha,haz⟩ := List.mem_map.mp hz'
      exact ⟨a,ha,by change f a ∈ W; rw [haz]; exact hzW⟩
  · intro h
    refine ⟨?_,?_⟩
    · obtain ⟨y,hy,hxy⟩ := h.1
      exact ⟨f y,hy,hxy.map hom⟩
    · intro y hy p
      obtain ⟨z,hz,q,hq⟩ := walk_lift_from_embedded_graph f p x rfl
      have hzD : z ∉ f ⁻¹' D := by
        change f z ∉ D
        rw [hz]
        exact hy
      obtain ⟨a,ha,haW⟩ := h.2 z hzD q
      refine ⟨f a,?_,haW⟩
      rw [← hq]
      exact List.mem_map.mpr ⟨a,ha,rfl⟩

end PottsContinuity.Thm3.Prop4
