module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.Push

/-- A confined walk can be pulled back when every step between its support
vertices lifts. The ambient inclusion need not be a graph embedding: this
retains the distinction between a true dual graph and an induced face graph. -/
theorem exists_walk_pullback_support_steps {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    {u v : W} (p : H.Walk u v) (a b : V) (ha : f a=u) (hb : f b=v)
    (hsupport : ∀ z ∈ p.support, ∃ x, f x=z)
    (hsteps : ∀ x y : V, f x ∈ p.support → f y ∈ p.support → H.Adj (f x) (f y) → G.Adj x y) :
    ∃ r : G.Walk a b, ∀ x ∈ r.support, f x ∈ p.support := by
  revert hsteps hsupport
  revert a b
  induction p with
  | @nil u =>
    intro a b ha hb hsupport hsteps
    have hab : a=b := f.injective (ha.trans hb.symm)
    subst b
    refine ⟨.nil,?_⟩
    intro x hx
    have hxa : x=a := List.mem_singleton.mp hx
    subst x
    simpa only [ha] using (SimpleGraph.Walk.nil : H.Walk u u).start_mem_support
  | @cons u t v hut p ih =>
    intro a b ha hb hsupport hsteps
    have htmem : t ∈ (p.cons hut).support := List.mem_cons_of_mem _ p.start_mem_support
    obtain ⟨c,hc⟩ := hsupport t htmem
    have hs' : ∀ z ∈ p.support, ∃ x, f x=z := by
      intro z hz
      exact hsupport z (List.mem_cons_of_mem _ hz)
    have he' : ∀ x y : V, f x ∈ p.support → f y ∈ p.support →
        H.Adj (f x) (f y) → G.Adj x y := by
      intro x y hx hy hxy
      exact hsteps x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy) hxy
    obtain ⟨r,hr⟩ := ih c b hc hb hs' he'
    have hac : G.Adj a c := by
      apply hsteps a c
      · simpa only [ha] using (p.cons hut).start_mem_support
      · simpa only [hc] using htmem
      · simpa only [ha,hc] using hut
    refine ⟨r.cons hac,?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa only [ha] using (p.cons hut).start_mem_support
    · exact List.mem_cons_of_mem _ (hr x hx)

end PottsContinuity.Push
