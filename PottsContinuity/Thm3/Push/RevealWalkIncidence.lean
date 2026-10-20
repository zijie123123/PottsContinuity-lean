module

public import PottsContinuity.PD.FK.Graph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK

/-- Along a walk with no mixed recorded/unrecorded incidence, absence of
recorded bonds at its starting vertex propagates to every vertex. -/
theorem unrevealed_incidence_propagates_along_walk
    {V : Type*} (G : SimpleGraph V) (R : Configuration G) {s t : V} (p : G.Walk s t)
    (hno : ∀ u ∈ p.support, ¬ (∃ f ∈ R, ∃ g : G.edgeSet,
      g ∉ R ∧ u ∈ f.val ∧ u ∈ g.val))
    (hstart : ∀ f : G.edgeSet, s ∈ f.val → f ∉ R) :
    ∀ u ∈ p.support, ∀ f : G.edgeSet, u ∈ f.val → f ∉ R := by
  revert hno hstart
  induction p with
  | @nil a =>
    intro hno hstart u hu
    have heq : u=a := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hu
    subst u
    exact hstart
  | @cons a b c hab p ih =>
    intro hno hstart u hu
    let e : G.edgeSet := ⟨s(a,b),G.mem_edgeSet.mpr hab⟩
    have he : e ∉ R := hstart e (Sym2.mem_mk_left _ _)
    have hb : ∀ f : G.edgeSet, b ∈ f.val → f ∉ R := by
      intro f hbf hf
      exact hno b (List.mem_cons_of_mem a p.start_mem_support) ⟨f,hf,e,he,hbf,Sym2.mem_mk_right _ _⟩
    have htail : ∀ v ∈ p.support, ¬ (∃ f ∈ R, ∃ g : G.edgeSet,
        g ∉ R ∧ v ∈ f.val ∧ v ∈ g.val) := by
      intro v hv
      exact hno v (List.mem_cons_of_mem a hv)
    rcases (List.mem_cons.mp hu) with rfl | hu
    · exact hstart
    · exact ih htail hb u hu

end PottsContinuity.Push
