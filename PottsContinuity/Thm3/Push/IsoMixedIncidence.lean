module

public import PottsContinuity.PD.FK.Isomorphism
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Literal incidence with both a recorded and an unrecorded bond commutes
with any graph relabeling, on the full original vertex carriers. -/
theorem mixed_incidence_configurationIso_iff
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (R : Configuration G) (u : V) :
    (∃ f ∈ configurationIso e R, ∃ g : H.edgeSet,
      g ∉ configurationIso e R ∧ e u ∈ f.val ∧ e u ∈ g.val) ↔
    (∃ f ∈ R, ∃ g : G.edgeSet, g ∉ R ∧ u ∈ f.val ∧ u ∈ g.val) := by
  classical
  have hmem (f : G.edgeSet) :
      e u ∈ (configurationIsoEdgeEquiv e f).val ↔ u ∈ f.val := by
    change e u ∈ Sym2.map e f.val ↔ u ∈ f.val
    rw [Sym2.mem_map]
    constructor
    · rintro ⟨v,hv,hvu⟩
      exact e.injective hvu ▸ hv
    · intro hu
      exact ⟨u,hu,rfl⟩
  constructor
  · rintro ⟨f,hf,g,hg,huf,hug⟩
    obtain ⟨f,rfl⟩ := (configurationIsoEdgeEquiv e).surjective f
    obtain ⟨g,rfl⟩ := (configurationIsoEdgeEquiv e).surjective g
    refine ⟨f,?_,g,?_,(hmem f).mp huf,(hmem g).mp hug⟩
    · exact Finset.mem_map.mp hf |>.elim fun a ha =>
        (configurationIsoEdgeEquiv e).injective ha.2 ▸ ha.1
    · intro hg'
      exact hg (Finset.mem_map.mpr ⟨g,hg',rfl⟩)
  · rintro ⟨f,hf,g,hg,huf,hug⟩
    refine ⟨configurationIsoEdgeEquiv e f,Finset.mem_map.mpr ⟨f,hf,rfl⟩,
      configurationIsoEdgeEquiv e g,?_,(hmem f).mpr huf,(hmem g).mpr hug⟩
    intro hg'
    obtain ⟨g',hg',heq⟩ := Finset.mem_map.mp hg'
    exact hg ((configurationIsoEdgeEquiv e).injective heq ▸ hg')

end
end PottsContinuity.Push
