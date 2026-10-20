-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/EdgeRestrictionReachableClosure.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.EdgeRestriction
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- At a vertex away from the exceptional set, uniform membership status of
all incident original edges propagates any known retained incident edge to all
original neighbors. -/
theorem edgeRestriction_adj_of_uniform_incident_status
    {V : Type*} (G : SimpleGraph V) (R : Configuration G) (B : Set V)
    (huniform : ∀ v, v ∉ B → ∀ e f : G.edgeSet,
      v ∈ e.val → v ∈ f.val → (e ∈ R ↔ f ∈ R))
    {v w : V} (hvB : v ∉ B) (e : G.edgeSet)
    (heV : v ∈ e.val) (heR : e ∉ R) (hvw : G.Adj v w) :
    (edgeRestriction G R).Adj v w := by
  let f : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.mpr hvw⟩
  have hfV : v ∈ f.val := (Sym2.mem_iff').2 (Or.inl rfl)
  have hfR : f ∉ R := by
    intro hf
    exact heR ((huniform v hvB e f heV hfV).mpr hf)
  have hfRestr : f.val ∈ (edgeRestriction G R).edgeSet := by
    rw [edgeRestriction_edgeSet]
    refine ⟨f.property, ?_⟩
    intro hopen
    exact hfR ((coe_mem_openEdges_iff G R f).mp hopen)
  exact (edgeRestriction G R).mem_edgeSet.mp (by simpa [f] using hfRestr)

end PottsContinuity.FKC.FiniteFK
