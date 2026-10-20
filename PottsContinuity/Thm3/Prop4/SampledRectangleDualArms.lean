module

public import PottsContinuity.PlanarTopology.SampledClosedRowsScreen
public import PottsContinuity.Thm3.Prop4.FiniteDualArmsCorrelation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Dual arms retaining a closed sampled original bond at every step

Unlike an agreeing whole-plane completion, this carrier adds no unsampled
side-cap bonds. The two arms are walks in the same actual sampled graph.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- Closing sampled original edges retains every actual sampled dual adjacency. -/
theorem sampled_rectangle_closed_dual_antitone (a : LatticeVertex) (w h : ℕ) :
    Antitone (PlanarTopology.rectangleSampledClosedDualGraph a w h) := by
  intro A C hAC s t hst
  obtain ⟨e,he,hends⟩ := hst
  exact ⟨e,fun heA => he (hAC heA),hends⟩

/-- Two actual dual arms in the literal sampled rectangle, with arbitrary
specified endpoints and supports and no exterior-completion bonds. -/
def sampledRectangleDualArmsEvent (a : LatticeVertex) (w h : ℕ)
    (F G L U : Set LatticeVertex) (P Q : LatticeVertex → Prop) :
    Set (Configuration (rectangleGraph a w h)) :=
  {A | ∃ f ∈ F, ∃ g ∈ G, ∃ s ∈ L, ∃ t ∈ U,
    ∃ minus : (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Walk s f,
    ∃ plus : (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Walk g t,
      (∀ z ∈ minus.support, P z) ∧ (∀ z ∈ plus.support, Q z)}

/-- The sampled-arm event persists when any original sampled edges are closed. -/
theorem isLowerSet_sampledRectangleDualArmsEvent (a : LatticeVertex) (w h : ℕ)
    (F G L U : Set LatticeVertex) (P Q : LatticeVertex → Prop) :
    IsLowerSet (sampledRectangleDualArmsEvent a w h F G L U P Q) := by
  rintro A C hCA ⟨f,hf,g,hg,s,hs,t,ht,minus,plus,hm,hp⟩
  let hle := sampled_rectangle_closed_dual_antitone a w h hCA
  refine ⟨f,hf,g,hg,s,hs,t,ht,minus.mapLe hle,plus.mapLe hle,?_,?_⟩
  · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hm
  · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hp

end
end PottsContinuity.Thm3.Prop4
