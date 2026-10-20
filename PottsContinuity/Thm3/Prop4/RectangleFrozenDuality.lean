module

public import PottsContinuity.Thm3.Prop4.FiniteFilterEquiv
public import PottsContinuity.DualityExt.RectangleResults
public import PottsContinuity.PD.FK.ConditionalLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Exact dual law after opening every revealed original bond

The crossing dual bonds are conditioned closed. The ambient dual boundary
is the proved rectangle exterior wiring; no boundary class is guessed.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.Duality
noncomputable section

local instance frozenDualityPrimalEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance frozenDualityDualEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDualGraph a w h).edgeSet := Classical.decEq _

/-- The unique crossing bond correspondence on actual primal and dual graph edges. -/
def rectangleCrossingEdgeEquiv (a : LatticeVertex) (w h : ℕ) :
    (rectangleGraph a w h).edgeSet ≃ (rectangleDualGraph a w h).edgeSet :=
  (rectanglePrimalDualEdgeEquiv a w h).trans (rectangleDualGraphEdgeEquiv a w h)

/-- The actual dual bonds crossing a prescribed set of original primal bonds. -/
def rectangleCrossedEdges (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) : Configuration (rectangleDualGraph a w h) :=
  R.map (rectangleCrossingEdgeEquiv a w h).toEmbedding

/-- The state of each actual crossing dual bond is the complementary original state. -/
theorem rectangle_crossing_edge_mem_dual_iff (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (e : (rectangleGraph a w h).edgeSet) :
    rectangleCrossingEdgeEquiv a w h e ∈ rectanglePrimalDualConfigurationEquiv a w h A ↔ e ∉ A :=
  mem_rectanglePrimalDualConfigurationEquiv a w h A (rectanglePrimalDualEdgeEquiv a w h e)

/-- Fixing every revealed primal bond open is exactly fixing every crossed
dual bond closed, with every other sampled bond still random. -/
theorem rectangle_all_open_state_iff_dual_closed (a : LatticeVertex) (w h : ℕ)
    (R A : Configuration (rectangleGraph a w h)) :
    A ∈ frozenStateEvent R ⟨R,Finset.Subset.refl R⟩ ↔
      rectanglePrimalDualConfigurationEquiv a w h A ∈
        frozenStateEvent (rectangleCrossedEdges a w h R) ⟨∅,Finset.empty_subset _⟩ := by
  classical
  change A ∩ R = R ↔
    rectanglePrimalDualConfigurationEquiv a w h A ∩ rectangleCrossedEdges a w h R = ∅
  rw [Finset.inter_eq_right,← Finset.disjoint_iff_inter_eq_empty]
  constructor
  · intro hRA
    apply Finset.disjoint_left.mpr
    intro d hd hdR
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hdR
    exact ((rectangle_crossing_edge_mem_dual_iff a w h A e).mp hd) (hRA he)
  · intro hdisj e he
    by_contra heA
    exact Finset.disjoint_left.mp hdisj
      ((rectangle_crossing_edge_mem_dual_iff a w h A e).mpr heA)
      (Finset.mem_map.mpr ⟨e,he,rfl⟩)

/-- Rectangle free-to-wired duality transports the full original conditional
law at the actual all-open revealed state to the actual closed-dual-state law. -/
theorem rectangle_free_all_open_filter_map_dual_closed (θ : Parameters)
    (a : LatticeVertex) (w h : ℕ) (R : Configuration (rectangleGraph a w h)) :
    ((law (rectangleGraph a w h) θ (BoundaryCondition.free ∅)).filter
      (frozenStateEvent R ⟨R,Finset.Subset.refl R⟩)
      (frozenStateEvent_support θ (BoundaryCondition.free ∅) R ⟨R,Finset.Subset.refl R⟩)).map
        (rectanglePrimalDualConfigurationEquiv a w h) =
      (law (rectangleDualGraph a w h) (dualParameters θ) (rectangleDualBoundaryCondition a w h)).filter
        (frozenStateEvent (rectangleCrossedEdges a w h R) ⟨∅,Finset.empty_subset _⟩)
        (frozenStateEvent_support (dualParameters θ) (rectangleDualBoundaryCondition a w h)
          (rectangleCrossedEdges a w h R) ⟨∅,Finset.empty_subset _⟩) := by
  have hEvent : (rectanglePrimalDualConfigurationEquiv a w h).symm ⁻¹'
      frozenStateEvent R ⟨R,Finset.Subset.refl R⟩ =
      frozenStateEvent (rectangleCrossedEdges a w h R) ⟨∅,Finset.empty_subset _⟩ := by
    ext B
    simp only [Set.mem_preimage]
    rw [rectangle_all_open_state_iff_dual_closed,Equiv.apply_symm_apply]
  have h := finite_pmf_filter_map_equiv (law (rectangleGraph a w h) θ (BoundaryCondition.free ∅))
    (rectanglePrimalDualConfigurationEquiv a w h) _
    (frozenStateEvent_support θ (BoundaryCondition.free ∅) R ⟨R,Finset.Subset.refl R⟩)
  simpa only [DualityExt.rectangle_freeLaw_map_dual_wired,hEvent] using h

end
end PottsContinuity.Thm3.Prop4
