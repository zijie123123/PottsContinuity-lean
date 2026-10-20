module

public import PottsContinuity.PD.Duality.CrossingDuality
public import PottsContinuity.PD.Duality.DualConfigurationBridge
public import PottsContinuity.PD.FK.Wiring
public import PottsContinuity.PD.RCInfinite.Cylinders
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Actual finite rectangle observables of whole-plane configurations

Restriction retains exactly the open sampled bonds. Crossing uses actual
connectivity on the induced rectangle, with no boundary identifications.
-/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance infiniteRectangleEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance infiniteRectangleEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Restrict a whole-plane state to the actual bonds of a finite embedded graph. -/
def embeddedRestriction (j : G.edgeSet ↪ PD.squareLattice.edgeSet)
    (ω : LatticeConfiguration) : Configuration G :=
  Finset.univ.filter (fun e => ω (j e) = true)

@[simp] theorem mem_embeddedRestriction (j : G.edgeSet ↪ PD.squareLattice.edgeSet)
    (ω : LatticeConfiguration) (e : G.edgeSet) :
    e ∈ embeddedRestriction G j ω ↔ ω (j e) = true := by
  classical
  simp [embeddedRestriction]

theorem embeddedRestriction_monotone (j : G.edgeSet ↪ PD.squareLattice.edgeSet) :
    Monotone (embeddedRestriction G j) := by
  intro ω η h e he
  rw [mem_embeddedRestriction] at he ⊢
  have hh := h (j e)
  rw [he] at hh
  exact top_le_iff.mp hh

/-- Every event of a finite embedded configuration is a cylinder event. -/
theorem embeddedRestriction_isCylinder (j : G.edgeSet ↪ PD.squareLattice.edgeSet)
    (S : Set (Configuration G)) : IsCylinder (embeddedRestriction G j ⁻¹' S) := by
  classical
  refine ⟨Finset.univ.map j, ?_⟩
  intro ω η h
  have heq : embeddedRestriction G j ω = embeddedRestriction G j η := by
    ext e
    simp only [mem_embeddedRestriction]
    rw [h (j e) (Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩)]
  change embeddedRestriction G j ω ∈ S ↔ embeddedRestriction G j η ∈ S
  rw [heq]

/-- Horizontal crossing of a whole-plane state inside the closed rectangle. -/
def horizontalRectangle (a : LatticeVertex) (w h : ℕ) : Set LatticeConfiguration :=
  embeddedRestriction (rectangleGraph a w h)
    (frozenEdgeEmbedding (latticeRectangle a w h)) ⁻¹' rectangleHorizontalCrossingEvent a w h

theorem horizontalRectangle_isCylinder (a : LatticeVertex) (w h : ℕ) :
    IsCylinder (horizontalRectangle a w h) :=
  embeddedRestriction_isCylinder _ _ _

theorem horizontalRectangle_isUpperSet (a : LatticeVertex) (w h : ℕ) :
    IsUpperSet (horizontalRectangle a w h) := by
  intro ω η hωη hω
  obtain ⟨u, v, hu, hv, huv⟩ := hω
  exact ⟨u, v, hu, hv, actualConnected_mono
    (embeddedRestriction_monotone _ _ hωη) huv⟩

/-- True dual bottom-to-top crossing, read from a whole-plane dual state. -/
def dualPortRectangle (a : LatticeVertex) (w h : ℕ) : Set LatticeConfiguration :=
  embeddedRestriction (rectangleDualGraph a w h)
    (rectangleDualEdgeToSquareEdge a w h) ⁻¹' rectangleDualBottomTopCrossingEvent a w h

theorem dualPortRectangle_isCylinder (a : LatticeVertex) (w h : ℕ) :
    IsCylinder (dualPortRectangle a w h) :=
  embeddedRestriction_isCylinder _ _ _

end
end PottsContinuity.BD12
