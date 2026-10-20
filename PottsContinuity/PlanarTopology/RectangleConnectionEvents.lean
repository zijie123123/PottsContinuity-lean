module

public import PottsContinuity.BD12.TwoBlockConnectivity
public import PottsContinuity.BD12.RectangleOpenGraphs
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

/-- Actual sampled connectivity between two vertex sets inside the finite
induced rectangle, retaining all isolated vertices and original bonds. -/
def rectangleConnectionEvent (a : LatticeVertex) (w h : ℕ) (S T : Set LatticeVertex) :
    Set LatticeConfiguration :=
  embeddedRestriction (rectangleGraph a w h) (frozenEdgeEmbedding (latticeRectangle a w h)) ⁻¹'
    arcsConnectionEvent (rectangleGraph a w h) (Subtype.val ⁻¹' S) (Subtype.val ⁻¹' T)

theorem rectangleConnectionEvent_isCylinder (a : LatticeVertex) (w h : ℕ) (S T : Set LatticeVertex) :
    IsCylinder (rectangleConnectionEvent a w h S T) := embeddedRestriction_isCylinder _ _ _

theorem rectangleConnectionEvent_measurableSet (a : LatticeVertex) (w h : ℕ) (S T : Set LatticeVertex) :
    MeasurableSet (rectangleConnectionEvent a w h S T) :=
  (rectangleConnectionEvent_isCylinder a w h S T).measurableSet

theorem rectangleConnectionEvent_isUpperSet (a : LatticeVertex) (w h : ℕ) (S T : Set LatticeVertex) :
    IsUpperSet (rectangleConnectionEvent a w h S T) := by
  intro ω η hωη hω
  exact arcsConnectionEvent_isUpperSet _ _ (embeddedRestriction_monotone _ _ hωη) hω

theorem rectangleConnectionEvent_iff (a : LatticeVertex) (w h : ℕ)
    (S T : Set LatticeVertex) (ω : LatticeConfiguration) :
    ω ∈ rectangleConnectionEvent a w h S T ↔
      ∃ u : RectangleVertex a w h, u.val ∈ S ∧
        ∃ v : RectangleVertex a w h, v.val ∈ T ∧
          ((PD.rcInfiniteOpenGraph ω).induce (latticeRectangle a w h : Set LatticeVertex)).Reachable u v := by
  have hg := embeddedRestriction_domainGraph (latticeRectangle a w h) ω
  change openGraph (rectangleGraph a w h)
    (embeddedRestriction _ (frozenEdgeEmbedding (latticeRectangle a w h)) ω) = _ at hg
  change (∃ u : RectangleVertex a w h, u.val ∈ S ∧
    ∃ v : RectangleVertex a w h, v.val ∈ T ∧ (openGraph _ _).Reachable u v) ↔ _
  rw [hg]

theorem rectangleConnectionEvent_mono (a : LatticeVertex) (w h : ℕ)
    {S S' T T' : Set LatticeVertex} (hS : S ⊆ S') (hT : T ⊆ T') :
    rectangleConnectionEvent a w h S T ⊆ rectangleConnectionEvent a w h S' T' := by
  rintro ω ⟨u,hu,v,hv,hconn⟩
  exact ⟨u,hS hu,v,hT hv,hconn⟩

theorem rectangleConnectionEvent_eq_univ_of_common_vertex (a : LatticeVertex) (w h : ℕ)
    (S T : Set LatticeVertex) (u : RectangleVertex a w h) (huS : u.val ∈ S) (huT : u.val ∈ T) :
    rectangleConnectionEvent a w h S T = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  exact (rectangleConnectionEvent_iff a w h S T ω).mpr ⟨u,huS,u,huT,SimpleGraph.Reachable.refl u⟩

end
end PottsContinuity.PlanarTopology
