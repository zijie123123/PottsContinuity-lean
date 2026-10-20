module

public import PottsContinuity.Thm3.Prop4.FKCRectangleDualLift
public import PottsContinuity.BD12.RectangleConfinedWalk
public import PottsContinuity.FKC.FiniteFK.RectangleEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Literal original-state restriction to the shared finite rectangle

Restriction reads each actual original bond once. Finite crossings use actual
open paths, and therefore transport to the frozen whole-plane rectangle event
without adding wired-boundary connections.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- Every FKC rectangle edge embeds as its original unordered lattice edge. -/
def fkcRectangleOriginalEdgeEmbedding (a : ℤ × ℤ) (w h : ℕ) :
    (FKC.rectangleGraph a w h).edgeSet ↪ PD.squareLattice.edgeSet where
  toFun e := fkcOriginalEdgeEquiv (FKC.FiniteFK.rectanglePrimalEdgeToSquareEdge a w h e)
  inj' := fkcOriginalEdgeEquiv.injective.comp
    (FKC.FiniteFK.rectanglePrimalEdgeToSquareEdge_injective a w h)

/-- Restrict the actual original states, retaining the finite graph's whole vertex carrier. -/
def fkcRectangleRestriction (a : ℤ × ℤ) (w h : ℕ) (ω : LatticeConfiguration) :
    FKC.FiniteFK.Configuration (FKC.rectangleGraph a w h) :=
  BD12.embeddedRestriction (FKC.rectangleGraph a w h) (fkcRectangleOriginalEdgeEmbedding a w h) ω

/-- The finite configuration agrees exactly with every original sampled state. -/
theorem fkcRectangleRestriction_state (a : ℤ × ℤ) (w h : ℕ) (ω : LatticeConfiguration)
    (e : FKC.FiniteFK.rectanglePrimalEdgeCarrier a w h) :
    ω (fkcOriginalEdgeEquiv (FKC.FiniteFK.rectanglePrimalEdgeToSquareEdge a w h e)) =
      FKC.FiniteFK.rectangleOpenExtensionState (fkcRectangleRestriction a w h ω) e := by
  apply Bool.eq_iff_iff.mpr
  rw [FKC.FiniteFK.rectangleOpenExtensionState_eq_true_iff]
  exact (BD12.mem_embeddedRestriction (FKC.rectangleGraph a w h)
    (fkcRectangleOriginalEdgeEmbedding a w h) ω e).symm

/-- A finite open rectangle edge is an actual whole-plane open edge. -/
def fkcRectanglePrimalOriginalHom (a : ℤ × ℤ) (w h : ℕ) (ω : LatticeConfiguration) :
    FKC.FiniteFK.openGraph (FKC.rectangleGraph a w h) (fkcRectangleRestriction a w h ω) →g
      PD.rcInfiniteOpenGraph ω where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    obtain ⟨e,he,hstate⟩ := (BD12.embeddedRestriction_openGraph_adj
      (FKC.rectangleGraph a w h) (fkcRectangleOriginalEdgeEmbedding a w h) ω u v).mp huv
    have hG := (FKC.rectangleGraph a w h).mem_edgeSet.mp (he ▸ e.property)
    have hadj : PD.squareLattice.Adj u.val v.val :=
      fkcOriginalLatticeIso.toHom.map_adj ((FKC.rectangleGraph_adj_iff _ _ _ _ _).mp hG)
    have hval : (fkcRectangleOriginalEdgeEmbedding a w h e).val = s(u.val,v.val) := by
      rw [show (fkcRectangleOriginalEdgeEmbedding a w h e).val =
        (FKC.FiniteFK.rectanglePrimalEdgeToSquareEdge a w h e).val from fkcOriginalEdgeEquiv_val _]
      change Sym2.map Subtype.val e.val = s(u.val,v.val)
      rw [he]
      rfl
    have heq : fkcRectangleOriginalEdgeEmbedding a w h e =
        ⟨s(u.val,v.val),PD.squareLattice.mem_edgeSet.mpr hadj⟩ := Subtype.ext hval
    rw [PD.rcInfiniteOpenGraph,SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨PD.squareLattice.mem_edgeSet.mpr hadj,?_⟩,hadj.ne⟩
    rwa [heq] at hstate

/-- An actual finite crossing is the original-state confined rectangle crossing. -/
theorem fkc_rectangle_crossing_original (a : ℤ × ℤ) (w h : ℕ) (ω : LatticeConfiguration)
    (hcross : fkcRectangleRestriction a w h ω ∈ FKC.FiniteFK.rectangleHorizontalCrossingEvent a w h) :
    ω ∈ BD12.horizontalRectangle a w h := by
  obtain ⟨u,v,hu,hv,⟨p⟩⟩ := hcross
  let f := fkcRectanglePrimalOriginalHom a w h ω
  apply (BD12.horizontalRectangle_iff_confined_open_walk a w h ω).mpr
  refine ⟨u.val,v.val,p.map f,(Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hv).2,?_⟩
  intro z hz
  have hs := SimpleGraph.Walk.support_map f p
  have hz' : z ∈ p.support.map (fun x => x.val) :=
    Eq.mp (congrArg (fun xs : List (ℤ × ℤ) => z ∈ xs) hs) hz
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz'
  exact x.property

end
end PottsContinuity.Thm3.Prop4
