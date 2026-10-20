module

public import PottsContinuity.PD.FK.FrozenLimitBridge
public import PottsContinuity.PD.Duality.WholePlaneDualGraph
public import PottsContinuity.PlanarTopology.RectangleDualGraphBridge
public import PottsContinuity.FKC.FiniteFK.RectangleOpenExtension
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Order.CompletePartialOrder

/-!
# Faithful lifting of the finite complementary rectangle dual

The finite dual uses only sampled original bonds. Its walks lift to every
agreeing whole-plane extension, with the actual face labels and their support
preserved. No state of an unsampled exterior bond is prescribed.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial
noncomputable section

/-- Identity on vertices identifies the two genuine square-lattice graphs. -/
def fkcOriginalLatticeIso : FKC.squareLattice ≃g PD.FK.squareLattice where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro u v
    exact (PD.FK.squareLattice_adj_iff u v).trans (FKC.squareLattice_adj_iff u v).symm

/-- The original unordered edge is unchanged by this carrier equivalence. -/
def fkcOriginalEdgeEquiv : FKC.squareLattice.edgeSet ≃ PD.FK.squareLattice.edgeSet :=
  SimpleGraph.Iso.mapEdgeSet fkcOriginalLatticeIso

/-- Original edges remain the same unordered pair of integer vertices. -/
theorem fkcOriginalEdgeEquiv_val (e : FKC.squareLattice.edgeSet) :
    (fkcOriginalEdgeEquiv e).val = e.val := by
  change Sym2.map id e.val = e.val
  exact congrFun Sym2.map_id e.val

/-- Closed edges in the larger primal sample remain closed in the original sample. -/
theorem fkc_closedDualGraph_le_original_of_state_le (ω : LatticeConfiguration)
    (η : FKC.LatticeConfiguration) (hstate : ∀ e, ω (fkcOriginalEdgeEquiv e) ≤ η e) :
    FKC.Medial.wholePlaneClosedDualGraph η ≤ wholePlaneClosedDualGraph ω := by
  rintro u v ⟨b,hb,hends⟩
  refine ⟨PlanarTopology.pdBondOfFKC b,?_,?_⟩
  · have he : latticeBondEdge (PlanarTopology.pdBondOfFKC b) =
        fkcOriginalEdgeEquiv (FKC.Medial.latticeBondEdge b) := by
      apply Subtype.ext
      exact PlanarTopology.pdBondOfFKC_toSym2 b
    change ω (latticeBondEdge (PlanarTopology.pdBondOfFKC b)) = false
    rw [he]
    have hh := hstate (FKC.Medial.latticeBondEdge b)
    change η (FKC.Medial.latticeBondEdge b) = false at hb
    rw [hb] at hh
    exact le_antisymm hh bot_le
  · simpa only [PlanarTopology.pdBondOfFKC_faceBase] using hends

/-- The open-outside finite extension dominates every agreeing plane sample. -/
theorem fkc_rectangle_openOutside_dominates (a : ℤ × ℤ) (w h : ℕ)
    (A : FKC.FiniteFK.Configuration (FKC.rectangleGraph a w h))
    (ω : LatticeConfiguration)
    (hω : ∀ e : FKC.FiniteFK.rectanglePrimalEdgeCarrier a w h,
      ω (fkcOriginalEdgeEquiv (FKC.FiniteFK.rectanglePrimalEdgeToSquareEdge a w h e)) =
        FKC.FiniteFK.rectangleOpenExtensionState A e) :
    ∀ e, ω (fkcOriginalEdgeEquiv e) ≤ FKC.FiniteFK.rectangleOpenOutsideExtension a w h A e := by
  intro e
  by_cases he : ∃ f : FKC.FiniteFK.rectanglePrimalEdgeCarrier a w h,
      FKC.FiniteFK.rectanglePrimalEdgeToSquareEdge a w h f = e
  · obtain ⟨f,rfl⟩ := he
    rw [FKC.FiniteFK.rectangleOpenOutsideExtension_on_edge,hω f]
  · rw [FKC.FiniteFK.rectangleOpenOutsideExtension_outside_open a w h A e
      (fun f hf => he ⟨f,hf⟩)]
    exact le_top

/-- Every actual finite complementary edge remains dual-open in any agreeing extension. -/
def fkcRectangleDualOriginalHom (a : ℤ × ℤ) (w h : ℕ)
    (A : FKC.FiniteFK.Configuration (FKC.rectangleGraph a w h))
    (ω : LatticeConfiguration)
    (hω : ∀ e : FKC.FiniteFK.rectanglePrimalEdgeCarrier a w h,
      ω (fkcOriginalEdgeEquiv (FKC.FiniteFK.rectanglePrimalEdgeToSquareEdge a w h e)) =
        FKC.FiniteFK.rectangleOpenExtensionState A e) :
    FKC.FiniteFK.openGraph (FKC.FiniteFK.rectangleDualGraph a w h)
      (FKC.FiniteFK.rectangleDualConfiguration a w h A) →g wholePlaneClosedDualGraph ω where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    have hh := (FKC.FiniteFK.rectangleOpenOutsideDualGraphHom a w h A).map_adj huv
    exact fkc_closedDualGraph_le_original_of_state_le ω _
      (fkc_rectangle_openOutside_dominates a w h A ω hω) hh

/-- Lifting preserves every fixed condition on the integer face labels of the walk. -/
theorem fkc_rectangle_dual_walk_original (a : ℤ × ℤ) (w h : ℕ)
    (A : FKC.FiniteFK.Configuration (FKC.rectangleGraph a w h))
    (ω : LatticeConfiguration)
    (hω : ∀ e : FKC.FiniteFK.rectanglePrimalEdgeCarrier a w h,
      ω (fkcOriginalEdgeEquiv (FKC.FiniteFK.rectanglePrimalEdgeToSquareEdge a w h e)) =
        FKC.FiniteFK.rectangleOpenExtensionState A e)
    {u v : FKC.FiniteFK.RectangleDualVertex a w h}
    (p : (FKC.FiniteFK.openGraph (FKC.FiniteFK.rectangleDualGraph a w h)
      (FKC.FiniteFK.rectangleDualConfiguration a w h A)).Walk u v)
    (P : (ℤ × ℤ) → Prop) (hp : ∀ z ∈ p.support, P z.val) :
    ∃ q : (wholePlaneClosedDualGraph ω).Walk u.val v.val,
      ∀ z ∈ q.support, P z := by
  let f := fkcRectangleDualOriginalHom a w h A ω hω
  induction p with
  | @nil x =>
    refine ⟨.nil,?_⟩
    intro z hz
    have hz' : z = x.val := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hz
    subst z
    exact hp x (by simp only [SimpleGraph.Walk.support_nil,List.mem_singleton])
  | @cons u x v hux p ih =>
    obtain ⟨q,hq⟩ := ih (fun z hz => hp z (List.mem_cons_of_mem _ hz))
    refine ⟨.cons (f.map_adj hux) q,?_⟩
    intro z hz
    change z ∈ u.val :: q.support at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hp u (by change u ∈ u :: p.support; exact List.mem_cons_self)
    · exact hq z hz

end
end PottsContinuity.Thm3.Prop4
