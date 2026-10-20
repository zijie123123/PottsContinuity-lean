module

public import PottsContinuity.PlanarTopology.CentralTargetDualPorts
public import PottsContinuity.PD.Duality.Rectangle
public import PottsContinuity.PD.FK.Graph
public import PottsContinuity.FKC.FiniteFK.Isomorphism
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- The PD rectangle and the polygon's actual closure graph have identical
integer vertices and nearest-neighbour edges. This is a genuine graph isomorphism. -/
def rectangleDomainGraphIso (a : FKC.LatticeVertex) (w h : ℕ)
    (hw : 2 ≤ w) (hh : 2 ≤ h) (δ : FKC.PositiveMesh) :
    PD.FK.rectangleGraph a w h ≃g FKC.domainLatticeGraph δ
      ((rectangleLatticePolygon a w h (by omega) (by omega)).domain δ) where
  toFun u := ⟨u.val,(rectangleLatticePolygon_vertex_iff a w h hw hh δ u.val).mpr
    ((PD.FK.mem_latticeRectangle a u.val w h).mp u.property)⟩
  invFun v := ⟨v.val,(PD.FK.mem_latticeRectangle a v.val w h).mpr
    ((rectangleLatticePolygon_vertex_iff a w h hw hh δ v.val).mp v.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro u v
    rw [rectangleLatticePolygon_graph_adj_iff a w h hw hh δ,
      PD.FK.rectangleGraph_adj_iff,FKC.squareLattice_adj_iff,PD.FK.squareLattice_adj_iff]
    rfl

@[simp] theorem rectangleDomainGraphIso_val (a : FKC.LatticeVertex) (w h : ℕ)
    (hw : 2 ≤ w) (hh : 2 ≤ h) (δ : FKC.PositiveMesh)
    (u : PD.FK.RectangleVertex a w h) :
    (rectangleDomainGraphIso a w h hw hh δ u).val = u.val := rfl

/-- Equal geometric domains induce isomorphic actual domain graphs. -/
def domainGraphIsoOfEq (δ : FKC.PositiveMesh) {D E : Set ℂ} (h : D = E) :
    FKC.domainLatticeGraph δ D ≃g FKC.domainLatticeGraph δ E := by
  subst E
  exact SimpleGraph.Iso.refl

@[simp] theorem domainGraphIsoOfEq_val (δ : FKC.PositiveMesh) {D E : Set ℂ}
    (h : D = E) (u : FKC.DomainVertex δ D) : (domainGraphIsoOfEq δ h u).val = u.val := by
  subst E
  rfl

/-- Exact membership bridge to the PD rectangle's entire vertex carrier. -/
theorem centralTargetRectangle_vertex_mem_iff (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) (z : FKC.LatticeVertex) :
    FKC.latticeEmbed δ z ∈ closure ((centralTargetRectanglePolygon k hk).domain δ) ↔
      z ∈ PD.FK.latticeRectangle (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k) := by
  unfold centralTargetRectanglePolygon
  rw [rotateLatticePolygon_domain,
    rectangleLatticePolygon_vertex_iff _ _ _ (by omega) (by omega)]
  exact (PD.FK.mem_latticeRectangle _ _ _ _).symm

/-- Actual adjacency in the central-mark polygon graph is nearest-neighbour
adjacency on its complete closure carrier. -/
theorem centralTargetRectangle_graph_adj_iff (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (u v : FKC.DomainVertex δ ((centralTargetRectanglePolygon k hk).domain δ)) :
    (FKC.domainLatticeGraph δ ((centralTargetRectanglePolygon k hk).domain δ)).Adj u v ↔
      FKC.squareLattice.Adj u.val v.val := by
  rw [FKC.domainLatticeGraph_adj_iff]
  constructor
  · exact And.left
  · intro huv
    refine ⟨huv,?_⟩
    have hc : Convex ℝ (closure ((centralTargetRectanglePolygon k hk).domain δ)) := by
      unfold centralTargetRectanglePolygon
      rw [rotateLatticePolygon_domain,
        rectangleLatticePolygon_closure _ _ _ (by omega) (by omega)]
      exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
        ((convex_Icc _ _).linear_preimage Complex.imLm)
    exact hc.segment_subset u.property v.property

/-- The graph bridge for the cyclic central-target convention, with the
integer vertex map given directly, avoiding a geometric equality cast. -/
def centralTargetRectangleGraphIso (k : ℕ) (hk : 1 ≤ k) (δ : FKC.PositiveMesh) :
    PD.FK.rectangleGraph (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k) ≃g
      FKC.domainLatticeGraph δ ((centralTargetRectanglePolygon k hk).domain δ) where
  toFun u := ⟨u.val,(centralTargetRectangle_vertex_mem_iff k hk δ u.val).mpr u.property⟩
  invFun v := ⟨v.val,(centralTargetRectangle_vertex_mem_iff k hk δ v.val).mp v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro u v
    rw [centralTargetRectangle_graph_adj_iff,PD.FK.rectangleGraph_adj_iff,
      FKC.squareLattice_adj_iff,PD.FK.squareLattice_adj_iff]
    rfl

@[simp] theorem centralTargetRectangleGraphIso_val (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (u : PD.FK.RectangleVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)) :
    (centralTargetRectangleGraphIso k hk δ u).val = u.val := rfl

/-- Original PD rectangle configurations give the exact B/D dual-face
existence conclusion after the genuine primal graph isomorphism. The final
transport of literal dual bonds to PD's true finite dual graph is separate. -/
theorem centralTargetRectangle_transported_dual_exists (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (A : PD.FK.Configuration
      (PD.FK.rectangleGraph (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)))
    (hno : ¬∃ u : PD.FK.RectangleVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k),
      (u.val.2 = 12*(k : ℤ) ∧ -(k : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (k : ℤ)) ∧
      ∃ v : PD.FK.RectangleVertex (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k),
        (v.val.2 = -12*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ)) ∧
        PD.FK.ActualConnected _ A u v) :
    ∃ x ∈ centralLeftDualPorts k, ∃ y ∈ centralRightDualPorts k,
      (domainClosedDualGraph (FKC.FiniteFK.configurationIso
        (centralTargetRectangleGraphIso k hk δ) A)).Reachable x y := by
  let e := centralTargetRectangleGraphIso k hk δ
  apply centralTargetRectangle_coordinate_dual_exists k hk δ
    (FKC.FiniteFK.configurationIso e A)
  rintro ⟨u,hu,v,hv,huv⟩
  have hval : ∀ z, (e.symm z).val = z.val := by
    intro z
    have h := centralTargetRectangleGraphIso_val k hk δ (e.symm z)
    change (e (e.symm z)).val = (e.symm z).val at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  have hr : PD.FK.ActualConnected _ A (e.symm u) (e.symm v) := by
    change FKC.FiniteFK.ActualConnected _ A (e.symm u) (e.symm v)
    apply (FKC.FiniteFK.actualConnected_configurationIso e A (e.symm u) (e.symm v)).mp
    simpa only [e.apply_symm_apply] using huv
  apply hno
  refine ⟨e.symm v,?_,e.symm u,?_,hr.symm⟩
  · simpa only [hval] using hv
  · simpa only [hval] using hu

end PottsContinuity.PlanarTopology
