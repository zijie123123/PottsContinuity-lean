module

public import PottsContinuity.PlanarTopology.AlphaTargetDualPorts
public import PottsContinuity.PlanarTopology.RectangleGraphBridge
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- Exact membership bridge to the PD rectangle's entire vertex carrier. -/
theorem alphaTargetRectangle_vertex_mem_iff (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) (z : FKC.LatticeVertex) :
    FKC.latticeEmbed δ z ∈ closure ((alphaTargetRectanglePolygon k hk).domain δ) ↔
      z ∈ PD.FK.latticeRectangle (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k) := by
  unfold alphaTargetRectanglePolygon
  rw [rotateLatticePolygon_domain,
    rectangleLatticePolygon_vertex_iff _ _ _ (by omega) (by omega)]
  exact (PD.FK.mem_latticeRectangle _ _ _ _).symm

/-- Actual adjacency in the central-mark polygon graph is nearest-neighbour
adjacency on its complete closure carrier. -/
theorem alphaTargetRectangle_graph_adj_iff (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (u v : FKC.DomainVertex δ ((alphaTargetRectanglePolygon k hk).domain δ)) :
    (FKC.domainLatticeGraph δ ((alphaTargetRectanglePolygon k hk).domain δ)).Adj u v ↔
      FKC.squareLattice.Adj u.val v.val := by
  rw [FKC.domainLatticeGraph_adj_iff]
  constructor
  · exact And.left
  · intro huv
    refine ⟨huv,?_⟩
    have hc : Convex ℝ (closure ((alphaTargetRectanglePolygon k hk).domain δ)) := by
      unfold alphaTargetRectanglePolygon
      rw [rotateLatticePolygon_domain,
        rectangleLatticePolygon_closure _ _ _ (by omega) (by omega)]
      exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
        ((convex_Icc _ _).linear_preimage Complex.imLm)
    exact hc.segment_subset u.property v.property

/-- The graph bridge for the cyclic central-target convention, with the
integer vertex map given directly, avoiding a geometric equality cast. -/
def alphaTargetRectangleGraphIso (k : ℕ) (hk : 1 ≤ k) (δ : FKC.PositiveMesh) :
    PD.FK.rectangleGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k) ≃g
      FKC.domainLatticeGraph δ ((alphaTargetRectanglePolygon k hk).domain δ) where
  toFun u := ⟨u.val,(alphaTargetRectangle_vertex_mem_iff k hk δ u.val).mpr u.property⟩
  invFun v := ⟨v.val,(alphaTargetRectangle_vertex_mem_iff k hk δ v.val).mp v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro u v
    rw [alphaTargetRectangle_graph_adj_iff,PD.FK.rectangleGraph_adj_iff,
      FKC.squareLattice_adj_iff,PD.FK.squareLattice_adj_iff]
    rfl

@[simp] theorem alphaTargetRectangleGraphIso_val (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (u : PD.FK.RectangleVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)) :
    (alphaTargetRectangleGraphIso k hk δ u).val = u.val := rfl

/-- Original PD rectangle configurations give the exact B/D dual-face
existence conclusion after the genuine primal graph isomorphism. The final
transport of literal dual bonds to PD's true finite dual graph is separate. -/
theorem alphaTargetRectangle_transported_dual_exists (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (A : PD.FK.Configuration
      (PD.FK.rectangleGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)))
    (hno : ¬∃ u : PD.FK.RectangleVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
      (u.val.2 = 64*(k : ℤ) ∧ -(k : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (k : ℤ)) ∧
      ∃ v : PD.FK.RectangleVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
        (v.val.2 = -64*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ)) ∧
        PD.FK.ActualConnected _ A u v) :
    ∃ x ∈ alphaLeftDualPorts k, ∃ y ∈ alphaRightDualPorts k,
      (domainClosedDualGraph (FKC.FiniteFK.configurationIso
        (alphaTargetRectangleGraphIso k hk δ) A)).Reachable x y := by
  let e := alphaTargetRectangleGraphIso k hk δ
  apply alphaTargetRectangle_coordinate_dual_exists k hk δ
    (FKC.FiniteFK.configurationIso e A)
  rintro ⟨u,hu,v,hv,huv⟩
  have hval : ∀ z, (e.symm z).val = z.val := by
    intro z
    have h := alphaTargetRectangleGraphIso_val k hk δ (e.symm z)
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
