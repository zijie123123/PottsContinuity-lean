module

public import PottsContinuity.DualityExt.RectangleResults
public import PottsContinuity.PD.Duality.CircuitEnclosure
public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration
public import PottsContinuity.PD.Duality.RayIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# A boundary-condition counterexample for annulus circuit wording

In the radius-one annulus, a closed dual circuit can have nonzero winding
about the origin while cutting off only an inner-boundary corner. That corner
still has an open path to the outer boundary. Thus “surrounding the origin”
must mean separation of the full inner source set for the annulus crossing
duality statement.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open scoped Classical
open PottsContinuity.PD.Duality
open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial

def annulusVertexSet (r : ℕ) : Finset LatticeVertex :=
  latticeBox (0, 0) (2 * r) \ latticeBox (0, 0) (r - 1)

def annulusOpenGraph (r : ℕ) (ω : LatticeConfiguration) : SimpleGraph LatticeVertex where
  Adj u v := u ∈ annulusVertexSet r ∧ v ∈ annulusVertexSet r ∧
    (wholePlaneOpenPrimalGraph ω).Adj u v
  symm := ⟨by
    rintro u v ⟨hu, hv, h⟩
    exact ⟨hv, hu, h.symm⟩⟩
  loopless := ⟨by
    intro u h
    exact (wholePlaneOpenPrimalGraph ω).loopless.irrefl u h.2.2⟩

def annulusOuterBoundary (R : ℕ) : Finset LatticeVertex :=
  (latticeBox (0, 0) R).filter fun v =>
    v.1 = (R : ℤ) ∨ v.1 = -(R : ℤ) ∨ v.2 = (R : ℤ) ∨ v.2 = -(R : ℤ)

def annulusOpenCrossing (r : ℕ) (ω : LatticeConfiguration) : Prop :=
  ∃ u v : LatticeVertex,
    u ∈ latticeBox (0, 0) r ∧ v ∈ annulusOuterBoundary (2 * r) ∧
      (annulusOpenGraph r ω).Reachable u v

private theorem walk_first_entry {V : Type*} (G : SimpleGraph V) (B : Set V)
    {u v : V} (p : G.Walk u v) (hu : u ∉ B) (hv : v ∈ B) :
    ∃ x, x ∈ B ∧ ∃ w, G.Adj w x ∧ w ∉ B ∧
      ∃ q : G.Walk u w, ∀ y ∈ q.support, y ∉ B := by
  classical
  induction p with
  | nil => exact False.elim (hu hv)
  | @cons u z v h p ih =>
      by_cases hz : z ∈ B
      · refine ⟨z, hz, u, h, hu, .nil, ?_⟩
        intro y hy
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
        subst y
        exact hu
      · obtain ⟨x, hx, w, hw, hwo, q, hq⟩ := ih hz hv
        refine ⟨x, hx, w, hw, hwo, .cons h q, ?_⟩
        intro y hy
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hu
        · exact hq y hy

private theorem walk_map_of_support {V : Type*} {G H : SimpleGraph V}
    {u v : V} (P : V → Prop) (p : G.Walk u v)
    (hP : ∀ x ∈ p.support, P x)
    (hAdj : ∀ a b, G.Adj a b → P a → P b → H.Adj a b) : H.Reachable u v := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u z v h p ih =>
      have hu : P u := hP u (by simp)
      have hz : P z := hP z (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have htail : ∀ x ∈ p.support, P x := fun x hx => hP x (by
        simp [SimpleGraph.Walk.support_cons, hx])
      exact (hAdj u z h hu hz).reachable.trans (ih htail)

end PottsContinuity.DualityExt
