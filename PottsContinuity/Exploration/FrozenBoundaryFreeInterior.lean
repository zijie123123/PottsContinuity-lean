module

public import PottsContinuity.PD.FK.DomainMarkov
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

/-!
# Free induced boundary on an isolated interior

If no revealed open edge is incident to an interior set, and the set is
disjoint from the original boundary, the boundary partition induced by the
frozen record is discrete when restricted to that set. For a circuit
application, the closed primal edges crossing the circuit must imply the
no-incident-open-edge premise.
-/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

variable {V : Type*} {G : SimpleGraph V}

private theorem actualConnected_eq_of_no_open_neighbor
    (H : Configuration G) {u v : V}
    (hno : ∀ w, ¬ (openGraph G H).Adj u w)
    (hconn : ActualConnected G H u v) : v = u := by
  rcases (actualConnected_iff_walk G H u v).mp hconn with ⟨p⟩
  cases p with
  | nil => rfl
  | @cons x y z hxy tail => exact (hno y) hxy |>.elim

/-- A frozen boundary partition makes no nontrivial identifications on a set
with no incident revealed open edge, disjoint from the original boundary. -/
theorem frozenBoundary_partition_free_on_isolated
    (ξ : BoundaryCondition V) (H : Configuration G) (B : Set V)
    (hdisjoint : Disjoint B ξ.boundary)
    (hnoedge : ∀ u, u ∈ B → ∀ v, ¬ (openGraph G H).Adj u v)
    {u v : V} (hu : u ∈ B) (hv : v ∈ B) :
    (frozenBoundary ξ H).partition.r u v ↔ u = v := by
  classical
  have hubound : u ∉ ξ.boundary := by
    intro hξ
    exact (Set.disjoint_left.mp hdisjoint hu hξ)
  constructor
  · intro hrel
    change (componentSetoid G ξ H).r u v at hrel
    rw [componentSetoid_rel_iff] at hrel
    let R : V → V → Prop := fun x y =>
      ActualConnected G H x y ∨ ξ.partition.r x y
    have hstep : ∀ x y, R x y → (x = u ↔ y = u) := by
      intro x y hxy
      change ActualConnected G H x y ∨ ξ.partition.r x y at hxy
      rcases hxy with hconn | hboundary
      · constructor
        · intro hx
          subst x
          exact actualConnected_eq_of_no_open_neighbor H (hnoedge u hu) hconn
        · intro hy
          subst y
          exact actualConnected_eq_of_no_open_neighbor H (hnoedge u hu) hconn.symm
      · constructor
        · intro hx
          subst x
          rcases ξ.supported hboundary with heq | ⟨hxb, _⟩
          · exact heq.symm
          · exact (hubound hxb).elim
        · intro hy
          subst y
          rcases ξ.supported hboundary with heq | ⟨_, hyb⟩
          · exact heq
          · exact (hubound hyb).elim
    have hgen : ∀ {x y}, Relation.EqvGen R x y → (x = u ↔ y = u) := by
      intro x y hxy
      induction hxy with
      | rel x y hxy => exact hstep x y hxy
      | refl x => exact Iff.rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz
    have huiff : u = u ↔ v = u := hgen hrel
    exact (huiff.mp rfl).symm
  · intro huv
    subst v
    exact (frozenBoundary ξ H).partition.iseqv.refl u

end PottsContinuity.Exploration
