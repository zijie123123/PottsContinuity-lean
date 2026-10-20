module

public import PottsContinuity.Thm3.Prop4.FirstTargetPrefix
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Removing internal region edges from a bridge between two regions -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
noncomputable section

/-- Keep every actual graph edge except those internal to either of two
specified regions. Original vertices and graph incidence are unchanged. -/
def regionBridgeGraph {V : Type*} (G : SimpleGraph V) (P Q : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ¬(x ∈ P ∧ y ∈ P) ∧ ¬(x ∈ Q ∧ y ∈ Q)
  symm := ⟨by
    rintro x y ⟨hxy,hP,hQ⟩
    exact ⟨hxy.symm,fun h => hP h.symm,fun h => hQ h.symm⟩⟩
  loopless := ⟨by
    intro x h
    exact G.loopless.irrefl x h.1⟩

/-- Any actual connection from P to Q contains a connection between SOME
vertices of P and Q using no edges internal to either region. This applies
to arbitrary repeated walks and does not require finite or simple paths. -/
theorem regionBridgeGraph_reachable_between_regions {V : Type*}
    (G : SimpleGraph V) (P Q : Set V) {a b : V}
    (ha : a ∈ P) (hb : b ∈ Q) (hab : G.Reachable a b) :
    ∃ x ∈ P, ∃ y ∈ Q, (regionBridgeGraph G P Q).Reachable x y := by
  classical
  by_contra hnone
  let S : Set V := {x | ∃ s ∈ P, (regionBridgeGraph G P Q).Reachable s x}
  have hnotQ : ∀ x ∈ S, x ∉ Q := by
    rintro x ⟨s,hs,hsx⟩ hx
    exact hnone ⟨s,hs,x,hx,hsx⟩
  have hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S := by
    intro x hx y hxy
    by_cases hyP : y ∈ P
    · exact ⟨y,hyP,SimpleGraph.Reachable.refl _⟩
    · obtain ⟨s,hs,hsx⟩ := hx
      have hxQ := hnotQ x ⟨s,hs,hsx⟩
      have hstep : (regionBridgeGraph G P Q).Adj x y :=
        ⟨hxy,fun h => hyP h.2,fun h => hxQ h.1⟩
      exact ⟨s,hs,hsx.trans hstep.reachable⟩
  have propagate {x y : V} (p : G.Walk x y) (hx : x ∈ S) : y ∈ S := by
    induction p with
    | nil => exact hx
    | @cons x z y hxz p ih => exact ih (hclosed x hx z hxz)
  obtain ⟨p⟩ := hab
  exact hnotQ b (propagate p ⟨a,ha,SimpleGraph.Reachable.refl _⟩) hb

end
end PottsContinuity.Thm3.Prop4
