-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/ConnectorEmbedding.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.ConnectorGraph
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

def boxExitCarrierVertex {n : ℕ} (exits : Fin 3 → BoxExit n) :
    BoxExitCarrier n → LatticeVertex
  | Sum.inl x => x.val
  | Sum.inr j => boxExitOutside (exits j)

/-- Distinct cluster witnesses force the three fixed exit vertices to be
distinct. -/
theorem boxExitTripleCell_outside_injective {n : ℕ}
    (ω : LatticeConfiguration) (xs : Fin 3 → LatticeVertex)
    (exits : Fin 3 → BoxExit n) (hcell : ω ∈ boxExitTripleCell n xs exits) :
    Function.Injective (fun j => boxExitOutside (exits j)) := by
  intro j k heq
  change boxExitOutside (exits j) = boxExitOutside (exits k) at heq
  by_contra hjk
  have hj := (Set.mem_iInter.mp hcell.2) j
  have hk := (Set.mem_iInter.mp hcell.2) k
  have hreachj := hj.2.1
  have hreachk := hk.2.1
  have hreachk' : (rcInfiniteOpenGraph ω).Reachable (xs k) (boxExitOutside (exits j)) := by
    rw [← heq] at hreachk
    exact hreachk
  exact (hcell.1.2 j k hjk) (hreachj.trans hreachk'.symm)

def boxExitCarrierEmbedding {n : ℕ} (exits : Fin 3 → BoxExit n)
    (hdistinct : Function.Injective (fun j => boxExitOutside (exits j))) :
    BoxExitCarrier n ↪ LatticeVertex where
  toFun := boxExitCarrierVertex exits
  inj' := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        apply congrArg Sum.inl
        exact Subtype.ext h
      | inr k =>
        change a.val = boxExitOutside (exits k) at h
        exact ((boxExit_outside_not_mem (exits k)) (h ▸ a.property)).elim
    | inr j =>
      cases y with
      | inl b =>
        change boxExitOutside (exits j) = b.val at h
        exact ((boxExit_outside_not_mem (exits j)) (h.symm ▸ b.property)).elim
      | inr k =>
        change boxExitOutside (exits j) = boxExitOutside (exits k) at h
        exact congrArg Sum.inr (hdistinct h)

theorem boxExitConnector_adj_lattice {n : ℕ} (exits : Fin 3 → BoxExit n)
    (a b : BoxExitCarrier n)
    (hab : (boxExitConnectorGraph n exits).Adj a b) :
    squareLattice.Adj (boxExitCarrierVertex exits a) (boxExitCarrierVertex exits b) := by
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      change squareLattice.Adj x.val y.val
      exact (boxGraph_adj_iff (0, 0) n x y).mp hab
    | inr j =>
      change squareLattice.Adj x.val (boxExitOutside (exits j))
      have hxy : x.val = boxExitInside (exits j) := by
        simpa only [boxExitConnector_adj_inl_inr] using hab
      exact hxy.symm ▸ (exits j).property.2
  | inr j =>
    cases b with
    | inl x =>
      change squareLattice.Adj (boxExitOutside (exits j)) x.val
      have hxy : boxExitInside (exits j) = x.val := by
        simpa only [boxExitConnector_adj_inr_inl] using hab
      exact hxy ▸ (exits j).property.2.symm
    | inr k => change False at hab; exact hab.elim

theorem boxExitConnector_adj_incident_box {n : ℕ} (exits : Fin 3 → BoxExit n)
    (a b : BoxExitCarrier n)
    (hab : (boxExitConnectorGraph n exits).Adj a b) :
    ∃ x ∈ latticeBox (0, 0) n,
      x ∈ (s(boxExitCarrierVertex exits a, boxExitCarrierVertex exits b) : Sym2 LatticeVertex).toFinset := by
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      exact ⟨x.val, x.property, by simp [boxExitCarrierVertex, Sym2.toFinset_mk_eq]⟩
    | inr j =>
      exact ⟨x.val, x.property, by simp [boxExitCarrierVertex, Sym2.toFinset_mk_eq]⟩
  | inr j =>
    cases b with
    | inl x =>
      exact ⟨x.val, x.property, by simp [boxExitCarrierVertex, Sym2.toFinset_mk_eq]⟩
    | inr k => change False at hab; exact hab.elim

end
end PottsContinuity.PD.RCInfinite
