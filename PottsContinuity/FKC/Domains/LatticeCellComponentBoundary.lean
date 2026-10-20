-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeCellComponentBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticeCellBoundary
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.FKC.Domains

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open SimpleGraph

private theorem latticeBond_faceBase_adjacent (e : LatticeBond) :
    squareLattice.Adj (e.faceBase true) (e.faceBase false) := by
  rcases e with ⟨⟨x, y⟩, ax⟩
  cases ax <;> simp [LatticeBond.faceBase, squareLattice]

/-- The cells in `S` reachable from `c` by unit-face adjacency. -/
noncomputable def latticeCellReachableComponent
    (S : Finset LatticeVertex) (c : LatticeVertex) (hc : c ∈ S) :
    Finset LatticeVertex := by
  classical
  let G : SimpleGraph {x // x ∈ S} :=
    squareLattice.induce (↑S : Set LatticeVertex)
  exact S.filter fun x =>
    ∃ hx : x ∈ S, G.Reachable ⟨c, hc⟩ ⟨x, hx⟩

theorem mem_latticeCellReachableComponent_self
    (S : Finset LatticeVertex) (c : LatticeVertex) (hc : c ∈ S) :
    c ∈ latticeCellReachableComponent S c hc := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨hc, ⟨hc, Reachable.refl _⟩⟩

theorem latticeCellReachableComponent_subset
    (S : Finset LatticeVertex) (c : LatticeVertex) (hc : c ∈ S) :
    latticeCellReachableComponent S c hc ⊆ S :=
  Finset.filter_subset _ _

theorem latticeCellBoundaryBonds_reachableComponent_subset
    (S : Finset LatticeVertex) (c : LatticeVertex) (hc : c ∈ S) :
    latticeCellBoundaryBonds (latticeCellReachableComponent S c hc) ⊆
      latticeCellBoundaryBonds S := by
  classical
  intro e he
  rw [mem_latticeCellBoundaryBonds] at he ⊢
  let C := latticeCellReachableComponent S c hc
  change (e.faceBase true ∈ C) ≠ (e.faceBase false ∈ C) at he
  change (e.faceBase true ∈ S) ≠ (e.faceBase false ∈ S)
  have hsub : C ⊆ S := latticeCellReachableComponent_subset S c hc
  have hpropagate : ∀ a b : LatticeVertex, a ∈ S → b ∈ S →
      squareLattice.Adj a b → a ∈ C → b ∈ C := by
    intro a b ha hb hadj haC
    obtain ⟨ha', ⟨_, hreach⟩⟩ := Finset.mem_filter.mp haC
    have hstep :
        (squareLattice.induce (↑S : Set LatticeVertex)).Reachable
          ⟨a, ha'⟩ ⟨b, hb⟩ := by
      refine ⟨Walk.cons ?_ Walk.nil⟩
      change squareLattice.Adj a b
      exact hadj
    have hreachB := hreach.trans hstep
    exact Finset.mem_filter.mpr ⟨hb, ⟨hb, hreachB⟩⟩
  by_cases ht : e.faceBase true ∈ C
  · have htS : e.faceBase true ∈ S := hsub ht
    by_cases hfS : e.faceBase false ∈ S
    · have hfC : e.faceBase false ∈ C :=
        hpropagate _ _ htS hfS (latticeBond_faceBase_adjacent e) ht
      exact (he (by simp [ht, hfC])).elim
    · simp [htS, hfS]
  · have hf : e.faceBase false ∈ C := by
      by_contra hfC
      exact he (by simp [ht, hfC])
    have hfS : e.faceBase false ∈ S := hsub hf
    by_cases htS : e.faceBase true ∈ S
    · have htC : e.faceBase true ∈ C := by
        have hstep := latticeBond_faceBase_adjacent e
        have hadj : squareLattice.Adj (e.faceBase false) (e.faceBase true) := hstep.symm
        exact hpropagate _ _ hfS htS hadj hf
      exact (he (by simp [htC, hf])).elim
    · simp [htS, hfS]

end PottsContinuity.FKC.Domains
