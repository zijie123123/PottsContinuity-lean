module

public import PottsContinuity.PlanarTopology.KSTRectangleRealization
public import PottsContinuity.PD.RCInfinite.Cylinders
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Every original bond of a confined walk is a literal edge of the finite
induced domain. This is an equality of original bonds, not a wiring quotient. -/
theorem walk_edge_lift_domain (S : Finset LatticeVertex) {u v : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (hS : ∀ z ∈ p.support, z ∈ S)
    (e : PD.squareLattice.edgeSet) (he : e.val ∈ p.edges) :
    ∃ f : (PD.squareLattice.induce (S : Set LatticeVertex)).edgeSet,
      frozenEdgeEmbedding S f = e := by
  rcases e with ⟨e,heG⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hx := hS x (p.fst_mem_support_of_mem_edges he)
    have hy := hS y (p.snd_mem_support_of_mem_edges he)
    exact ⟨⟨s(⟨x,hx⟩,⟨y,hy⟩),heG⟩,rfl⟩

/-- The openness of a confined original walk depends only on finite induced
edges. Endpoint or geometry predicates can therefore be imposed separately. -/
theorem kstPathOpen_congr_on_domain (S : Finset LatticeVertex)
    {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hS : ∀ z ∈ p.support, z ∈ S) (ω η : LatticeConfiguration)
    (hωη : ∀ f : (PD.squareLattice.induce (S : Set LatticeVertex)).edgeSet,
      ω (frozenEdgeEmbedding S f) = η (frozenEdgeEmbedding S f)) :
    kstPathOpen ω p ↔ kstPathOpen η p := by
  constructor <;> intro hp e he
  · obtain ⟨f,hf⟩ := walk_edge_lift_domain S p hS e he
    rw [← hf,← hωη f]
    exact hp _ (by rwa [hf])
  · obtain ⟨f,hf⟩ := walk_edge_lift_domain S p hS e he
    rw [← hf,hωη f]
    exact hp _ (by rwa [hf])

end
end PottsContinuity.PlanarTopology
