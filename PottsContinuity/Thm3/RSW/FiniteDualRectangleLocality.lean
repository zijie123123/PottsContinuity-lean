module

public import PottsContinuity.Thm3.RSW.FiniteClosedDualRectangle

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite

/-- A confined original closed-dual crossing can be replayed when all
crossing primal bonds in its rectangle remain closed. No extremal selector
or region outside the original sampled rectangle is used. -/
theorem finiteClosedDualHorizontalRectangle_replay_of_closedBonds
    (V : Finset LatticeVertex) (l r b t : ℤ)
    (A B : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (hclosed : ∀ c : LatticeBond,
      (l ≤ (c.faceBase false).1 ∧ (c.faceBase false).1 ≤ r ∧
        b ≤ (c.faceBase false).2 ∧ (c.faceBase false).2 ≤ t) →
      (l ≤ (c.faceBase true).1 ∧ (c.faceBase true).1 ≤ r ∧
        b ≤ (c.faceBase true).2 ∧ (c.faceBase true).2 ≤ t) →
      latticeConfigurationBondState (finiteSubgraphConfiguration V 0 A) c = false →
      latticeConfigurationBondState (finiteSubgraphConfiguration V 0 B) c = false)
    (hA : A ∈ finiteClosedDualHorizontalRectangle V l r b t) :
    B ∈ finiteClosedDualHorizontalRectangle V l r b t := by
  obtain ⟨u,v,p,hu,hv,hp⟩ := hA
  let H := wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 B)
  have hedge : ∀ E, E ∈ p.edges → E ∈ H.edgeSet := by
    intro E
    refine Sym2.inductionOn E (fun x y => ?_)
    intro hE
    have hx := hp x (p.fst_mem_support_of_mem_edges hE)
    have hy := hp y (p.snd_mem_support_of_mem_edges hE)
    obtain ⟨c,hc,hends⟩ := p.adj_of_mem_edges hE
    have hf : l ≤ (c.faceBase false).1 ∧ (c.faceBase false).1 ≤ r ∧
        b ≤ (c.faceBase false).2 ∧ (c.faceBase false).2 ≤ t := by
      rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx
      · exact hy
    have ht : l ≤ (c.faceBase true).1 ∧ (c.faceBase true).1 ≤ r ∧
        b ≤ (c.faceBase true).2 ∧ (c.faceBase true).2 ≤ t := by
      rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hy
      · exact hx
    exact ⟨c,hclosed c hf ht hc,hends⟩
  refine ⟨u,v,p.transfer H hedge,hu,hv,?_⟩
  intro x hx
  have hs : (p.transfer H hedge).support = p.support := p.support_transfer hedge
  rw [hs] at hx
  exact hp x hx

/-- The source crossing reads only actual primal bond states crossed by
dual steps with both face bases in its literal rectangle. -/
theorem finiteClosedDualHorizontalRectangle_iff_of_bondStates
    (V : Finset LatticeVertex) (l r b t : ℤ)
    (A B : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (hstate : ∀ c : LatticeBond,
      (l ≤ (c.faceBase false).1 ∧ (c.faceBase false).1 ≤ r ∧
        b ≤ (c.faceBase false).2 ∧ (c.faceBase false).2 ≤ t) →
      (l ≤ (c.faceBase true).1 ∧ (c.faceBase true).1 ≤ r ∧
        b ≤ (c.faceBase true).2 ∧ (c.faceBase true).2 ≤ t) →
      latticeConfigurationBondState (finiteSubgraphConfiguration V 0 A) c =
        latticeConfigurationBondState (finiteSubgraphConfiguration V 0 B) c) :
    A ∈ finiteClosedDualHorizontalRectangle V l r b t ↔
      B ∈ finiteClosedDualHorizontalRectangle V l r b t := by
  constructor
  · exact finiteClosedDualHorizontalRectangle_replay_of_closedBonds V l r b t A B
      (fun c hf ht hc => (hstate c hf ht).symm.trans hc)
  · exact finiteClosedDualHorizontalRectangle_replay_of_closedBonds V l r b t B A
      (fun c hf ht hc => (hstate c hf ht).trans hc)

end PottsContinuity.RSW
