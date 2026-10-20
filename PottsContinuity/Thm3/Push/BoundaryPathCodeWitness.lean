module

public import PottsContinuity.Exploration.BoundaryClusterPathSelector
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.Push
open PD.FK Exploration
noncomputable section

/-- Decode the finite least-code selector `Exploration.boundaryClusterPathCodeSelector` on any
supplied recorded graph.
This is the configuration-valued code selector, before any cluster reveal. -/
theorem boundaryPathCodeSelector_hasPath {V : Type*} [Finite V] [LinearOrder V]
    {G : SimpleGraph V} (S T : Set V) (R : Configuration G) (code : List V)
    (hcode : boundaryClusterPathCodeSelector S T R = some code) :
    ∃ x ∈ S, ∃ y ∈ T, ∃ p : (openGraph G R).Path x y,
      boundaryClusterPathCode R ⟨x,y,p⟩ = code := by
  classical
  unfold boundaryClusterPathCodeSelector at hcode
  dsimp only at hcode
  split_ifs at hcode with hc
  · have heq := Option.some.inj hcode
    have hmem := Finset.min'_mem _ hc
    rw [heq] at hmem
    obtain ⟨p,hvalid,hp⟩ := Finset.mem_image.mp hmem
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hvalid
    exact ⟨p.1,hvalid.1,p.2.1,hvalid.2,p.2.2,hp⟩

end
end PottsContinuity.Push
