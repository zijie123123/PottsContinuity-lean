module

public import PottsContinuity.PD.FK.Isomorphism
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! # Pullback of actual recorded walks and their whole supports -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
local instance recordedPullbackVertexEq (V : Type*) : DecidableEq V := Classical.decEq _

/-- An actual recorded walk and its complete finite support pull back through
an original graph isomorphism, with the two prescribed marks retained. -/
theorem recorded_walk_pullback_support {V W : Type*}
    [vertexEqV : DecidableEq V] [vertexEqW : DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (R : Configuration H) (u v : V)
    (p : (openGraph H R).Walk (e u) (e v)) (T : Finset W)
    (hT : p.support.toFinset = T) :
    ∃ q : (openGraph G ((configurationIso e).symm R)).Walk u v,
      q.support.toFinset = T.map e.symm.toEquiv.toEmbedding := by
  classical
  let back : openGraph H R →g openGraph G ((configurationIso e).symm R) :=
    { toFun := e.symm
      map_rel' := by
        intro a b hab
        apply (openGraphIso e ((configurationIso e).symm R)).map_rel_iff'.mp
        change (openGraph H ((configurationIso e) ((configurationIso e).symm R))).Adj
          (e (e.symm a)) (e (e.symm b))
        simpa only [Equiv.apply_symm_apply,e.apply_symm_apply] using hab }
  let q := (p.map back).copy (e.symm_apply_apply u) (e.symm_apply_apply v)
  refine ⟨q,?_⟩
  rw [← hT]
  simp only [q,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]
  ext z
  simp only [List.mem_toFinset,Finset.mem_map,List.mem_map]
  rfl

end
end PottsContinuity.Thm3.Prop4
