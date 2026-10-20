-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFaceVertexIncidenceBound.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceSetVertexIncidence
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

theorem parafermionicCoverFaceBaseCorner_injective :
    Function.Injective (fun f : ParafermionicCoverVertex => f) := by
  intro f g h
  exact h

theorem parafermionicCoverFaceRightCorner_injective :
    Function.Injective (fun f : ParafermionicCoverVertex =>
      parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2) := by
  intro f g h
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  simp only [parafermionicCoverFaceRightLift_formula, Prod.mk.injEq] at h
  rcases h with ⟨⟨hx,hy⟩,hk⟩
  simp only [Prod.mk.injEq]
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem parafermionicCoverFaceRightUpCorner_injective :
    Function.Injective (fun f : ParafermionicCoverVertex =>
      parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2) := by
  intro f g h
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  simp only [parafermionicCoverFaceRightUpLift_formula, Prod.mk.injEq] at h
  rcases h with ⟨⟨hx,hy⟩,hk⟩
  simp only [Prod.mk.injEq]
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem parafermionicCoverFaceRightUpLeftCorner_injective :
    Function.Injective (fun f : ParafermionicCoverVertex =>
      parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2) := by
  intro f g h
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  simp only [parafermionicCoverFaceRightUpLeftLift_formula, Prod.mk.injEq] at h
  rcases h with ⟨⟨hx,hy⟩,hk⟩
  simp only [Prod.mk.injEq]
  exact ⟨⟨by omega, by omega⟩, by omega⟩

end PottsContinuity.FKC.Medial
