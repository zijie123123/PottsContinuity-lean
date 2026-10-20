-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverOpenWalkRayEnclosure.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverOpenWalkFilling
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPrimalEdgeWalk
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph

/-- A single genuine finite box encloses the actual refined closed pairing
walk, the refinement of an actual open walk, and an arbitrary actual
nine-step refined primal ray. The ray's support-modulus exclusion supplies
the ordinary-face nonbranch premise. -/
theorem parafermionicCoverOpenWalkRay_exists_common_box
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {a : ParafermionicCoverFinitePort n × Bool}
    (q : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk a a)
    {x y : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk x y)
    (u : ParafermionicCoverVertex) (d : Fin 4) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ z ∈ (parafermionicCoverRefinedPairingWalk n hn A q).support,
        z ∈ parafermionicCoverBoxVertices N) ∧
      (∀ z ∈ (parafermionicCoverRefinedPrimalSubstitute
        (w.map (parafermionicCoverBoxOpenWalkHom n A))).support,
        z ∈ parafermionicCoverFiniteOrdinaryFaces N) ∧
      (∀ z ∈ (parafermionicCoverRefinedPrimalEdgeWalk u d).support,
        z ∈ parafermionicCoverFiniteOrdinaryFaces N) := by
  let ray := parafermionicCoverRefinedPrimalEdgeWalk u d
  have hray : ∀ f ∈ ray.support, f.1 ≠ (0,-1) := by
    intro f hf hbranch
    have hmod := parafermionicCoverRefinedPrimalEdgeWalk_support_modulus u d f hf
    rcases f with ⟨⟨fx, fy⟩, k⟩
    change (fx, fy) = (0,-1) at hbranch
    simp only [Prod.mk.injEq] at hbranch
    rcases hbranch with ⟨rfl, rfl⟩
    norm_num at hmod
  obtain ⟨N, hN, hbox, hfaces⟩ :=
    parafermionicCoverOpenWalkFilling_exists_common_box n hn A q w
      ray.support hray
  refine ⟨N, hN, hbox, ?_, ?_⟩
  · intro z hz
    exact hfaces z (List.mem_append.mpr (Or.inl hz))
  · intro z hz
    exact hfaces z (List.mem_append.mpr (Or.inr hz))

end PottsContinuity.FKC.FiniteFK
