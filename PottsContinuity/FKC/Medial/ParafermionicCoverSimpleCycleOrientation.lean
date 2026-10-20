-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverSimpleCycleOrientation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverSimpleCycleFilling
public import PottsContinuity.FKC.Medial.FiniteCycleSupportedFlow

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

 theorem parafermionicCoverSimpleCycleFilling_coefficient_orientation
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ∃ k : ℤ, (k = -1 ∨ k = 1) ∧
      ∀ d ∈ p.darts,
        parafermionicCoverFaceBoundaryCoefficient
          (parafermionicCoverSimpleCycleFillingSet hn p hp) d.fst d.snd = k := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let c : ParafermionicCoverBoxVertex n → ParafermionicCoverBoxVertex n → ℤ :=
    parafermionicCoverFaceBoundaryCoefficient S
  have hspec := parafermionicCoverSimpleCycleFillingSet_spec hn p hp
  have hanti : ∀ x y, c x y = -c y x := by
    intro x y
    exact parafermionicCoverFaceBoundaryCoefficient_antisymm S x y
  have hbalance : ∀ x, ∑ y : ParafermionicCoverBoxVertex n, c x y = 0 := by
    intro x
    exact parafermionicCoverFaceBoundaryCoefficient_divergence S x
  have hsupport : ∀ x y, s(x,y) ∉ p.edges → c x y = 0 := by
    intro x y hnot
    by_contra hnonzero
    exact hnot ((hspec.2.2 x y).mp hnonzero)
  have hnonzero : ∀ x y, s(x,y) ∈ p.edges → c x y ≠ 0 := by
    intro x y hedge
    exact (hspec.2.2 x y).mpr hedge
  have hbound : ∀ x y, c x y = -1 ∨ c x y = 0 ∨ c x y = 1 := by
    intro x y
    simpa [c] using parafermionicCoverFaceBoundaryCoefficient_mem S x y
  simpa [S, c] using
    (cycleSupportedFlow_constantOnDarts_sign
      (parafermionicCoverBoxGraph n) p hp c hanti hbalance hsupport hnonzero hbound)

end PottsContinuity.FKC.Medial
