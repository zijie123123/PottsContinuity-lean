-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverContourSum.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverContourMultiplicity
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

local instance coverContourSumAmbientFintype (n : ℕ) :
    Fintype (ParafermionicAmbientVertex n) := Fintype.ofFinite _

local instance coverContourSumExposedFintype (n : ℕ) :
    Fintype (parafermionicCoverExposedCornerOccurrence n) :=
  Fintype.ofInjective (fun c : parafermionicCoverExposedCornerOccurrence n => c.1)
    (fun _ _ h => Subtype.ext h)

/-- Actual box vertices having an actual cover-graph neighbor outside the box.
This includes top and bottom sheets. -/
def parafermionicCoverFiniteExteriorNeighborBoundary (n : ℕ) :
    Finset ParafermionicCoverVertex := by
  classical
  exact (parafermionicCoverBoxFinset n).filter fun v =>
    ∃ w : ParafermionicCoverVertex,
      parafermionicCoverGraph.Adj v w ∧ w ∉ parafermionicCoverBoxVertices n

def parafermionicCoverExposedPrimalImage (n : ℕ) :
    Finset ParafermionicCoverVertex :=
  (parafermionicCoverExposedCorners n).image
    (parafermionicCoverExposedCornerVertex n)

theorem parafermionicCoverExposedPrimalImage_subset_exteriorBoundary (n : ℕ) :
    parafermionicCoverExposedPrimalImage n ⊆
      parafermionicCoverFiniteExteriorNeighborBoundary n := by
  classical
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨c, hc, rfl⟩
  rw [parafermionicCoverFiniteExteriorNeighborBoundary, Finset.mem_filter]
  constructor
  · change parafermionicCoverExposedCornerVertex n c ∈
      parafermionicCoverBoxVertices n
    exact parafermionicCoverExposedCorner_vertex_mem_box n c
  · exact parafermionicCoverExposedCorner_has_outside_neighbor n c

local instance coverContourSumFiberFintype (n : ℕ) (v : ParafermionicCoverVertex) :
    Fintype (parafermionicCoverExposedOccurrencesAt n v) :=
  Fintype.ofInjective
    (fun c : parafermionicCoverExposedOccurrencesAt n v => c.1)
    (fun _ _ h => Subtype.ext h)

private theorem parafermionicCoverExposedFiber_card_le_eight (n : ℕ)
    (v : ParafermionicCoverVertex) :
    ((parafermionicCoverExposedCorners n).filter fun c =>
      parafermionicCoverExposedCornerVertex n c = v).card ≤ 8 := by
  classical
  let F := (parafermionicCoverExposedCorners n).filter fun c =>
    parafermionicCoverExposedCornerVertex n c = v
  let toOccurrencesAt (c : F) : parafermionicCoverExposedOccurrencesAt n v :=
    ⟨c.1, (Finset.mem_filter.mp c.2).2⟩
  have hinj : Function.Injective toOccurrencesAt := by
    intro c d h
    exact Subtype.ext
      (congrArg (fun x : parafermionicCoverExposedOccurrencesAt n v => x.1) h)
  have hcard : Fintype.card F ≤ 8 := by
    calc
      Fintype.card F ≤ Fintype.card (parafermionicCoverExposedOccurrencesAt n v) :=
        Fintype.card_le_of_injective toOccurrencesAt hinj
      _ ≤ 8 := parafermionicCoverExposedOccurrencesAt_card_le_eight n v
  rw [← Fintype.card_coe F]
  exact hcard

/-- Any nonnegative vertex weights sum over all retained exposed occurrences
to at most eight times their sum over the actual primal image. This is a coarse
fiber bound; no sharper contour multiplicity is asserted. -/
theorem parafermionicCoverExposedCorners_weighted_sum_le_eight_image
    (n : ℕ) (f : ParafermionicCoverVertex → ℝ)
    (hf : ∀ v, 0 ≤ f v) :
    (∑ c ∈ parafermionicCoverExposedCorners n,
      f (parafermionicCoverExposedCornerVertex n c)) ≤
      8 * (∑ v ∈ parafermionicCoverExposedPrimalImage n, f v) := by
  classical
  let C := parafermionicCoverExposedCorners n
  let g := parafermionicCoverExposedCornerVertex n
  let I := parafermionicCoverExposedPrimalImage n
  have hmap : ∀ c ∈ C, g c ∈ I := by
    intro c hc
    exact Finset.mem_image_of_mem g hc
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun c => f (g c))]
  calc
    (∑ v ∈ I, ∑ c ∈ C with g c = v, f (g c)) ≤
        ∑ v ∈ I, 8 * f v := by
          apply Finset.sum_le_sum
          intro v hv
          let F := C.filter fun c => g c = v
          have hsum : (∑ c ∈ C with g c = v, f (g c)) =
              ∑ c ∈ F, f v := by
            apply Finset.sum_congr rfl
            intro c hc
            simp only [Finset.mem_filter] at hc
            rw [hc.2]
          rw [hsum]
          have hcard := parafermionicCoverExposedFiber_card_le_eight n v
          have hcardR : (F.card : ℝ) ≤ 8 := by exact_mod_cast hcard
          calc
            (∑ c ∈ F, f v) = (F.card : ℝ) * f v := by simp
            _ ≤ 8 * f v := mul_le_mul_of_nonneg_right hcardR (hf v)
    _ = 8 * (∑ v ∈ I, f v) := by rw [Finset.mul_sum]

/-- The same coarse bound holds when the occurrence weights are summed over the
full actual exterior-neighbor boundary, including both extremal sheets. -/
theorem parafermionicCoverExposedCorners_weighted_sum_le_eight_boundary
    (n : ℕ) (f : ParafermionicCoverVertex → ℝ)
    (hf : ∀ v, 0 ≤ f v) :
    (∑ c ∈ parafermionicCoverExposedCorners n,
      f (parafermionicCoverExposedCornerVertex n c)) ≤
      8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n, f v) := by
  calc
    (∑ c ∈ parafermionicCoverExposedCorners n,
      f (parafermionicCoverExposedCornerVertex n c)) ≤
        8 * (∑ v ∈ parafermionicCoverExposedPrimalImage n, f v) :=
      parafermionicCoverExposedCorners_weighted_sum_le_eight_image n f hf
    _ ≤ 8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n, f v) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (parafermionicCoverExposedPrimalImage_subset_exteriorBoundary n)
        (by intro v hv hnot; exact hf v)

end
end PottsContinuity.FKC.FiniteFK
