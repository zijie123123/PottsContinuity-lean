-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverSelectedCornerNeighbors.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverSelectedCorners
public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceCornerCompass
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

theorem parafermionicCoverFiniteFaceSelectedCorner_neighbors_mem_box
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) (c : Fin 4)
    (hc : c ∈ parafermionicCoverFiniteFaceSelectedCorners S v) :
    parafermionicCoverCompassNeighbor v.1 c ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverCompassNeighbor v.1 (c + 1) ∈
        parafermionicCoverBoxVertices n := by
  rcases (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v c).mp hc with
    ⟨i, hi, hcv⟩
  have hnext :
      parafermionicCoverCompassNeighbor v.1 c =
        parafermionicCoverFaceCorner i.1 (c + 1) := by
    have h := (parafermionicCoverFiniteFaceCorner_next_compass i c).symm
    rw [hcv] at h
    exact h
  have hprev :
      parafermionicCoverCompassNeighbor v.1 (c + 1) =
        parafermionicCoverFaceCorner i.1 (c - 1) := by
    have h := (parafermionicCoverFiniteFaceCorner_prev_compass i c).symm
    rw [hcv] at h
    exact h
  constructor
  · rw [hnext]
    exact parafermionicCoverFiniteFaceCorner_mem_box i (c + 1)
  · rw [hprev]
    exact parafermionicCoverFiniteFaceCorner_mem_box i (c - 1)

theorem parafermionicCoverFiniteFaceSelectedCorners_missing_of_outside_neighbor
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) (d : Fin 4)
    (hnot : parafermionicCoverCompassNeighbor v.1 d ∉
      parafermionicCoverBoxVertices n) :
    d ∉ parafermionicCoverFiniteFaceSelectedCorners S v ∧
      d - 1 ∉ parafermionicCoverFiniteFaceSelectedCorners S v := by
  have hidx : (d - 1) + 1 = d := by
    fin_cases d <;> decide
  constructor
  · intro hd
    exact hnot
      (parafermionicCoverFiniteFaceSelectedCorner_neighbors_mem_box S v d hd).1
  · intro hprev
    have hmem :=
      (parafermionicCoverFiniteFaceSelectedCorner_neighbors_mem_box S v (d - 1)
        hprev).2
    rw [hidx] at hmem
    exact hnot hmem

end PottsContinuity.FKC.Medial
