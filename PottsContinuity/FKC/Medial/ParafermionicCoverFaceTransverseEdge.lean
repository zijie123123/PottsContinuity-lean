-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFaceTransverseEdge.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceCornerCompass

@[expose] public section

namespace PottsContinuity.FKC.Medial

/-- At a horizontal face step, the positive perpendicular edge belongs to both
actual retained face dart sets, with opposite orientations. -/
theorem parafermionicCoverFaceTransverseEdge_east
    {n : ℕ} (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (h : j.1 = parafermionicCoverCompassNeighbor i.1 0) :
    (j.1, parafermionicCoverCompassNeighbor j.1 1) ∈
        parafermionicCoverFiniteFaceDarts i.1 ∧
      (parafermionicCoverCompassNeighbor j.1 1, j.1) ∈
        parafermionicCoverFiniteFaceDarts j.1 := by
  have hnext0 : parafermionicCoverFaceCorner i.1 1 =
      parafermionicCoverCompassNeighbor i.1 0 := by
    simpa using parafermionicCoverFiniteFaceCorner_next_compass i 0
  have hnext1 : parafermionicCoverFaceCorner i.1 2 =
      parafermionicCoverCompassNeighbor (parafermionicCoverFaceCorner i.1 1) 1 := by
    simpa using parafermionicCoverFiniteFaceCorner_next_compass i 1
  have hi1 : j.1 = parafermionicCoverFaceCorner i.1 1 := h.trans hnext0.symm
  have hi2 : parafermionicCoverFaceCorner i.1 2 =
      parafermionicCoverCompassNeighbor j.1 1 := by
    simpa [← hi1] using hnext1
  have hj3 : parafermionicCoverFaceCorner j.1 3 =
      parafermionicCoverCompassNeighbor j.1 1 := by
    have hprev := parafermionicCoverFiniteFaceCorner_prev_compass j 0
    have hidx : (0 : Fin 4) - 1 = 3 := by decide
    rw [hidx] at hprev
    simpa using hprev
  constructor
  · simpa [hi1, hi2] using
      (show (parafermionicCoverFaceCorner i.1 1,
        parafermionicCoverFaceCorner i.1 2) ∈
        parafermionicCoverFiniteFaceDarts i.1 by
          simp [parafermionicCoverFiniteFaceDarts,
            parafermionicCoverFaceCorner])
  · simpa [hj3] using
      (show (parafermionicCoverFaceCorner j.1 3,
        parafermionicCoverFaceCorner j.1 0) ∈
        parafermionicCoverFiniteFaceDarts j.1 by
          simp [parafermionicCoverFiniteFaceDarts,
            parafermionicCoverFaceCorner])

/-- At a north face step, the same actual positive transverse edge is shared
with opposite orientations. -/
theorem parafermionicCoverFaceTransverseEdge_north
    {n : ℕ} (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (h : j.1 = parafermionicCoverCompassNeighbor i.1 1) :
    (parafermionicCoverCompassNeighbor j.1 0, j.1) ∈
        parafermionicCoverFiniteFaceDarts i.1 ∧
      (j.1, parafermionicCoverCompassNeighbor j.1 0) ∈
        parafermionicCoverFiniteFaceDarts j.1 := by
  have hprev0 : parafermionicCoverFaceCorner i.1 3 =
      parafermionicCoverCompassNeighbor i.1 1 := by
    have hp := parafermionicCoverFiniteFaceCorner_prev_compass i 0
    have hidx : (0 : Fin 4) - 1 = 3 := by decide
    rw [hidx] at hp
    simpa using hp
  have hi2 : j.1 = parafermionicCoverFaceCorner i.1 3 := h.trans hprev0.symm
  have hprev3 : parafermionicCoverFaceCorner i.1 2 =
      parafermionicCoverCompassNeighbor (parafermionicCoverFaceCorner i.1 3) 0 := by
    have hp := parafermionicCoverFiniteFaceCorner_prev_compass i 3
    have hidx : (3 : Fin 4) - 1 = 2 := by decide
    have hdir : (3 : Fin 4) + 1 = 0 := by decide
    rw [hidx, hdir] at hp
    exact hp
  have hi1 : parafermionicCoverFaceCorner i.1 2 =
      parafermionicCoverCompassNeighbor j.1 0 := by
    simpa [← hi2] using hprev3
  have hj1 : parafermionicCoverFaceCorner j.1 1 =
      parafermionicCoverCompassNeighbor j.1 0 := by
    simpa using parafermionicCoverFiniteFaceCorner_next_compass j 0
  constructor
  · simpa [hi1, hi2] using
      (show (parafermionicCoverFaceCorner i.1 2,
        parafermionicCoverFaceCorner i.1 3) ∈
        parafermionicCoverFiniteFaceDarts i.1 by
          simp [parafermionicCoverFiniteFaceDarts,
            parafermionicCoverFaceCorner])
  · simpa [hj1, parafermionicCoverFaceCorner_zero] using
      (show (parafermionicCoverFaceCorner j.1 0,
        parafermionicCoverFaceCorner j.1 1) ∈
        parafermionicCoverFiniteFaceDarts j.1 by
          simp [parafermionicCoverFiniteFaceDarts,
            parafermionicCoverFaceCorner])

end PottsContinuity.FKC.Medial
