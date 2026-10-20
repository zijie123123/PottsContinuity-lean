-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverContourMultiplicity.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverContourBoundary
public import PottsContinuity.FKC.Medial.PortPrimalVertexCoordinates
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

local instance coverMultiplicityAmbientFintype (n : ℕ) :
    Fintype (ParafermionicAmbientVertex n) := Fintype.ofFinite _

local instance coverMultiplicityExposedFintype (n : ℕ) :
    Fintype (parafermionicCoverExposedCornerOccurrence n) :=
  Fintype.ofInjective (fun c : parafermionicCoverExposedCornerOccurrence n => c.1)
    (fun _ _ h => Subtype.ext h)

/-- Exposed corner occurrences supported at a specified actual cover vertex. -/
def parafermionicCoverExposedOccurrencesAt (n : ℕ) (v : ParafermionicCoverVertex) :=
  {c : parafermionicCoverExposedCornerOccurrence n //
    parafermionicCoverExposedCornerVertex n c = v}

local instance coverMultiplicityOccurrencesAtFintype (n : ℕ)
    (v : ParafermionicCoverVertex) :
    Fintype (parafermionicCoverExposedOccurrencesAt n v) :=
  Fintype.ofInjective
    (fun c : parafermionicCoverExposedOccurrencesAt n v => c.1)
    (fun _ _ h => Subtype.ext h)

/-- The eight axis/tip/side choices determine an exposed occurrence above its
actual primal vertex. This is a coarse bound; no sharper source contour count
is asserted. -/
theorem parafermionicCoverExposedOccurrencesAt_card_le_eight (n : ℕ)
    (v : ParafermionicCoverVertex) :
    Fintype.card (parafermionicCoverExposedOccurrencesAt n v) ≤ 8 := by
  let flags (c : parafermionicCoverExposedOccurrencesAt n v) :
      LatticeAxis × (Bool × Bool) :=
    (parafermionicCoverFinitePortCoordinatesEmbedding n c.1.1).2
  have hinj : Function.Injective flags := by
    intro c d hflags
    have hcoords : parafermionicCoverFinitePortCoordinatesEmbedding n c.1.1 =
        parafermionicCoverFinitePortCoordinatesEmbedding n d.1.1 := by
      apply Prod.ext
      · apply Subtype.ext
        change parafermionicCoverPortVertex c.1.1 =
          parafermionicCoverPortVertex d.1.1
        have hc : parafermionicCoverPortVertex c.1.1 = v := c.2
        have hd : parafermionicCoverPortVertex d.1.1 = v := d.2
        exact hc.trans hd.symm
      · exact hflags
    have hport := (parafermionicCoverFinitePortCoordinatesEmbedding n).injective hcoords
    exact Subtype.ext (Subtype.ext hport)
  have hcard := Fintype.card_le_of_injective flags hinj
  have hflags : Fintype.card (LatticeAxis × (Bool × Bool)) = 8 := by
    decide
  rw [hflags] at hcard
  exact hcard

end
end PottsContinuity.FKC.FiniteFK
