module

public import PottsContinuity.Thm4Plane.ScreenConnector
public import PottsContinuity.Thm4Plane.ScreenChainRule

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC.FiniteFK

noncomputable section

local instance slitScreenConfigurationMeasurableSpace (m : ℕ) :
    MeasurableSpace (Configuration (slitBoxGraph (16 * m))) :=
  PottsContinuity.PD.FK.configurationMeasurableSpace _

/-- The finite Dobrushin law on the literal slit carrier at screen scale `m`. -/
def slitScreenFiniteMeasure (q : Set.Icc (1 : ℝ) 4) (m : ℕ) :
    @Measure (Configuration (slitBoxGraph (16 * m)))
      (PottsContinuity.PD.FK.configurationMeasurableSpace _) :=
  PottsContinuity.PD.FK.measure (slitBoxGraph (16 * m))
    (PottsContinuity.Thm4.selfDualParameters ⟨q, q.2.1⟩)
    (PottsContinuity.Thm4.fkcBoundaryToPD (slitBoxBoundary (16 * m)))

local instance slitScreenFiniteMeasure_isProbabilityMeasure
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ) :
    IsProbabilityMeasure (slitScreenFiniteMeasure q m) := by
  dsimp [slitScreenFiniteMeasure]
  infer_instance

/-- The three source event factors multiply to a finite screen probability
lower bound. `hF` is the joint vertical-screen factor and `hC` is the
connector-event factor, each stated without conditioning denominators. -/
theorem slitScreenFourFactor_probability_lower_bound_of_crossing_factors
    (q : Set.Icc (1 : ℝ) 4) (b d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hF : ∀ m : ℕ, 1 ≤ m →
      b * (slitScreenFiniteMeasure q m).real (slitScreenEvent m) ≤
        (slitScreenFiniteMeasure q m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)))
    (hC : ∀ m : ℕ, 1 ≤ m →
      d * (slitScreenFiniteMeasure q m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)) ≤
        (slitScreenFiniteMeasure q m).real
          ((slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)) ∩
              slitScreenConnectorEvent m)) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      (c / ((16 * m : ℕ) : ℝ)^16) * b * d ≤
        (slitScreenFiniteMeasure q m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m) ∩
              slitScreenConnectorEvent m) := by
  obtain ⟨c, hc, hE⟩ := slitScreenEvent_probability_lower_bound q
  refine ⟨c, hc, ?_⟩
  intro m hm
  have hA : c / ((16 * m : ℕ) : ℝ)^16 ≤
      (slitScreenFiniteMeasure q m).real (slitScreenEvent m) := by
    simpa [slitScreenFiniteMeasure, Measure.real_def] using hE m hm
  have hprod := three_event_probability_chain_lower_bound
    (slitScreenFiniteMeasure q m) (slitScreenEvent m)
    (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)
    (slitScreenConnectorEvent m)
    (c / ((16 * m : ℕ) : ℝ)^16) b d hb hd hA (hF m hm) (hC m hm)
  simpa [Set.inter_assoc] using hprod

end
end PottsContinuity.Thm4Plane
