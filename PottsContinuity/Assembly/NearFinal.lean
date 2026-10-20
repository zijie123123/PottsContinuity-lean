module

public import PottsContinuity.Assembly.Links
public import PottsContinuity.Assembly.FourCorridorAssembly
public import PottsContinuity.Thm1.Theorem1OfTheorem2
public import PottsContinuity.Thm3.Easy.P5AnnulusWiredBoxTransfer
public import PottsContinuity.Thm3.Prop4.TouchOnlyAssemblyConsumer
public import PottsContinuity.Thm3.Push.UnconditionalPush
public import PottsContinuity.Thm4Plane.ScreenActiveConnectorFactor
public import PottsContinuity.Thm4Plane.ScreenActiveConnectorSourcePaths
public import PottsContinuity.Thm4Plane.ScreenCanonicalPlaneSourceRecords
public import PottsContinuity.Thm4Plane.ScreenSideFactor
public import PottsContinuity.Thm4Plane.PlaneFiniteComparison
public import PottsContinuity.Thm4Plane.ScreenFactorAssembly
public import PottsContinuity.Thm3.RSW.StoppingUpper
public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import PottsContinuity.Thm4Plane.ScreenBoundaryClusterConditional
public import PottsContinuity.Thm4Plane.ScreenPlaneAssembly
public import PottsContinuity.Thm4Plane.ScreenRecordAssembly
public import PottsContinuity.Thm3.Push.PushOfStripRSW

@[expose] public section

namespace PottsContinuity.Assembly

open MeasureTheory
open PottsContinuity
open PottsContinuity.FKC.FiniteFK

noncomputable section

/-- Assemble frozen Theorem 3 from the exact touching family (Lemma 6). The Lemma 4
recurrence and pair estimate, P5-to-P1, the critical value, and the other cycle links
are supplied by proved theorems. -/
theorem theorem_3_of_touch
    (q : ℝ) (hq : 1 ≤ q)
    (hTouch : ∀ (q : Set.Ici (1 : ℝ)) (k l : ℕ), 1 ≤ k → k ≤ l →
      ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
        1 / (20 * (k : ℝ)^2 * (l : ℝ)^2) ≤
          Thm3.Prop4.tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ (pc : Set.Icc (0 : ℝ) 1)
      (φ : Fin 2 → Measure (squareLattice.edgeSet → Bool)),
      IsRCCriticalPoint ⟨q, hq⟩ pc ∧
      (∀ i, IsRCInfiniteVolumeLimit pc
        ⟨q, lt_of_lt_of_le one_pos hq⟩ i (φ i)) ∧
      List.TFAE
        [assertionP1 (φ 1), assertionP2 (φ 0) (φ 1),
          assertionP3 (φ 0), assertionP4 (φ 0),
          assertionP5 pc ⟨q, lt_of_lt_of_le one_pos hq⟩] := by
  let hP4P5geom : p4toP5RemainingGeometryProvider :=
    Thm3.Prop4.p4toP5RemainingGeometryProvider_of_touch hTouch
  exact theorem_3_of_links q hq
    (hP4toP5_of_remainingGeometryProvider hP4P5geom)
    (by
      intro qI p μ hp hμ hP5
      exact Thm3.Easy.p5_implies_p1 qI p μ hp hμ hP5)

end
end PottsContinuity.Assembly
