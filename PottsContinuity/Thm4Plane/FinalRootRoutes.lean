module

public import PottsContinuity.Assembly.Links
public import PottsContinuity.Assembly.FourCorridorAssembly
public import PottsContinuity.Thm1.Theorem1OfTheorem2
public import PottsContinuity.Thm3.Easy.P5AnnulusWiredBoxTransfer
public import PottsContinuity.Thm3.Prop4.TouchOnlyAssemblyConsumer
public import PottsContinuity.Thm3.RSW.TiltedReducedMarginal
public import PottsContinuity.Thm3.Touch.ReducedMarginalComposition
public import PottsContinuity.Thm4Plane.TheoremFourOfSideFactor

@[expose] public section

namespace PottsContinuity.Thm4Plane

open MeasureTheory
open PottsContinuity
open PottsContinuity.FKC.FiniteFK

noncomputable section

private theorem corrected_touch_lower_bound
    (q : Set.Ici (1 : ℝ)) (k l : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l)
    (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    1 / (20 * (k : ℝ) ^ 2 * (l : ℝ) ^ 2) ≤
      Thm3.Prop4.tiltedTouchProbability (RSW.selfDualParameters q) k l s :=
  Thm3.Touch.selfDual_tilted_touch_all_slopes_corrected_of_reducedMarginal
    q k l hk hkl
    (fun s' hs' => RSW.selfDual_tiltedStrip_reflected_marginal q (2 * k) s' hs')
    s hs

/-- Assemble the exact frozen Theorem 2 conclusion from the side-factor
family, the derived touching estimate, and the proved implication links. -/
theorem theorem_2_of_sideFactor
    (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4)
    (hside : ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ m : ℕ, 1 ≤ m →
      c₂ ^ 2 * (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m) ≤
        (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m))) :
    ∃ (pc : Set.Icc (0 : ℝ) 1) (φ₁ : Measure (squareLattice.edgeSet → Bool)),
      IsRCCriticalPoint ⟨q, hq.1⟩ pc ∧
      IsRCInfiniteVolumeLimit pc ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 1 φ₁ ∧
      φ₁ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0 := by
  obtain ⟨p₄, μ₄, hp₄, hμ₄, hP4₄⟩ :=
    theorem_four_at_self_dual_of_sideFactor q hq hside
  have hTheorem4 : ∃ (p₄ : Set.Icc (0 : ℝ) 1)
      (μ₄ : Measure (squareLattice.edgeSet → Bool)),
      (p₄ : ℝ) = Real.sqrt q / (1 + Real.sqrt q) ∧
      IsRCInfiniteVolumeLimit p₄
        ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 0 μ₄ ∧
      Assembly.assertionP4 μ₄ :=
    ⟨p₄, μ₄, hp₄, hμ₄, hP4₄⟩
  let hTouch : ∀ (qI : Set.Ici (1 : ℝ)) (k l : ℕ), 1 ≤ k → k ≤ l →
      ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
        1 / (20 * (k : ℝ) ^ 2 * (l : ℝ) ^ 2) ≤
          Thm3.Prop4.tiltedTouchProbability (RSW.selfDualParameters qI) k l s :=
    fun qI k l hk hkl s hs => corrected_touch_lower_bound qI k l hk hkl s hs
  let hP4P5geom : Assembly.p4toP5RemainingGeometryProvider :=
    Thm3.Prop4.p4toP5RemainingGeometryProvider_of_touch hTouch
  exact Assembly.theorem_2_of_links q hq hTheorem4
    (Assembly.hP4toP5_of_remainingGeometryProvider hP4P5geom)
    (by
      intro qI p μ hp hμ hP5
      exact Thm3.Easy.p5_implies_p1 qI p μ hp hμ hP5)

/-- Assemble the exact frozen Theorem 1 conclusion by the Edwards–Sokal
consumer applied to the side-factor Theorem 2 route. -/
theorem theorem_1_of_sideFactor
    (hside : ∀ q : Set.Icc (1 : ℝ) 4, ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ m : ℕ, 1 ≤ m →
        c₂ ^ 2 * (slitScreenFiniteMeasure q m).real (slitScreenEvent m) ≤
          (slitScreenFiniteMeasure q m).real
            (slitScreenEvent m ∩
              (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)))
    (q : ℕ) (hq : q ∈ Set.Icc 2 4) :
    ∃ βc : ℝ, IsPottsCriticalPoint q βc ∧
      ∀ i : Fin q, ∃ μ : Measure (ℤ × ℤ → Fin q),
        IsPottsInfiniteVolumeLimit q βc i μ ∧
          μ.real {σ | σ (0, 0) = i} = 1 / (q : ℝ) := by
  exact Thm1.theorem_1_of_theorem2
    (fun qR hqR => theorem_2_of_sideFactor qR hqR (hside ⟨qR, hqR⟩)) q hq

end
end PottsContinuity.Thm4Plane
