module

public import PottsContinuity.PlanarTopology.BalancedSeedReflection
public import PottsContinuity.PlanarTopology.BalancedCellLeftEscape

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite Filter Topology
open scoped ENNReal
noncomputable section

/-- Right escape uses the reflected law and only the three comparisons needed
by the arm estimate. The reflected base is its own reverse horizontal witness. -/
theorem balanced_cells_eventually_far_right
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ M : ℕ, ∃ N : ℕ, ∀ W H : ℕ, N < W → 2*N+2 < H →
      ∀ v x y : Fin (W+1) × Fin (H+1),
        RectangleSeedBalancedCell μ W H (2*r+2) v x y → M < W-v.1.val := by
  let ν := μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso)
  have htrans := reflectionXLaw_translation_invariant μ htranslation
  have hNuInfinite := configurationIsoLaw_infinite kstReflectionXIso μ hinfinite
  have hθ : Tendsto (fun r : ℕ => ν.real (infiniteHit (latticeBox (0,0) r : Set LatticeVertex))) atTop (𝓝 1) := by
    have hh := ENNReal.continuousAt_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤) |>.tendsto.comp
      (infiniteHit_box_probability_tendsto_one ν hNuInfinite)
    simpa only [Function.comp_def,Measure.real_def,ENNReal.toReal_one] using hh
  obtain ⟨R,hR⟩ := eventually_atTop.mp ((tendsto_order.mp hθ).1 0 zero_lt_one)
  refine ⟨R,?_⟩
  intro r hr M
  let θ := ν.real (infiniteHit (latticeBox (0,0) r : Set LatticeVertex))
  have hlim := halfPlane_arm_real_probability_tendsto_zero ν htrans
    (reflectionXLaw_FKG μ hFKG) (reflectionXLaw_dual_unique μ hunique)
    (reflectionXLaw_dual_infinite μ hdualInfinite)
    (halfPlaneRectangleSeeds (M+1+(2*r+2)) (2*r+2))
  obtain ⟨N,hN⟩ := ((tendsto_order.mp hlim).2 (θ/4) (by dsimp [θ]; linarith [hR r hr])).exists
  refine ⟨N,?_⟩
  intro W H hW hH v x y hc
  by_contra hnot
  let v' := rectangleSeedReflectXAnchor v
  let y' := rectangleSeedReflectXAnchor y
  have hbottom : rectangleSeedTopProbability ν W H (2*r+2) v' ≤
      rectangleSeedBottomProbability ν W H (2*r+2) v' := by
    simpa only [ν,v',reflectionXLaw_rectangleSeedTopProbability μ htranslation,
      reflectionXLaw_rectangleSeedBottomProbability μ htranslation] using hc.bottom_ge_top
  have hright : rectangleSeedLeftProbability ν W H (2*r+2) v' ≤
      rectangleSeedRightProbability ν W H (2*r+2) v' := by
    simpa only [ν,v',reflectionXLaw_rectangleSeedLeftProbability μ htranslation,
      reflectionXLaw_rectangleSeedRightProbability μ htranslation] using hc.left_ge_right
  have htop : rectangleSeedBottomProbability ν W H (2*r+2) y' ≤
      rectangleSeedTopProbability ν W H (2*r+2) y' := by
    simpa only [ν,y',reflectionXLaw_rectangleSeedBottomProbability μ htranslation,
      reflectionXLaw_rectangleSeedTopProbability μ htranslation] using hc.top_ge_bottom
  have hnear : v'.1.val ≤ M := Nat.le_of_not_gt hnot
  have hh := balanced_cell_near_left_core_probability_le_four_arms_of_three_comparisons
    ν htrans W H M r N hW hH v' v' y' hbottom hright htop
    ⟨Nat.le_succ _,Nat.le_succ _⟩ ⟨Nat.le_succ _,Nat.le_succ _⟩
    (rectangleSeedReflectXAnchor_close hc.top_close_fst) hc.top_close_snd hnear
  have heq := congrArg ENNReal.toReal (measure_infiniteHit_latticeBox_translate ν
    ((v'.1.val:ℤ)+(r:ℤ)+1,(v'.2.val:ℤ)+(r:ℤ)+1) (htrans _) r)
  change ν.real (infiniteHit (latticeBox ((v'.1.val:ℤ)+(r:ℤ)+1,(v'.2.val:ℤ)+(r:ℤ)+1) r : Set LatticeVertex)) = θ at heq
  rw [heq] at hh
  linarith

end
end PottsContinuity.PlanarTopology
