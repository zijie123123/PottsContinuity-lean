module

public import PottsContinuity.PlanarTopology.BalancedCellLeftBound
public import PottsContinuity.PlanarTopology.HalfPlaneFKG
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite Filter Topology
open scoped ENNReal
noncomputable section

theorem latticeTranslate_image_box_zero (a : LatticeVertex) (r : ℕ) :
    latticeTranslate a '' (latticeBox (0,0) r : Set LatticeVertex) = (latticeBox a r : Set LatticeVertex) := by
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    have hh := (mem_latticeBox (0,0) u r).mp hu
    apply (mem_latticeBox a (latticeTranslate a u) r).mpr
    dsimp [latticeTranslate] at *
    omega
  · intro hz
    let u : LatticeVertex := (z.1-a.1,z.2-a.2)
    have hu : latticeTranslate a u = z := by ext <;> dsimp [u,latticeTranslate] <;> omega
    refine ⟨u,?_,hu⟩
    apply (mem_latticeBox (0,0) u r).mpr
    have hh := (mem_latticeBox a z r).mp hz
    dsimp [u]
    omega

theorem measure_infiniteHit_latticeBox_translate (μ : Measure LatticeConfiguration)
    (a : LatticeVertex) (hμ : μ.map (edgeTranslate a) = μ) (r : ℕ) :
    μ (infiniteHit (latticeBox a r : Set LatticeVertex)) =
      μ (infiniteHit (latticeBox (0,0) r : Set LatticeVertex)) := by
  have hh := measure_infiniteHit_translate μ a hμ (latticeBox (0,0) r : Set LatticeVertex)
  rwa [latticeTranslate_image_box_zero] at hh

/-- Positive hitting probability of the common core and dual-induced arm decay
force every balanced cell away from Left, uniformly over large rectangles. -/
theorem balanced_cells_eventually_far_left_of_positive_core
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (r : ℕ) (hr : 0 < μ.real (infiniteHit (latticeBox (0,0) r : Set LatticeVertex))) :
    ∀ M : ℕ, ∃ N : ℕ, ∀ W H : ℕ, N < W → 2*N+2 < H →
      ∀ v x y : Fin (W+1) × Fin (H+1),
        RectangleSeedBalancedCell μ W H (2*r+2) v x y → M < v.1.val := by
  intro M
  let θ := μ.real (infiniteHit (latticeBox (0,0) r : Set LatticeVertex))
  have hlim := halfPlane_arm_real_probability_tendsto_zero μ htranslation hFKG hunique hinfinite
    (halfPlaneRectangleSeeds (M+1+(2*r+2)) (2*r+2))
  have he := (tendsto_order.mp hlim).2 (θ/4) (by dsimp [θ]; linarith)
  obtain ⟨N,hN⟩ := he.exists
  refine ⟨N,?_⟩
  intro W H hW hH v x y hcell
  by_contra hnot
  have hnear : v.1.val ≤ M := Nat.le_of_not_gt hnot
  have hh := balanced_cell_near_left_core_probability_le_four_arms μ htranslation W H M r N hW hH v x y hcell hnear
  have hc := measure_infiniteHit_latticeBox_translate μ
    ((v.1.val:ℤ)+(r:ℤ)+1,(v.2.val:ℤ)+(r:ℤ)+1) (htranslation _) r
  have hcR := congrArg ENNReal.toReal hc
  change μ.real (infiniteHit (latticeBox ((v.1.val:ℤ)+(r:ℤ)+1,(v.2.val:ℤ)+(r:ℤ)+1) r : Set LatticeVertex)) = θ at hcR
  rw [hcR] at hh
  linarith

/-- Almost-sure original infinity supplies positive common cores at every
sufficiently large radius, so the actual left bulk-escape statement holds at
all those radii. No rectangle-local uniqueness is used before escape. -/
theorem balanced_cells_eventually_far_left
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ M : ℕ, ∃ N : ℕ, ∀ W H : ℕ, N < W → 2*N+2 < H →
      ∀ v x y : Fin (W+1) × Fin (H+1),
        RectangleSeedBalancedCell μ W H (2*r+2) v x y → M < v.1.val := by
  have hθ : Tendsto (fun r : ℕ => μ.real (infiniteHit (latticeBox (0,0) r : Set LatticeVertex))) atTop (𝓝 1) := by
    have hh := ENNReal.continuousAt_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤) |>.tendsto.comp
      (infiniteHit_box_probability_tendsto_one μ hinfinite)
    simpa only [Function.comp_def,Measure.real_def,ENNReal.toReal_one] using hh
  obtain ⟨R,hR⟩ := eventually_atTop.mp ((tendsto_order.mp hθ).1 0 zero_lt_one)
  refine ⟨R,?_⟩
  intro r hr
  exact balanced_cells_eventually_far_left_of_positive_core μ htranslation hFKG hunique hdualInfinite r (hR r hr)

end
end PottsContinuity.PlanarTopology
