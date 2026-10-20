module

public import PottsContinuity.PlanarTopology.DRTHeightSelector
public import PottsContinuity.PlanarTopology.DRTVerticalFixedHeight
public import PottsContinuity.BD12.RectangleHeightMonotone
public import PottsContinuity.BD12.RectangleWidthTruncation

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite BD12 Filter Topology
noncomputable section

theorem verticalRectangle_antitone_height (a : LatticeVertex) (w h H : ℕ) (hh : h ≤ H) :
    verticalRectangle a w H ⊆ verticalRectangle a w h := by
  intro ω hω
  have ht := verticalRectangle_transpose a w H ω hω
  have hs := horizontalRectangle_mono_width a.swap h H w hh ht
  exact (Set.ext_iff.mp (horizontalRectangle_transpose_preimage a w h) ω).mp hs

theorem verticalRectangle_zero_height_eq_univ (w : ℕ) : verticalRectangle (0,0) w 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  let u : RectangleVertex (0,0) w 0 := ⟨(0,0),by simp [mem_latticeRectangle]⟩
  exact ⟨u,u,rfl,rfl,SimpleGraph.Reachable.refl u⟩

/-- The actual crossing profiles have consecutive balanced heights tending
to infinity. Width n+1 retains every positive width, without a zero-width row. -/
theorem exists_actual_balanced_height_tendsto_atTop
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hdualUnique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) :
    ∃ k : ℕ → ℕ, (∀ n,
      μ.real (horizontalRectangle (0,0) (n+1) (k n)) ≤ μ.real (verticalRectangle (0,0) (n+1) (k n)) ∧
      μ.real (verticalRectangle (0,0) (n+1) (k n+1)) < μ.real (horizontalRectangle (0,0) (n+1) (k n+1))) ∧
      Tendsto k atTop atTop := by
  let h := fun n k : ℕ => μ.real (horizontalRectangle (0,0) (n+1) k)
  let v := fun n k : ℕ => μ.real (verticalRectangle (0,0) (n+1) k)
  have hvzero (w : ℕ) : μ.real (verticalRectangle (0,0) w 0) = 1 := by
    rw [verticalRectangle_zero_height_eq_univ]
    simp [Measure.real_def]
  have hmono : ∀ n, Monotone (h n) := by
    intro n k K hk
    exact measureReal_mono (horizontalRectangle_mono_height (0,0) (n+1) k K hk)
  have vanti : ∀ n, Antitone (v n) := by
    intro n k K hk
    exact measureReal_mono (verticalRectangle_antitone_height (0,0) (n+1) k K hk)
  have hzero : ∀ n, h n 0 ≤ v n 0 := by
    intro n
    change μ.real (horizontalRectangle (0,0) (n+1) 0) ≤ μ.real (verticalRectangle (0,0) (n+1) 0)
    rw [hvzero]
    exact measureReal_le_one
  have hcross : ∀ n, ∃ K, v n K < h n K := by
    intro n
    have hhl := horizontalRectangle_fixed_width_real_probability_tendsto_one μ htranslation hFKG hunique hinfinite n
    have hvl : Tendsto (fun K : ℕ => μ.real (verticalRectangle (0,0) (n+1) K)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mp
        (verticalRectangle_fixed_width_real_probability_tendsto_zero μ htranslation hFKG hdualUnique hdualInfinite (n+1))
    have he₁ := (tendsto_order.mp hhl).1 (1/2) (by norm_num : (1/2:ℝ) < 1)
    have he₂ := (tendsto_order.mp hvl).2 (1/2) (by norm_num : (0:ℝ) < 1/2)
    obtain ⟨K,hK₁,hK₂⟩ := (he₁.and he₂).exists
    exact ⟨K,by dsimp [v,h]; linarith⟩
  have hfixed : ∀ K, Tendsto (fun n => h n K) atTop (𝓝 0) := by
    intro K
    exact horizontalRectangle_fixed_height_real_probability_tendsto_zero μ htranslation hFKG hdualUnique hdualInfinite K
  have vfixed : ∀ K, Tendsto (fun n => v n K) atTop (𝓝 1) := by
    intro K
    cases K with
    | zero =>
      change Tendsto (fun n : ℕ => μ.real (verticalRectangle (0,0) (n+1) 0)) atTop (𝓝 1)
      simp only [hvzero]
      exact tendsto_const_nhds
    | succ K =>
      exact (tendsto_add_atTop_iff_nat 1).mpr
        (verticalRectangle_fixed_height_real_probability_tendsto_one μ htranslation hFKG hunique hinfinite K)
  exact exists_balanced_height_tendsto_atTop_of_fixedHeightLimits h v hmono vanti hzero hcross hfixed vfixed

end
end PottsContinuity.PlanarTopology
