module

public import PottsContinuity.PlanarTopology.BalancedCellFiniteWitness

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

theorem translated_finite_set_strict_rectangle_interior
    (T : Finset LatticeVertex) (W H s : ℕ) (v : Fin (W+1) × Fin (H+1))
    (hleft : subgraphBoxRadius T < v.1.val) (hbottom : subgraphBoxRadius T < v.2.val)
    (hright : subgraphBoxRadius T < W-v.1.val) (htop : subgraphBoxRadius T < H-v.2.val) :
    ∀ z ∈ T.image (latticeTranslate ((v.1.val:ℤ),(v.2.val:ℤ))),
      0 < z.1 ∧ z.1 < ((W+s:ℕ):ℤ) ∧ 0 < z.2 ∧ z.2 < ((H+s:ℕ):ℤ) := by
  intro z hz
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
  have hb := (mem_latticeBox (0,0) u (subgraphBoxRadius T)).mp (subgraph_subset_boxRadius T hu)
  have hv₁ := v.1.isLt
  have hv₂ := v.2.isLt
  dsimp [latticeTranslate] at *
  omega

/-- The high-probability translated local witness lies strictly inside R,
so every literal side endpoint provides a global outside-witness. -/
theorem balanced_cells_uniform_interior_local_uniqueness
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hdualUnique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ S : Finset LatticeVertex, ∀ ε : ℝ, 0 < ε →
      ∃ T : Finset LatticeVertex, S ⊆ T ∧ ∃ N : ℕ, ∀ W H : ℕ, N < W → N < H →
        ∀ v x y : Fin (W+1) × Fin (H+1), RectangleSeedBalancedCell μ W H (2*r+2) v x y →
          let a : LatticeVertex := ((v.1.val:ℤ),(v.2.val:ℤ))
          T.image (latticeTranslate a) ⊆ PD.FK.latticeRectangle (0,0) (W+2*r+2) (H+2*r+2) ∧
          (∀ z ∈ T.image (latticeTranslate a),
            0 < z.1 ∧ z.1 < ((W+2*r+2:ℕ):ℤ) ∧ 0 < z.2 ∧ z.2 < ((H+2*r+2:ℕ):ℤ)) ∧
          1-ε < μ.real (finiteLocalUniquenessEvent
            (S.image (latticeTranslate a)) (T.image (latticeTranslate a))) := by
  obtain ⟨RL,hL⟩ := balanced_cells_uniform_local_uniqueness μ htranslation hFKG hdualUnique hdualInfinite hunique hinfinite
  obtain ⟨RB,hB⟩ := balanced_cells_eventually_far_all_sides μ htranslation hFKG hdualUnique hdualInfinite hinfinite
  refine ⟨max RL RB,?_⟩
  intro r hr S ε hε
  obtain ⟨T,hST,NL,hNL⟩ := hL r (le_trans (le_max_left _ _) hr) S ε hε
  obtain ⟨NB,hNB⟩ := hB r (le_trans (le_max_right _ _) hr) (subgraphBoxRadius T)
  refine ⟨T,hST,NL+NB,?_⟩
  intro W H hW hH v x y hc
  obtain ⟨hinside,hprob⟩ := hNL W H (by omega) (by omega) v x y hc
  obtain ⟨hl,hb,hr,ht⟩ := hNB W H (by omega) (by omega) v x y hc
  refine ⟨hinside,?_,hprob⟩
  simpa only [Nat.add_assoc] using
    translated_finite_set_strict_rectangle_interior T W H (2*r+2) v hl hb hr ht

end
end PottsContinuity.PlanarTopology
