module

public import PottsContinuity.PlanarTopology.BalancedCellBulkEscape
public import PottsContinuity.PlanarTopology.LocalUniquenessProbability
public import PottsContinuity.PlanarTopology.LocalUniquenessTranslation

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite Filter Topology
noncomputable section

theorem translated_finite_set_subset_rectangle_of_anchor_margins
    (T : Finset LatticeVertex) (W H s : ℕ) (v : Fin (W+1) × Fin (H+1))
    (hleft : subgraphBoxRadius T < v.1.val) (hbottom : subgraphBoxRadius T < v.2.val)
    (hright : subgraphBoxRadius T < W-v.1.val) (htop : subgraphBoxRadius T < H-v.2.val) :
    T.image (latticeTranslate ((v.1.val:ℤ),(v.2.val:ℤ))) ⊆ PD.FK.latticeRectangle (0,0) (W+s) (H+s) := by
  intro z hz
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
  have hb := (mem_latticeBox (0,0) u (subgraphBoxRadius T)).mp (subgraph_subset_boxRadius T hu)
  apply (mem_latticeRectangle (0,0) _ (W+s) (H+s)).mpr
  dsimp [latticeTranslate] at *
  have hv₁ := v.1.isLt
  have hv₂ := v.2.isLt
  omega

/-- The translated finite local-uniqueness event has at least the original
probability under a translation-invariant law, retaining its global witnesses. -/
theorem measure_finiteLocalUniquenessEvent_translate_ge (μ : Measure LatticeConfiguration)
    (a : LatticeVertex) (hμ : μ.map (edgeTranslate a) = μ) (S T : Finset LatticeVertex) :
    μ (finiteLocalUniquenessEvent S T) ≤ μ (finiteLocalUniquenessEvent
      (S.image (latticeTranslate a)) (T.image (latticeTranslate a))) := by
  have hs : finiteLocalUniquenessEvent S T ⊆ edgeTranslate a ⁻¹'
      finiteLocalUniquenessEvent (S.image (latticeTranslate a)) (T.image (latticeTranslate a)) := by
    intro ω hω
    exact finiteLocalUniquenessEvent_translate a S T ω hω
  have hh := measure_mono (μ := μ) hs
  rwa [← Measure.map_apply (edgeTranslate_measurable _)
    (finiteLocalUniquenessEvent_measurableSet _ _),hμ] at hh

/-- A finite local witness connects marked roots inside every larger domain.
The witnesses reaching outside T remain global open paths, not paths required
to stay in the larger domain. -/
theorem finiteLocalUniquenessEvent_connects_in_domain
    (S T : Finset LatticeVertex) (D : Set LatticeVertex) (hTD : (T : Set LatticeVertex) ⊆ D)
    (ω : LatticeConfiguration) (hω : ω ∈ finiteLocalUniquenessEvent S T)
    (u v : {z // z ∈ D}) (hu : u.val ∈ S) (hv : v.val ∈ S)
    (hex : ∃ x, x ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable u.val x)
    (hey : ∃ y, y ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable v.val y) :
    ((PD.rcInfiniteOpenGraph ω).induce D).Reachable u v := by
  let uT : {z // z ∈ T} := ⟨u.val,hω.1 hu⟩
  let vT : {z // z ∈ T} := ⟨v.val,hω.1 hv⟩
  let f : (PD.rcInfiniteOpenGraph ω).induce (T : Set LatticeVertex) →g
      (PD.rcInfiniteOpenGraph ω).induce D :=
    { toFun := fun z => ⟨z.val,hTD z.property⟩, map_rel' := fun h => h }
  exact (hω.2 uT vT hu hv hex hey).map f

/-- At every sufficiently large fixed seed radius, each balanced anchor admits
a translated fixed local witness lying inside its rectangle, with probability
arbitrarily close to one uniformly in that rectangle and anchor. -/
theorem balanced_cells_uniform_local_uniqueness
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
          1-ε < μ.real (finiteLocalUniquenessEvent
            (S.image (latticeTranslate a)) (T.image (latticeTranslate a))) := by
  obtain ⟨R,hR⟩ := balanced_cells_eventually_far_all_sides μ htranslation hFKG hdualUnique hdualInfinite hinfinite
  refine ⟨R,?_⟩
  intro r hr S ε hε
  have hlim := local_uniqueness_real_probability_tendsto_one μ hunique S
  obtain ⟨k,hk⟩ := ((tendsto_order.mp hlim).1 (1-ε) (by linarith)).exists
  let T := S ∪ latticeBox (0,0) k
  obtain ⟨N,hN⟩ := hR r hr (subgraphBoxRadius T)
  refine ⟨T,Finset.subset_union_left, N,?_⟩
  intro W H hW hH v x y hc
  obtain ⟨hl,hb,hr,ht⟩ := hN W H hW hH v x y hc
  refine ⟨?_,?_⟩
  · simpa only [Nat.add_assoc] using
      translated_finite_set_subset_rectangle_of_anchor_margins T W H (2*r+2) v hl hb hr ht
  · apply lt_of_lt_of_le hk
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_finiteLocalUniquenessEvent_translate_ge
      μ ((v.1.val:ℤ),(v.2.val:ℤ)) (htranslation _) S T)

end
end PottsContinuity.PlanarTopology
