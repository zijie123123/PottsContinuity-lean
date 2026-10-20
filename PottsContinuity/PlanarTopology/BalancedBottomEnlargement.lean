module

public import PottsContinuity.PlanarTopology.BalancedCellInteriorWitness
public import PottsContinuity.PlanarTopology.VerticalShiftGluing
public import PottsContinuity.PlanarTopology.SeedShiftMarkedBox

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite BD12 Filter Topology
open scoped ENNReal
noncomputable section

/-- A high Bottom probability at a balanced seed produces a high vertical
crossing probability after any fixed integral vertical enlargement. -/
theorem balanced_bottom_connection_enlarges_to_vertical
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hdualUnique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent)
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∃ N : ℕ, ∀ W H : ℕ, N < W → N < H →
      ∀ v x y : Fin (W+1) × Fin (H+1), RectangleSeedBalancedCell μ W H (2*r+2) v x y →
        1-ε < rectangleSeedBottomProbability μ W H (2*r+2) v →
          1-5*ε < μ.real (verticalRectangle (0,0) (W+(2*r+2)) (H+(2*r+2)+d)) := by
  obtain ⟨RU,hU⟩ := balanced_cells_uniform_interior_local_uniqueness μ htranslation hFKG
    hdualUnique hdualInfinite hunique hinfinite
  have hθ : Tendsto (fun r : ℕ => μ.real (infiniteHit (latticeBox (0,0) r : Set LatticeVertex))) atTop (𝓝 1) := by
    have hh := ENNReal.continuousAt_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤) |>.tendsto.comp
      (infiniteHit_box_probability_tendsto_one μ hinfinite)
    simpa only [Function.comp_def,Measure.real_def,ENNReal.toReal_one] using hh
  obtain ⟨RI,hI⟩ := eventually_atTop.mp ((tendsto_order.mp hθ).1 (1-ε) (by linarith))
  refine ⟨max RU RI,?_⟩
  intro r hr
  let s := 2*r+2
  let S₀ := latticeBox (0,0) (s+d+1)
  obtain ⟨T,hST,N,hN⟩ := hU r (le_trans (le_max_left _ _) hr) S₀ ε hε
  refine ⟨N,?_⟩
  intro W H hW hH v x y hc hbottom
  obtain ⟨hTR,hinterior,hlocal⟩ := hN W H hW hH v x y hc
  let a : LatticeVertex := ((v.1.val:ℤ),(v.2.val:ℤ))
  let S := S₀.image (latticeTranslate a)
  let T' := T.image (latticeTranslate a)
  let C := (latticeBox ((v.1.val:ℤ)+(r:ℤ)+1,(v.2.val:ℤ)+(r:ℤ)+1) r : Set LatticeVertex)
  have hVS : (PD.FK.latticeRectangle ((v.1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex) ⊆ S := by
    exact seed_subset_translated_marked_box W H s d v v
      ⟨Nat.le_succ _,Nat.le_succ _⟩ ⟨Nat.le_succ _,Nat.le_succ _⟩
  have hYS : (PD.FK.latticeRectangle ((y.1.val:ℤ),(y.2.val:ℤ)) s s : Set LatticeVertex) ⊆ S :=
    seed_subset_translated_marked_box W H s d v y hc.top_close_fst hc.top_close_snd
  have hshiftS : latticeTranslate (0,(d:ℤ)) ''
      (PD.FK.latticeRectangle ((y.1.val:ℤ),(y.2.val:ℤ)) s s : Set LatticeVertex) ⊆ S :=
    seed_vertical_shift_subset_translated_marked_box W H s d d le_rfl v y hc.top_close_fst hc.top_close_snd
  have hTR' : (T' : Set LatticeVertex) ⊆ PD.FK.latticeRectangle (0,0) (W+s) (H+s) := by
    intro z hz
    simpa only [s,Nat.add_assoc,Finset.mem_coe] using hTR hz
  have hint : ∀ z ∈ T', 0 < z.2 ∧ z.2 < ((H+s:ℕ):ℤ) := by
    intro z hz
    have hh := hinterior z hz
    simpa only [s,Nat.add_assoc] using hh.2.2
  have hbound := vertical_shift_gluing_probability_lower μ htranslation W H s d v y C S T'
    (balanced_cell_core_subset_top_seed hc) hVS hYS hshiftS hTR' hint hc.top_ge_bottom
  have heq : μ.real (infiniteHit C) = μ.real (infiniteHit (latticeBox (0,0) r : Set LatticeVertex)) := by
    have hh := congrArg ENNReal.toReal (measure_infiniteHit_latticeBox_translate μ
      ((v.1.val:ℤ)+(r:ℤ)+1,(v.2.val:ℤ)+(r:ℤ)+1) (htranslation _) r)
    simpa only [Measure.real_def] using hh
  rw [heq] at hbound
  have hcore := hI r (le_trans (le_max_right _ _) hr)
  change 1-ε < μ.real (finiteLocalUniquenessEvent S T') at hlocal
  change 1-5*ε < μ.real (verticalRectangle (0,0) (W+s) (H+s+d))
  linarith

end
end PottsContinuity.PlanarTopology
