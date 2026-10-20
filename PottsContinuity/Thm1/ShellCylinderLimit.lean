module

public import PottsContinuity.Thm1.ShellOuterCylinderBridge
public import PottsContinuity.PD.FK.WiredBoxLaw
public import PottsContinuity.PD.Defs.IsRCInfiniteVolumeLimit
public import PottsContinuity.PD.RCInfinite.Cylinders
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

private theorem pottsESSupport_mono {V W : Finset (ℤ × ℤ)}
    (hVW : V ⊆ W) : pottsESSupport V ⊆ pottsESSupport W := by
  intro x hx
  unfold pottsESSupport at hx ⊢
  rcases Finset.mem_union.mp hx with hxV | hxN
  · exact Finset.mem_union.mpr (Or.inl (hVW hxV))
  · obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hxN
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_biUnion.mpr ⟨v, hVW hv, hxv⟩

private theorem pottsESSupport_exhaustive
    (V : ℕ → Finset (ℤ × ℤ))
    (hExhaust : ∀ x, ∃ n, x ∈ V n) :
    ∀ x, ∃ n, x ∈ pottsESSupport (V n) := by
  intro x
  obtain ⟨n, hn⟩ := hExhaust x
  exact ⟨n, Finset.mem_union.mpr (Or.inl hn)⟩

private theorem pottsES_wiredBoxReal_allOpen (θ : Parameters) (r : ℕ)
    (F : Finset PD.FK.squareLattice.edgeSet) :
    (wiredBoxProbabilityMeasure θ (0, 0) r : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) =
      (measure (boxGraph (0, 0) r) θ
        (BoundaryCondition.wired (boxVertexBoundary (0, 0) r))
        (wiredBoxCylinderEvent (0, 0) r F)).toReal := by
  change ENNReal.toReal
      ((wiredBoxProbabilityMeasure θ (0, 0) r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F)) = _
  exact congrArg ENNReal.toReal (wiredBoxProbabilityMeasure_allOpen θ (0, 0) r F)

/-- Along any increasing exhaustive vertex sequence, the shell-graph
Edwards--Sokal wired law has the same limit as the wired random-cluster law on
every finite all-open edge cylinder. -/
theorem pottsESWiredShell_allOpenProbability_tendsto
    (θ : Parameters) (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ)
    (F : Finset PD.FK.squareLattice.edgeSet) :
    Tendsto
      (fun n => (measure (pottsESGraph (V n)) θ (pottsESBoundaryCondition (V n))
        (pottsESAllOpenCylinderEvent (V n) F)).toReal)
      atTop (𝓝 (μ.real (LatticeConfiguration.allOpen F))) := by
  let R : ℕ → ℕ := fun n => pottsESShellComparisonRadius (V n)
  let shellProbability : ℕ → ℝ := fun n =>
    (measure (pottsESGraph (V n)) θ (pottsESBoundaryCondition (V n))
      (pottsESAllOpenCylinderEvent (V n) F)).toReal
  let boxProbability : ℕ → ℝ := fun r =>
    (wiredBoxProbabilityMeasure θ (0, 0) r : Measure LatticeConfiguration).real
      (LatticeConfiguration.allOpen F)
  have hSupportNest : ∀ n, pottsESSupport (V n) ⊆ pottsESSupport (V (n + 1)) :=
    fun n => pottsESSupport_mono (hNest n)
  have hSupportExhaust : ∀ x, ∃ n, x ∈ pottsESSupport (V n) :=
    pottsESSupport_exhaustive V hExhaust
  have hRadius : Tendsto (fun n => subgraphBoxRadius (pottsESSupport (V n))) atTop atTop :=
    subgraphBoxRadius_tendsto hSupportNest hSupportExhaust
  have hR : Tendsto R atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    have heventually := hRadius.eventually (Filter.eventually_ge_atTop b)
    filter_upwards [heventually] with n hn
    dsimp [R, pottsESShellComparisonRadius]
    omega
  have hBox : Tendsto boxProbability atTop (𝓝 (μ.real (LatticeConfiguration.allOpen F))) := by
    simpa [boxProbability] using
      tendsto_cylinder_probability θ 1 μ hμ (isCylinder_allOpen F)
  have hOuter := hBox.comp hR
  obtain ⟨rF, hrF⟩ := exists_box_supporting_edge_finset F
  have hFrozenEdgeRange : ∀ e ∈ F,
      e ∈ Set.range (frozenEdgeEmbedding (latticeBox (0, 0) rF)) := by
    intro e he
    exact boxEdges_subset_frozenEdgeEmbedding_range rF (hrF e he)
  have hBoxEdgeId (r : ℕ) :
      frozenEdgeEmbedding (latticeBox (0, 0) r) = boxEdgeEmbedding (0, 0) r := rfl
  have hFBox : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding (0, 0) rF) := by
    intro e he
    rw [← hBoxEdgeId rF]
    exact hFrozenEdgeRange e he
  apply tendsto_order.2
  constructor
  · intro a ha
    have hOuterEvent := (tendsto_order.1 hOuter).1 a ha
    have hInclude := eventually_latticeBox_subset_of_exhaustion V hNest hExhaust rF
    filter_upwards [hOuterEvent, hInclude] with n hn hInc
    have hFSupport : ∀ e ∈ F, ∃ g : (pottsESGraph (V n)).edgeSet,
        ((pottsESEdgeEquiv (V n)).symm g).1 = e.1 := by
      intro e he
      obtain ⟨f, hf⟩ := Set.mem_range.mp (hFBox e he)
      obtain ⟨g, hg⟩ := pottsESBoxEdge_shellWitness (V n) rF hInc f
      exact ⟨g, hg.trans (congrArg Subtype.val hf)⟩
    have hCompare := wiredBox_allOpenProbability_le_pottsESWiredShell
      (V n) θ F hFSupport
    have hBoxId := pottsES_wiredBoxReal_allOpen θ (R n) F
    have hCompare' : boxProbability (R n) ≤ shellProbability n := by
      dsimp [boxProbability, shellProbability]
      rw [hBoxId]
      exact hCompare
    exact lt_of_lt_of_le hn hCompare'
  · intro a ha
    have hBoxEvent := (tendsto_order.1 hBox).2 a ha
    obtain ⟨r, ⟨hr, hrF⟩⟩ :=
      (hBoxEvent.and (Filter.eventually_ge_atTop rF)).exists
    have hFBoxR : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding (0, 0) r) := by
      intro e he
      rw [← hBoxEdgeId r]
      exact frozenEdgeEmbedding_range_mono
        (latticeBox_mono (0, 0) hrF) (hFrozenEdgeRange e he)
    have hInclude := eventually_latticeBox_subset_of_exhaustion V hNest hExhaust r
    filter_upwards [hInclude] with n hInc
    have hCompare := pottsESWiredShell_allOpenProbability_le_wiredBox
      (V n) θ r hInc F hFBoxR
    have hBoxId := pottsES_wiredBoxReal_allOpen θ r F
    have hCompare' : shellProbability n ≤ boxProbability r := by
      dsimp [shellProbability, boxProbability]
      rw [hBoxId]
      exact hCompare
    exact lt_of_le_of_lt hCompare' hr

end

end PottsContinuity.Thm1
