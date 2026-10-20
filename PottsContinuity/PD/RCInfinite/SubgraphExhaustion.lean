-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/SubgraphExhaustion.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.Mixing
public import PottsContinuity.PD.RCInfinite.SubgraphProbability
public import PottsContinuity.PD.RCInfinite.SurgeryEvents
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- A centered square containing a finite vertex set, with radius given by its
largest coordinate magnitude. -/
def subgraphBoxRadius (S : Finset LatticeVertex) : ℕ :=
  S.sup (fun x => max x.1.natAbs x.2.natAbs)

theorem subgraph_subset_boxRadius (S : Finset LatticeVertex) :
    S ⊆ latticeBox (0, 0) (subgraphBoxRadius S) := by
  intro x hx
  rw [mem_latticeBox]
  have hmax : max x.1.natAbs x.2.natAbs ≤ subgraphBoxRadius S := by
    exact Finset.le_sup (f := fun y => max y.1.natAbs y.2.natAbs) hx
  have hfirst : (x.1.natAbs : ℤ) ≤ subgraphBoxRadius S := by
    exact_mod_cast (le_trans (Nat.le_max_left _ _) hmax)
  have hsecond : (x.2.natAbs : ℤ) ≤ subgraphBoxRadius S := by
    exact_mod_cast (le_trans (Nat.le_max_right _ _) hmax)
  rw [Int.natCast_natAbs] at hfirst hsecond
  rcases abs_le.mp hfirst with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hsecond with ⟨hylo, hyhi⟩
  simp only [zero_sub, zero_add]
  exact ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩

theorem subgraphBoxRadius_ge_vertex (S : Finset LatticeVertex) {v : LatticeVertex}
    (hv : v ∈ S) : max v.1.natAbs v.2.natAbs ≤ subgraphBoxRadius S :=
  Finset.le_sup (f := fun x => max x.1.natAbs x.2.natAbs) hv

theorem subgraphBoxRadius_tendsto {S : ℕ → Finset LatticeVertex}
    (hnest : ∀ n, S n ⊆ S (n + 1)) (hexhaust : ∀ v, ∃ n, v ∈ S n) :
    Tendsto (fun n => subgraphBoxRadius (S n)) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := hexhaust (((b + 1 : ℕ) : ℤ), 0)
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
  have hSN : S N ⊆ S n := by
    induction hn with
    | refl => exact Finset.Subset.rfl
    | @step k hkn ih => exact ih.trans (hnest k)
  have hv : (((b + 1 : ℕ) : ℤ), 0) ∈ S n := hSN hN
  have hr := subgraphBoxRadius_ge_vertex (S n) hv
  simp only [Int.natAbs_zero, Nat.max_zero] at hr
  omega

theorem eventually_latticeBox_subset_of_exhaustion
    (S : ℕ → Finset LatticeVertex)
    (hnest : ∀ n, S n ⊆ S (n + 1)) (hexhaust : ∀ v, ∃ n, v ∈ S n)
    (r : ℕ) : ∀ᶠ n : ℕ in atTop, latticeBox (0, 0) r ⊆ S n := by
  have hev : ∀ᶠ n : ℕ in atTop, ∀ v ∈ latticeBox (0, 0) r, v ∈ S n := by
    apply (eventually_all_finset (latticeBox (0, 0) r)).2
    intro v hv
    obtain ⟨N, hN⟩ := hexhaust v
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    have hSN : S N ⊆ S n := by
      induction hn with
      | refl => exact Finset.Subset.rfl
      | @step k hkn ih => exact ih.trans (hnest k)
    exact hSN hN
  filter_upwards [hev] with n hn
  exact hn

theorem exists_box_supporting_edge_finset (F : Finset Edge) :
    ∃ r : ℕ, ∀ e ∈ F, e ∈ boxEdges (0, 0) r := by
  obtain ⟨r, hr⟩ := exists_box_containing_finset (edgeEndpoints F)
  refine ⟨r, ?_⟩
  intro e he
  rw [mem_boxEdges_iff]
  intro x hx
  apply hr x
  exact Finset.mem_biUnion.mpr ⟨e, he, by simpa [edgeEndpoints] using hx⟩

theorem boxEdges_subset_frozenEdgeEmbedding_range (r : ℕ) :
    boxEdges (0, 0) r ⊆ Set.range (frozenEdgeEmbedding (latticeBox (0, 0) r)) := by
  have hemb : frozenEdgeEmbedding (latticeBox (0, 0) r) = boxEdgeEmbedding (0, 0) r := rfl
  intro e he
  change e ∈ Set.range (boxEdgeEmbedding (0, 0) r) at he
  rw [← hemb] at he
  exact he

theorem finiteSubgraphProbabilityMeasure_real_allOpen (θ : Parameters)
    (S : Finset LatticeVertex) (i : Fin 2) (F : Finset Edge)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding S)) :
    (finiteSubgraphProbabilityMeasure θ S i : Measure LatticeConfiguration).real
      (LatticeConfiguration.allOpen F) =
      (measure (finiteLatticeGraph S) θ (frozenBoundaryCondition S i)
        (finiteSubgraphOpenEvent S F)).toReal := by
  change ENNReal.toReal ((finiteSubgraphProbabilityMeasure θ S i :
    Measure LatticeConfiguration) (LatticeConfiguration.allOpen F)) = _
  rw [finiteSubgraphProbabilityMeasure_allOpen θ S i F hF]

theorem finiteSubgraphProbabilityMeasure_free_open_mono {S T : Finset LatticeVertex}
    (θ : Parameters) (hST : S ⊆ T) (F : Finset Edge)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding S)) :
    (finiteSubgraphProbabilityMeasure θ S 0 : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) ≤
      (finiteSubgraphProbabilityMeasure θ T 0 : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) := by
  have hFT := fun e he => frozenEdgeEmbedding_range_mono hST (hF e he)
  rw [finiteSubgraphProbabilityMeasure_real_allOpen θ S 0 F hF,
    finiteSubgraphProbabilityMeasure_real_allOpen θ T 0 F hFT]
  simpa [frozenBoundaryCondition] using finiteSubgraph_free_open_mono θ hST F hF

theorem finiteSubgraphProbabilityMeasure_wired_open_antitone
    {S T : Finset LatticeVertex} (θ : Parameters) (hST : S ⊆ T)
    (F : Finset Edge) (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding S)) :
    (finiteSubgraphProbabilityMeasure θ T 1 : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) ≤
      (finiteSubgraphProbabilityMeasure θ S 1 : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) := by
  have hFT := fun e he => frozenEdgeEmbedding_range_mono hST (hF e he)
  rw [finiteSubgraphProbabilityMeasure_real_allOpen θ T 1 F hFT,
    finiteSubgraphProbabilityMeasure_real_allOpen θ S 1 F hF]
  simpa [frozenBoundaryCondition] using finiteSubgraph_wired_open_antitone θ hST F hF

/-- The finite FK laws on every nested exhaustive sequence of induced vertex
sets converge weakly to the corresponding infinite-volume box limit. -/
theorem finiteInducedSubgraphExhaustion_tendsto (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (S : ℕ → Finset LatticeVertex)
    (hnest : ∀ n, S n ⊆ S (n + 1))
    (hexhaust : ∀ v, ∃ n, v ∈ S n) :
    Tendsto (fun n => finiteSubgraphProbabilityMeasure θ (S n) i) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  classical
  let R : ℕ → ℕ := fun n => subgraphBoxRadius (S n)
  have hR : Tendsto R atTop atTop := by
    simpa [R] using subgraphBoxRadius_tendsto hnest hexhaust
  have hincludeF := eventually_latticeBox_subset_of_exhaustion S hnest hexhaust
  have hopen : ∀ F : Finset Edge, Tendsto
      (fun n => (finiteSubgraphProbabilityMeasure θ (S n) i :
        Measure LatticeConfiguration).real (LatticeConfiguration.allOpen F)) atTop
      (𝓝 (μ.real (LatticeConfiguration.allOpen F))) := by
    intro F
    obtain ⟨rF, hrF⟩ := exists_box_supporting_edge_finset F
    have hFbox : ∀ e ∈ F, e ∈ Set.range
        (frozenEdgeEmbedding (latticeBox (0, 0) rF)) := by
      intro e he
      exact boxEdges_subset_frozenEdgeEmbedding_range rF (hrF e he)
    have hbox : Tendsto
        (fun r => (boxMeasure θ i (0, 0) r : Measure LatticeConfiguration).real
          (LatticeConfiguration.allOpen F)) atTop
        (𝓝 (μ.real (LatticeConfiguration.allOpen F))) :=
      tendsto_cylinder_probability θ i μ hμ (isCylinder_allOpen F)
    have houter := hbox.comp hR
    fin_cases i
    · apply tendsto_order.2
      constructor
      · intro a ha
        obtain ⟨r, ⟨hr, hFr⟩⟩ :=
          (((tendsto_order.1 hbox).1 a ha).and
            (Filter.eventually_atTop.2 ⟨rF, fun r hr => hr⟩)).exists
        have hFAt : ∀ e ∈ F, e ∈ Set.range
            (frozenEdgeEmbedding (latticeBox (0, 0) r)) := by
          intro e he
          exact frozenEdgeEmbedding_range_mono (latticeBox_mono (0, 0) hFr)
            (hFbox e he)
        have hinclude := eventually_latticeBox_subset_of_exhaustion S hnest hexhaust r
        filter_upwards [hinclude] with n hInc
        have hnbox : a < (boxMeasure θ 0 (0, 0) r : Measure LatticeConfiguration).real
            (LatticeConfiguration.allOpen F) := hr
        have hcmp := finiteSubgraphProbabilityMeasure_free_open_mono θ hInc F hFAt
        have hboxId := finiteSubgraphProbabilityMeasure_box_allOpen θ 0 r F hFAt
        have hnbox' : a < (finiteSubgraphProbabilityMeasure θ
            (latticeBox (0, 0) r) 0 : Measure LatticeConfiguration).real
              (LatticeConfiguration.allOpen F) := by
          rw [hboxId]
          exact hnbox
        exact lt_of_lt_of_le hnbox' hcmp
      · intro a ha
        have houterEvent := (tendsto_order.1 houter).2 a ha
        filter_upwards [houterEvent, hincludeF rF] with n hn hInc
        have hOuterSet : S n ⊆ latticeBox (0, 0) (R n) := by
          simpa [R] using subgraph_subset_boxRadius (S n)
        have hFn : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding (S n)) := by
          intro e he
          exact frozenEdgeEmbedding_range_mono hInc (hFbox e he)
        have hFAt : ∀ e ∈ F, e ∈ Set.range
            (frozenEdgeEmbedding (latticeBox (0, 0) (R n))) := by
          intro e he
          exact frozenEdgeEmbedding_range_mono hOuterSet (hFn e he)
        have hSouter := finiteSubgraphProbabilityMeasure_free_open_mono θ hOuterSet F hFn
        have hOuterId := finiteSubgraphProbabilityMeasure_box_allOpen θ 0 (R n) F hFAt
        calc
          (finiteSubgraphProbabilityMeasure θ (S n) 0 :
              Measure LatticeConfiguration).real (LatticeConfiguration.allOpen F)
              ≤ (finiteSubgraphProbabilityMeasure θ (latticeBox (0, 0) (R n)) 0 :
                Measure LatticeConfiguration).real (LatticeConfiguration.allOpen F) := hSouter
          _ = (boxMeasure θ 0 (0, 0) (R n) :
                Measure LatticeConfiguration).real (LatticeConfiguration.allOpen F) := hOuterId
          _ < a := hn
    · apply tendsto_order.2
      constructor
      · intro a ha
        have houterEvent := (tendsto_order.1 houter).1 a ha
        filter_upwards [houterEvent, hincludeF rF] with n hn hInc
        have hOuterSet : S n ⊆ latticeBox (0, 0) (R n) := by
          simpa [R] using subgraph_subset_boxRadius (S n)
        have hFn : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding (S n)) := by
          intro e he
          exact frozenEdgeEmbedding_range_mono hInc (hFbox e he)
        have hFAt : ∀ e ∈ F, e ∈ Set.range
            (frozenEdgeEmbedding (latticeBox (0, 0) (R n))) := by
          intro e he
          exact frozenEdgeEmbedding_range_mono hOuterSet (hFn e he)
        have hSouter := finiteSubgraphProbabilityMeasure_wired_open_antitone
          θ hOuterSet F hFn
        have hOuterId := finiteSubgraphProbabilityMeasure_box_allOpen θ 1 (R n) F hFAt
        have hn' : a < (finiteSubgraphProbabilityMeasure θ
            (latticeBox (0, 0) (R n)) 1 : Measure LatticeConfiguration).real
              (LatticeConfiguration.allOpen F) := by
          rw [hOuterId]
          exact hn
        exact lt_of_lt_of_le hn' hSouter
      · intro a ha
        obtain ⟨r, ⟨hr, hFr⟩⟩ :=
          (((tendsto_order.1 hbox).2 a ha).and
            (Filter.eventually_atTop.2 ⟨rF, fun r hr => hr⟩)).exists
        have hFAt : ∀ e ∈ F, e ∈ Set.range
            (frozenEdgeEmbedding (latticeBox (0, 0) r)) := by
          intro e he
          exact frozenEdgeEmbedding_range_mono (latticeBox_mono (0, 0) hFr)
            (hFbox e he)
        have hinclude := eventually_latticeBox_subset_of_exhaustion S hnest hexhaust r
        filter_upwards [((tendsto_order.1 hbox).2 a ha).and hinclude]
          with n ⟨hnbox, hInc⟩
        have hcmp := finiteSubgraphProbabilityMeasure_wired_open_antitone θ hInc F hFAt
        have hboxId := finiteSubgraphProbabilityMeasure_box_allOpen θ 1 r F hFAt
        have hnbox : (finiteSubgraphProbabilityMeasure θ
            (latticeBox (0, 0) r) 1 : Measure LatticeConfiguration).real
              (LatticeConfiguration.allOpen F) < a := by
          rw [hboxId]
          exact hr
        exact lt_of_le_of_lt hcmp hnbox
  have hweak : Tendsto (fun n => finiteSubgraphProbabilityMeasure θ (S n) i)
      atTop (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) :=
    probabilityMeasures_tendsto_of_allOpen_real hopen
  simpa using hweak

end
end PottsContinuity.PD.RCInfinite
