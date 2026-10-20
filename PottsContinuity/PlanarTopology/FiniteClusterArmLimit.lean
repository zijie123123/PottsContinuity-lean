module

public import PottsContinuity.PlanarTopology.HalfPlaneClusterEvents
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory Filter Topology
noncomputable section

/-- An actual sampled-graph connection from a marked root to outside a target set. -/
def sampledGraphArmEvent {Ω V : Type*} (G : Ω → SimpleGraph V) (S : Finset V) (F : Set V) : Set Ω :=
  {ω | ∃ u ∈ S, ∃ v, v ∉ F ∧ (G ω).Reachable u v}

theorem sampledGraphArmEvent_measurableSet {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    (G : Ω → SimpleGraph V) (hG : ∀ u v, MeasurableSet {ω | (G ω).Adj u v})
    (S : Finset V) (F : Set V) : MeasurableSet (sampledGraphArmEvent G S F) := by
  classical
  have hm (u v : V) : MeasurableSet {ω | u ∈ S ∧ v ∉ F ∧ (G ω).Reachable u v} := by
    by_cases hu : u ∈ S <;> by_cases hv : v ∉ F
    · simpa [hu,hv] using measurableSet_sampledGraph_reachable G hG u v
    · simp [hv]
    · simp [hu]
    · simp [hu]
  convert MeasurableSet.iUnion (fun u => MeasurableSet.iUnion (hm u)) using 1
  ext ω
  simp only [sampledGraphArmEvent,Set.mem_ofPred_eq,Set.mem_iUnion]
  constructor
  · rintro ⟨u,hu,v,hv,hconn⟩
    exact ⟨u,v,hu,hv,hconn⟩
  · rintro ⟨u,v,hu,hv,hconn⟩
    exact ⟨u,hu,v,hv,hconn⟩

/-- Finite actual marked components cannot leave every set of an increasing
exhaustion. No independence or finite-energy assumption is involved. -/
theorem sampledGraphArmEvent_probability_tendsto_zero {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    (μ : Measure Ω) [IsFiniteMeasure μ] (G : Ω → SimpleGraph V)
    (hG : ∀ u v, MeasurableSet {ω | (G ω).Adj u v}) (S : Finset V)
    (F : ℕ → Set V) (hF : Monotone F) (hcover : ∀ v, ∃ n, v ∈ F n)
    (hfinite : ∀ᵐ ω ∂μ, ∀ u ∈ S, {v | (G ω).Reachable u v}.Finite) :
    Tendsto (fun n : ℕ => μ (sampledGraphArmEvent G S (F n))) atTop (𝓝 0) := by
  classical
  let E := fun n : ℕ => sampledGraphArmEvent G S (F n)
  have hmono : Antitone E := by
    rintro n m hnm ω ⟨u,hu,v,hv,hconn⟩
    exact ⟨u,hu,v,(fun hvn => hv (hF hnm hvn)),hconn⟩
  have hzero : μ (⋂ n, E n) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hfinite] with ω hω
    intro he
    let W := ⋃ u ∈ (S : Set V), {v | (G ω).Reachable u v}
    have hW : W.Finite := S.finite_toSet.biUnion (fun u hu => hω u hu)
    have hev : ∀ᶠ n : ℕ in atTop, ∀ v ∈ W, v ∈ F n := by
      apply hW.eventually_all.mpr
      intro v hv
      obtain ⟨N,hN⟩ := hcover v
      filter_upwards [eventually_ge_atTop N] with n hn
      exact hF hn hN
    obtain ⟨n,hn⟩ := hev.exists
    obtain ⟨u,hu,v,hv,hconn⟩ := Set.mem_iInter.mp he n
    exact hv (hn v (Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,hconn⟩⟩))
  have hh := tendsto_measure_iInter_atTop (μ := μ)
      (fun n => (sampledGraphArmEvent_measurableSet G hG S (F n)).nullMeasurableSet)
      hmono ⟨0,measure_ne_top μ _⟩
  change Tendsto (fun n : ℕ => μ (E n)) atTop (𝓝 (μ (⋂ n, E n))) at hh
  rw [hzero] at hh
  exact hh

end
end PottsContinuity.PlanarTopology
