module

public import PottsContinuity.PlanarTopology.HalfPlaneEvents
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Star
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- An actual graph component is infinite precisely when it reaches outside
every finite set of vertices. -/
theorem sampledGraph_infinite_iff_escape {V : Type*} (G : SimpleGraph V) (u : V) :
    {v | G.Reachable u v}.Infinite ↔ ∀ F : Finset V, ∃ v, v ∉ F ∧ G.Reachable u v := by
  classical
  constructor
  · intro hi F
    obtain ⟨v,hv,hvF⟩ := hi.exists_notMem_finset F
    exact ⟨v,hvF,hv⟩
  · intro he hf
    obtain ⟨v,hvF,hv⟩ := he hf.toFinset
    exact hvF (hf.mem_toFinset.mpr hv)

/-- Infinite-component membership is measurable for every countable sampled
graph with measurable adjacency. -/
theorem measurableSet_sampledGraph_infiniteAt {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    (G : Ω → SimpleGraph V) (hG : ∀ u v, MeasurableSet {ω | (G ω).Adj u v}) (u : V) :
    MeasurableSet {ω | {v | (G ω).Reachable u v}.Infinite} := by
  classical
  have hm (F : Finset V) : MeasurableSet {ω | ∃ v, v ∉ F ∧ (G ω).Reachable u v} := by
    have hv (v : V) : MeasurableSet {ω | v ∉ F ∧ (G ω).Reachable u v} := by
      by_cases h : v ∉ F
      · simpa [h] using measurableSet_sampledGraph_reachable G hG u v
      · simp [h]
    convert MeasurableSet.iUnion hv using 1
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  convert MeasurableSet.iInter hm using 1
  ext ω
  simp only [Set.mem_ofPred_eq,Set.mem_iInter,sampledGraph_infinite_iff_escape]

/-- Infinite membership in the actual original open half-plane component. -/
def halfPlaneInfiniteAt (u : {z : LatticeVertex // 0 ≤ z.1}) : Set LatticeConfiguration :=
  {ω | {v | ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable u v}.Infinite}

theorem halfPlaneInfiniteAt_measurableSet (u : {z : LatticeVertex // 0 ≤ z.1}) :
    MeasurableSet (halfPlaneInfiniteAt u) := by
  apply measurableSet_sampledGraph_infiniteAt
    (fun ω : LatticeConfiguration => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1})
  intro v w
  exact measurableSet_open_adj v.val w.val

/-- Both primal vertices of the unit boundary segment have finite actual
half-plane components. -/
def halfPlaneFiniteUnitEvent : Set LatticeConfiguration :=
  (halfPlaneInfiniteAt ⟨(0,0),by norm_num⟩ ∪ halfPlaneInfiniteAt ⟨(0,1),by norm_num⟩)ᶜ

theorem halfPlaneFiniteUnitEvent_measurableSet : MeasurableSet halfPlaneFiniteUnitEvent :=
  ((halfPlaneInfiniteAt_measurableSet _).union (halfPlaneInfiniteAt_measurableSet _)).compl

theorem mem_halfPlaneFiniteUnitEvent_iff (ω : LatticeConfiguration) :
    ω ∈ halfPlaneFiniteUnitEvent ↔ ∀ y : ℤ, (y = 0 ∨ y = 1) →
      {z : {z : LatticeVertex // 0 ≤ z.1} |
        ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable
          ⟨(0,y),by norm_num⟩ z}.Finite := by
  change (¬(_ ∨ _)) ↔ _
  rw [not_or]
  constructor
  · rintro ⟨h0,h1⟩ y (rfl | rfl)
    · exact Set.not_infinite.mp h0
    · exact Set.not_infinite.mp h1
  · intro h
    exact ⟨Set.not_infinite.mpr (h 0 (Or.inl rfl)),Set.not_infinite.mpr (h 1 (Or.inr rfl))⟩

end
end PottsContinuity.PlanarTopology
