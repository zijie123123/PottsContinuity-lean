module

public import PottsContinuity.PlanarTopology.UniqueClusterLocalization
public import PottsContinuity.BD12.RectangleOpenGraphs
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

/-- Both marked roots reaching outside T must be connected using only T.
This is a local uniqueness event for the actual sampled open graph. -/
def finiteLocalUniquenessEvent (S T : Finset LatticeVertex) : Set LatticeConfiguration :=
  {ω | S ⊆ T ∧ ∀ u v : {z // z ∈ T}, u.val ∈ S → v.val ∈ S →
    (∃ x, x ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable u.val x) →
    (∃ y, y ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable v.val y) →
      ((PD.rcInfiniteOpenGraph ω).induce (T : Set LatticeVertex)).Reachable u v}

theorem measurableSet_induced_open_reachable (T : Finset LatticeVertex)
    (u v : {z // z ∈ T}) :
    MeasurableSet {ω : LatticeConfiguration |
      ((PD.rcInfiniteOpenGraph ω).induce (T : Set LatticeVertex)).Reachable u v} := by
  have hh := (embeddedRestriction_isCylinder (PD.squareLattice.induce (T : Set LatticeVertex))
    (frozenEdgeEmbedding T) {A | ActualConnected _ A u v}).measurableSet
  convert hh using 1
  ext ω
  change _ ↔ (openGraph _ (embeddedRestriction _ _ ω)).Reachable u v
  rw [embeddedRestriction_domainGraph]
  rfl

theorem measurableSet_reaches_outside (T : Finset LatticeVertex) (u : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration |
      ∃ x, x ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable u x} := by
  have hm (x : LatticeVertex) : MeasurableSet {ω : LatticeConfiguration |
      x ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable u x} := by
    by_cases hx : x ∉ T
    · simpa [hx] using measurableSet_open_reachable u x
    · simp only [hx,false_and,Set.ofPred_false,MeasurableSet.empty]
  convert MeasurableSet.iUnion hm using 1
  ext ω
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq]

theorem finiteLocalUniquenessEvent_measurableSet (S T : Finset LatticeVertex) :
    MeasurableSet (finiteLocalUniquenessEvent S T) := by
  classical
  by_cases hST : S ⊆ T
  · have hm (u v : {z // z ∈ T}) : MeasurableSet {ω : LatticeConfiguration |
        u.val ∈ S → v.val ∈ S →
        (∃ x, x ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable u.val x) →
        (∃ y, y ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable v.val y) →
          ((PD.rcInfiniteOpenGraph ω).induce (T : Set LatticeVertex)).Reachable u v} := by
      by_cases hu : u.val ∈ S
      · by_cases hv : v.val ∈ S
        · have hh := ((measurableSet_reaches_outside T u.val).inter
            (measurableSet_reaches_outside T v.val)).compl.union
              (measurableSet_induced_open_reachable T u v)
          convert hh using 1
          ext ω
          simp only [hu,hv,true_implies,Set.mem_union,Set.mem_compl_iff,Set.mem_inter_iff,Set.mem_ofPred_eq]
          constructor
          · intro h
            by_cases ha : ∃ x, x ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable u.val x
            · by_cases hb : ∃ y, y ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable v.val y
              · exact Or.inr (h ha hb)
              · exact Or.inl (fun h' => hb h'.2)
            · exact Or.inl (fun h' => ha h'.1)
          · intro h ha hb
            rcases h with h | h
            · exact (h ⟨ha,hb⟩).elim
            · exact h
        · simp [hv]
      · simp [hu]
    convert MeasurableSet.iInter (fun u => MeasurableSet.iInter (hm u)) using 1
    ext ω
    simp only [finiteLocalUniquenessEvent,Set.mem_ofPred_eq,hST,true_and,Set.mem_iInter]
  · have he : finiteLocalUniquenessEvent S T = ∅ := by
      ext ω
      simp only [finiteLocalUniquenessEvent,Set.mem_ofPred_eq,hST,false_and,Set.mem_empty_iff_false]
    rw [he]
    exact MeasurableSet.empty

/-- Every configuration with at most one infinite component has a finite
local-uniqueness witness around every finite set of marked vertices. -/
theorem unique_cluster_mem_finiteLocalUniquenessEvent (ω : LatticeConfiguration)
    (hω : atMostOneInfiniteCluster ω) (S : Finset LatticeVertex) :
    ∃ T : Finset LatticeVertex, ω ∈ finiteLocalUniquenessEvent S T := by
  obtain ⟨T,hST,hT⟩ := unique_cluster_has_finite_local_witness ω hω S
  exact ⟨T,hST,hT (T : Set LatticeVertex) Set.Subset.rfl⟩

end
end PottsContinuity.PlanarTopology
