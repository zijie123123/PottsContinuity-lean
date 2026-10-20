module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.MeasurableSpace.Basic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory
noncomputable section

/-- An exact-length finite chain in a sampled graph, including length zero. -/
def sampledGraphChain {Ω V : Type*} (G : Ω → SimpleGraph V) :
    ℕ → Ω → V → V → Prop
  | 0, _, u, v => u = v
  | n+1, ω, u, v => ∃ z, (G ω).Adj u z ∧ sampledGraphChain G n ω z v

theorem sampledGraph_reachable_iff_chain {Ω V : Type*} (G : Ω → SimpleGraph V)
    (ω : Ω) (u v : V) :
    (G ω).Reachable u v ↔ ∃ n, sampledGraphChain G n ω u v := by
  have chain_reachable {n : ℕ} {u v : V} (h : sampledGraphChain G n ω u v) :
      (G ω).Reachable u v := by
    induction n generalizing u with
    | zero => exact h ▸ SimpleGraph.Reachable.refl u
    | succ n ih =>
      obtain ⟨z,huz,hzv⟩ := h
      exact huz.reachable.trans (ih hzv)
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact ⟨0,rfl⟩
    | cons h p ih =>
      obtain ⟨n,hn⟩ := ih
      exact ⟨n+1,_,h,hn⟩
  · rintro ⟨n,hn⟩
    exact chain_reachable hn

/-- On a countable carrier, measurable sampled adjacency gives measurable
actual reachability. This applies to arbitrary fixed induced domains. -/
theorem measurableSet_sampledGraph_reachable {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    (G : Ω → SimpleGraph V) (hG : ∀ u v, MeasurableSet {ω | (G ω).Adj u v})
    (u v : V) : MeasurableSet {ω | (G ω).Reachable u v} := by
  have hm (n : ℕ) (u : V) : MeasurableSet {ω | sampledGraphChain G n ω u v} := by
    induction n generalizing u with
    | zero => by_cases h : u = v <;> simp [sampledGraphChain,h]
    | succ n ih =>
      have hh := MeasurableSet.iUnion fun z => (hG u z).inter (ih z)
      convert hh using 1
      ext ω
      simp only [sampledGraphChain,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  have hh := MeasurableSet.iUnion fun n => hm n u
  convert hh using 1
  ext ω
  simp only [Set.mem_ofPred_eq,Set.mem_iUnion,sampledGraph_reachable_iff_chain]

end
end PottsContinuity.PlanarTopology
