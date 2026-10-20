module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section

/-- Finitely many marked vertices have a finite hull containing witnesses for
all connections that exist between them in the original graph. -/
theorem exists_finite_connection_hull {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    ∃ T : Finset V, S ⊆ T ∧ ∀ u ∈ S, ∀ v ∈ S, G.Reachable u v →
      ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ T := by
  classical
  have pair (u v : V) : ∃ T : Finset V, G.Reachable u v →
      ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ T := by
    by_cases h : G.Reachable u v
    · obtain ⟨p⟩ := h
      exact ⟨p.support.toFinset,fun _ => ⟨p,fun z hz => List.mem_toFinset.mpr hz⟩⟩
    · exact ⟨∅,fun h' => (h h').elim⟩
  choose F hF using pair
  let T := S ∪ S.biUnion (fun u => S.biUnion (fun v => F u v))
  refine ⟨T,fun z hz => Finset.mem_union_left _ hz,?_⟩
  intro u hu v hv huv
  obtain ⟨p,hp⟩ := hF u v huv
  refine ⟨p,?_⟩
  intro z hz
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨u,hu,Finset.mem_biUnion.mpr ⟨v,hv,hp z hz⟩⟩

/-- Global uniqueness of the infinite component gives uniform finite local
uniqueness near any fixed finite set. Roots reaching beyond the finite witness
set are connected inside it, simultaneously for every pair of marked roots. -/
theorem exists_finite_local_uniqueness {V : Type*} (G : SimpleGraph V) (S : Finset V)
    (hunique : ∀ u v, {z | G.Reachable u z}.Infinite →
      {z | G.Reachable v z}.Infinite → G.Reachable u v) :
    ∃ T : Finset V, S ⊆ T ∧ ∀ u ∈ S, ∀ v ∈ S,
      (∃ x, x ∉ T ∧ G.Reachable u x) → (∃ y, y ∉ T ∧ G.Reachable v y) →
        ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ T := by
  classical
  obtain ⟨H,hSH,hH⟩ := exists_finite_connection_hull G S
  have bounded (u : V) : ∃ K : Finset V, ¬{z | G.Reachable u z}.Infinite →
      ∀ z, G.Reachable u z → z ∈ K := by
    by_cases hi : {z | G.Reachable u z}.Infinite
    · exact ⟨∅,fun hn => (hn hi).elim⟩
    · have hf : {z | G.Reachable u z}.Finite := Set.not_infinite.mp hi
      exact ⟨hf.toFinset,fun _ z hz => hf.mem_toFinset.mpr hz⟩
  choose K hK using bounded
  let T := H ∪ S.biUnion K
  have hHT : H ⊆ T := fun z hz => Finset.mem_union_left _ hz
  refine ⟨T,Finset.Subset.trans hSH hHT,?_⟩
  intro u hu v hv hex hey
  have infinite (w : V) (hw : w ∈ S) (he : ∃ z, z ∉ T ∧ G.Reachable w z) :
      {z | G.Reachable w z}.Infinite := by
    by_contra hn
    obtain ⟨z,hz,hreach⟩ := he
    exact hz (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w,hw,hK w hn z hreach⟩))
  obtain ⟨p,hp⟩ := hH u hu v hv (hunique u v (infinite u hu hex) (infinite v hv hey))
  exact ⟨p,fun z hz => hHT (hp z hz)⟩

end
end PottsContinuity.PlanarTopology
