module

public import PottsContinuity.PlanarMixed.OrderedCutRegions
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-! Cut-avoiding reachability under collapse of connected vertex fibres.
Every cut is read by preimage, so no marked vertex is silently discarded. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed
noncomputable section

/-- Append an actual cut-avoiding walk to an already reached vertex. -/
theorem cutReachRegion_follow_walk {V : Type*} {G : SimpleGraph V}
    {cut seeds : Set V} {u v : V} (hu : u ∈ cutReachRegion G cut seeds)
    (p : G.Walk u v) (hp : ∀ w ∈ p.support, w ∉ cut) :
    v ∈ cutReachRegion G cut seeds := by
  obtain ⟨a,ha,q,hq⟩ := hu
  refine ⟨a,ha,q.append p,?_⟩
  intro w hw
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hw | hw
  · exact hq w hw
  · exact hp w hw

/-- Connected fibres are either entirely reached or entirely unreached when
the removed vertex set is the preimage of a cut in the collapsed carrier. -/
theorem cutReachRegion_fibre_saturated {V W : Type*} (G : SimpleGraph V) (π : V → W)
    (hf : ∀ u v, π u = π v → ∃ p : G.Walk u v, ∀ w ∈ p.support, π w = π u)
    (cut : Set W) (seeds : Set V) {u v : V} (huv : π u = π v)
    (hu : u ∈ cutReachRegion G (π ⁻¹' cut) seeds) :
    v ∈ cutReachRegion G (π ⁻¹' cut) seeds := by
  obtain ⟨p,hp⟩ := hf u v huv
  apply cutReachRegion_follow_walk hu p
  intro w hw
  change π w ∉ cut
  rw [hp w hw]
  exact cutReachRegion_avoids_cut (S := π ⁻¹' cut) hu

/-- Projection may collapse an edge to a vertex; actual cut-avoiding
reachability still projects without adding any marked vertex. -/
theorem cutReachRegion_map {V W : Type*} (G : SimpleGraph V) (π : V → W)
    (cut : Set W) (seeds : Set V) {v : V}
    (hv : v ∈ cutReachRegion G (π ⁻¹' cut) seeds) :
    π v ∈ cutReachRegion (G.map π) cut (π '' seeds) := by
  obtain ⟨a,ha,p,hp⟩ := hv
  have transfer {u v : V} (p : G.Walk u v) :
      (∀ w ∈ p.support, π w ∉ cut) →
      π u ∈ cutReachRegion (G.map π) cut (π '' seeds) →
      π v ∈ cutReachRegion (G.map π) cut (π '' seeds) := by
    induction p with
    | nil => intro _ hu; exact hu
    | @cons u z v huz p ih =>
      intro hp hu
      apply ih (fun w hw => hp w (by simp [hw]))
      by_cases heq : π u = π z
      · exact heq ▸ hu
      · exact cutReachRegion_edge_closed hu
          ((SimpleGraph.map_adj' π G _ _).mpr ⟨heq,u,z,huz,rfl,rfl⟩)
          (hp z (by simp))
  exact transfer p hp (cutReachRegion_contains (G.map π) ⟨a,ha,rfl⟩ (hp a p.start_mem_support))

/-- Collapse of connected fibres preserves the entire cut-reach region.
The mapped graph is the genuine image graph, including its exact carrier. -/
theorem cutReachRegion_map_iff_of_connected_fibres {V W : Type*}
    (G : SimpleGraph V) (π : V → W)
    (hf : ∀ u v, π u = π v → ∃ p : G.Walk u v, ∀ w ∈ p.support, π w = π u)
    (cut : Set W) (seeds : Set V) (v : V) :
    π v ∈ cutReachRegion (G.map π) cut (π '' seeds) ↔
      v ∈ cutReachRegion G (π ⁻¹' cut) seeds := by
  refine ⟨?_,cutReachRegion_map G π cut seeds⟩
  rintro ⟨a,⟨l,hl,hπl⟩,p,hp⟩
  have transfer {a b : W} (p : (G.map π).Walk a b) :
      (∀ w ∈ p.support, w ∉ cut) →
      (∀ u, π u = a → u ∈ cutReachRegion G (π ⁻¹' cut) seeds) →
      ∀ u, π u = b → u ∈ cutReachRegion G (π ⁻¹' cut) seeds := by
    induction p with
    | nil => intro _ hu; exact hu
    | @cons a b c hab p ih =>
      intro hp hu
      apply ih (fun w hw => hp w (by simp [hw]))
      intro z hz
      obtain ⟨_,u,v,huv,hπu,hπv⟩ := (SimpleGraph.map_adj' π G a b).mp hab
      have hv := cutReachRegion_edge_closed (hu u hπu) huv (by
        change π v ∉ cut
        rw [hπv]
        exact hp b (by simp))
      exact cutReachRegion_fibre_saturated G π hf cut seeds (hπv.trans hz.symm) hv
  apply transfer p hp ?_ v rfl
  intro u hu
  apply cutReachRegion_fibre_saturated G π hf cut seeds (hπl.trans hu.symm)
  apply cutReachRegion_contains G hl
  change π l ∉ cut
  rw [hπl]
  exact hp a p.start_mem_support

end
end PottsContinuity.PlanarMixed
