module

public import PottsContinuity.Thm3.Prop4.CensoredClusterReveal
public import PottsContinuity.Thm3.Prop4.ClusterFreeLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Actual paths censored at a prescribed wired arc

The censored graph isolates the arc vertices. Away from those vertices its
open paths are exactly ambient open paths avoiding the arc. This gives a
literal exploration of the clusters which could escape without hitting it.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G H : SimpleGraph V}
local instance arcVertexDecidableEq : DecidableEq V := Classical.decEq _
local instance arcEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Restriction to a fixed subgraph preserves precisely the open edges it contains. -/
theorem censored_openGraph_adj_iff (hHG : H ≤ G) (A : Configuration G) (u v : V) :
    (openGraph H (censoredConfiguration hHG A)).Adj u v ↔
      (openGraph G A).Adj u v ∧ H.Adj u v := by
  constructor
  · intro h
    obtain ⟨e,he,heq⟩ := (openGraph_adj H _ u v).mp h
    exact ⟨(openGraph_adj G A u v).mpr
      ⟨censoredEdgeInclusion hHG e,(mem_censoredConfiguration hHG A e).mp he,heq⟩,
      openGraph_le H _ h⟩
  · rintro ⟨hG,hH⟩
    obtain ⟨e,he,heq⟩ := (openGraph_adj G A u v).mp hG
    let f : H.edgeSet := ⟨s(u,v),H.mem_edgeSet.mpr hH⟩
    have hef : censoredEdgeInclusion hHG f = e := Subtype.ext heq.symm
    apply (openGraph_adj H _ u v).mpr
    refine ⟨f,(mem_censoredConfiguration hHG A f).mpr ?_,rfl⟩
    rw [hef]
    exact he

/-- Isolate a prescribed arc, retaining every original edge between other vertices. -/
def arcCensoredGraph (G : SimpleGraph V) (W : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ W ∧ v ∉ W
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

omit [Finite V] in
theorem arcCensoredGraph_le (G : SimpleGraph V) (W : Set V) : arcCensoredGraph G W ≤ G :=
  fun _ _ h => h.1

/-- Along the censored open graph, a seed outside the arc stays outside it. -/
theorem arcCensored_connected_not_mem (G : SimpleGraph V) (W : Set V)
    (A : Configuration G) {u v : V} (hu : u ∉ W)
    (h : ActualConnected (arcCensoredGraph G W)
      (censoredConfiguration (arcCensoredGraph_le G W) A) u v) : v ∉ W := by
  change (openGraph (arcCensoredGraph G W)
    (censoredConfiguration (arcCensoredGraph_le G W) A)).Reachable u v at h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ hedge _ => exact (openGraph_le _ _ hedge).2.2

/-- Every censored path from a seed outside the arc is an ambient path avoiding the arc. -/
theorem arcCensored_connected_has_avoiding_walk (G : SimpleGraph V) (W : Set V)
    (A : Configuration G) {u v : V} (hu : u ∉ W)
    (h : ActualConnected (arcCensoredGraph G W)
      (censoredConfiguration (arcCensoredGraph_le G W) A) u v) :
    ∃ p : (openGraph G A).Walk u v, ∀ z ∈ p.support, z ∉ W := by
  obtain ⟨p⟩ := h
  have hle : openGraph (arcCensoredGraph G W)
      (censoredConfiguration (arcCensoredGraph_le G W) A) ≤ openGraph G A := by
    intro a b hab
    exact ((censored_openGraph_adj_iff (arcCensoredGraph_le G W) A a b).mp hab).1
  refine ⟨p.mapLe hle,?_⟩
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  intro z hz
  exact arcCensored_connected_not_mem G W A hu (p.takeUntil z hz).reachable

/-- No-escape gives exclusion from the actual censored outside-seed cluster. -/
theorem no_escape_excludes_censoredSeedCluster (G : SimpleGraph V) (W D : Set V)
    (A : Configuration G) (x : V) (hWD : W ⊆ D)
    (hno : ∀ y : V, y ∉ D → ∀ p : (openGraph G A).Walk x y,
      ∃ z ∈ p.support, z ∈ W) :
    x ∉ censoredSeedCluster (arcCensoredGraph_le G W) Dᶜ A := by
  rintro ⟨y,hy,hyx⟩
  have hyW : y ∉ W := fun hyW => hy (hWD hyW)
  obtain ⟨p,hp⟩ := arcCensored_connected_has_avoiding_walk G W A hyW hyx
  obtain ⟨z,hz,hzW⟩ := hno y hy p.reverse
  exact hp z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz) hzW

end
end PottsContinuity.Thm3.Prop4
