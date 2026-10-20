module

public import PottsContinuity.Thm3.Push.SideCollarConnection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- A fixed collar bond can touch the source only at its physical left side. -/
theorem sideCollar_fixed_incidence_is_left (w h : ℕ)
    (u : RectangleVertex (0,0) w h)
    (e : (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).edgeSet)
    (he : e ∈ sideCollarOpenEdges w h) (hu : sideCollarEmbedding w h u ∈ e.val) :
    u.val.1 = 0 := by
  classical
  obtain ⟨a,b,ha,hb,heq⟩ := (Finset.mem_filter.mp he).2
  rw [heq] at hu
  have hbox := (mem_latticeRectangle (0,0) u.val w h).mp u.property
  rcases Sym2.mem_iff'.mp hu with hua | hub
  · have hx := congrArg (fun z => z.val.1) hua
    change u.val.1+2 = a.val.1 at hx
    dsimp at hbox
    omega
  · have hx := congrArg (fun z => z.val.1) hub
    change u.val.1+2 = b.val.1 at hx
    rcases hb with hb | hb
    · dsimp at hbox
      omega
    · have hb2 := hb.1
      omega

/-- Away from the left side, every auxiliary open neighbor of an embedded
source vertex is another embedded vertex joined by an original open bond. -/
theorem sideCollar_neighbor_lifts_off_left (w h : ℕ)
    (C : Configuration (rectangleGraph (0,0) w h))
    (u : RectangleVertex (0,0) w h) (hu : u.val.1 ≠ 0)
    (v : RectangleVertex (0,0) (sideCollarSize w h) (sideCollarSize w h))
    (huv : (openGraph (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h))
      (sideCollarExtension w h C)).Adj (sideCollarEmbedding w h u) v) :
    ∃ b : RectangleVertex (0,0) w h, sideCollarEmbedding w h b = v ∧
      (openGraph (rectangleGraph (0,0) w h) C).Adj u b := by
  classical
  obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ _ _).mp huv
  change e ∈ _ ∪ sideCollarOpenEdges w h at he
  rcases Finset.mem_union.mp he with he | he
  · have hmap : (openGraph (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h))
        (embeddedConfigurationEmbedding _ _ (sideCollarEmbedding w h)
          (sideCollarEmbedding_map_le w h) C)).Adj (sideCollarEmbedding w h u) v := by
      rw [openGraph_adj]
      exact ⟨e,he,heq⟩
    change (openGraph _ (subgraphConfigurationEmbedding (sideCollarEmbedding_map_le w h)
      (isolatedExtensionConfigurationEquiv _ (sideCollarEmbedding w h) C))).Adj _ _ at hmap
    rw [openGraph_subgraphConfigurationEmbedding,openGraph_isolatedExtension,
      SimpleGraph.map_adj] at hmap
    obtain ⟨a,b,hab,ha,hb⟩ := hmap
    have hau : a=u := (sideCollarEmbedding w h).injective ha
    subst a
    exact ⟨b,hb,hab⟩
  · exact (hu (sideCollar_fixed_incidence_is_left w h u e he (by rw [heq]; exact Sym2.mem_mk_left _ _))).elim

/-- Any auxiliary connection leaving the original carrier must first connect
to an actual original left-side vertex by original sampled bonds. -/
theorem sideCollar_outside_connection_implies_left (w h : ℕ)
    (C : Configuration (rectangleGraph (0,0) w h)) (a : RectangleVertex (0,0) w h)
    (z : RectangleVertex (0,0) (sideCollarSize w h) (sideCollarSize w h))
    (hz : z ∉ Set.range (sideCollarEmbedding w h))
    (haz : ActualConnected _ (sideCollarExtension w h C) (sideCollarEmbedding w h a) z) :
    ∃ b : RectangleVertex (0,0) w h, b.val.1 = 0 ∧
      ActualConnected (rectangleGraph (0,0) w h) C a b := by
  classical
  by_contra hno
  have hlift : ∀ {u v}, (p : (openGraph (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h))
      (sideCollarExtension w h C)).Walk u v) →
      ∀ b : RectangleVertex (0,0) w h, sideCollarEmbedding w h b = u →
      ActualConnected (rectangleGraph (0,0) w h) C a b →
      ∃ c : RectangleVertex (0,0) w h, sideCollarEmbedding w h c = v ∧
        ActualConnected (rectangleGraph (0,0) w h) C a c := by
    intro u v p
    induction p with
    | nil =>
        intro b hb hab
        exact ⟨b,hb,hab⟩
    | @cons u v t huv p ih =>
        intro b hb hab
        have hb0 : b.val.1 ≠ 0 := fun h => hno ⟨b,h,hab⟩
        rw [← hb] at huv
        obtain ⟨c,hc,hbc⟩ := sideCollar_neighbor_lifts_off_left w h C b hb0 v huv
        exact ih c hc (hab.trans hbc.reachable)
  obtain ⟨p⟩ := haz
  obtain ⟨b,hb,_⟩ := hlift p a rfl (SimpleGraph.Reachable.refl a)
  exact hz ⟨b,hb⟩

/-- The auxiliary top row lies strictly above every embedded source vertex. -/
theorem sideCollar_top_not_source (w h : ℕ)
    (z : RectangleVertex (0,0) (sideCollarSize w h) (sideCollarSize w h))
    (hz : z.val.2 = (sideCollarSize w h:ℕ)) :
    z ∉ Set.range (sideCollarEmbedding w h) := by
  rintro ⟨a,ha⟩
  have hy := congrArg (fun v => v.val.2) ha
  change a.val.2 = z.val.2 at hy
  have hbox := (mem_latticeRectangle (0,0) a.val w h).mp a.property
  dsimp [sideCollarSize] at hz
  dsimp at hbox
  omega

end
end PottsContinuity.Push
