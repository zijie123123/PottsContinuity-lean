module

public import PottsContinuity.PlanarMixed.RankedBand
public import PottsContinuity.PlanarTopology.SubpathExtraction
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Actual crossing restriction to a ranked band

The private prefix argument adapts `PlanarTopology.walk_prefix_at_level`: it uses only
an edge guard at the terminal level, allowing direct edges between the two
marked cuts. All extracted edges belong to the original open walk.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

private theorem walk_prefix_at_guard {V : Type*} {G : SimpleGraph V}
    (f : V → ℤ) (b : ℤ)
    (hguard : ∀ x y, G.Adj x y → f x < b → b ≤ f y → f y = b)
    {u v : V} (p : G.Walk u v) (hu : f u ≤ b) (hv : b ≤ f v) :
    ∃ z, ∃ (t : G.Walk u z) (s : G.Walk z v),
      f z = b ∧ p = t.append s ∧ ∀ x ∈ t.support, f x ≤ b := by
  induction p with
  | @nil u => exact ⟨u, .nil, .nil, by omega, rfl, by simpa using hu⟩
  | @cons u w v h p ih =>
    by_cases hub : f u = b
    · exact ⟨u, .nil, p.cons h, hub, rfl, by simpa using hu⟩
    · have hw : f w ≤ b := by
        by_cases hbw : b ≤ f w
        · have := hguard u w h (by omega) hbw
          omega
        · omega
      obtain ⟨z, t, s, hz, hp, ht⟩ := ih hw hv
      refine ⟨z, t.cons h, s, hz, ?_, ?_⟩
      · rw [hp]
        rfl
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hu
        · exact ht x hx

/-- A contiguous walk between the two marked cuts remains in the band.
No unit-step assumption between its interior labels is needed. -/
theorem rankedBand_subwalk {V : Type*} {G : SimpleGraph V}
    (r : V → ℤ) (hstep : RankedBandEdges G r)
    {u v : V} (p : G.Walk u v) (hu : r u ≤ 1) (hv : 3 ≤ r v) :
    ∃ x y, ∃ t : G.Walk x y, t.IsSubwalk p ∧ r x = 1 ∧ r y = 3 ∧
      ∀ z ∈ t.support, z ∈ rankedBandVertices r := by
  have h3 : ∀ x y, G.Adj x y → r x < 3 → 3 ≤ r y → r y = 3 := by
    intro x y h hx hy
    rcases hstep x y h with h | h | h <;> omega
  have h1 : ∀ x y, G.Adj x y → -r x < -1 → -1 ≤ -r y → -r y = -1 := by
    intro x y h hx hy
    rcases hstep x y h with h | h | h <;> omega
  obtain ⟨y, t, s, hy, hp, ht⟩ := walk_prefix_at_guard r 3 h3 p (by omega) (by omega)
  obtain ⟨x, k, j, hx, hj, hk⟩ := walk_prefix_at_guard (fun z => -r z) (-1) h1
    t.reverse (by omega) (by omega)
  have ht' : t = j.reverse.append k.reverse := by
    have h := congrArg SimpleGraph.Walk.reverse hj
    simpa only [SimpleGraph.Walk.reverse_reverse, SimpleGraph.Walk.reverse_append] using h
  have hkt : k.reverse.IsSubwalk t := SimpleGraph.Walk.isSubwalk_of_append_right ht'
  refine ⟨x, y, k.reverse, hkt.trans (SimpleGraph.Walk.isSubwalk_of_append_left hp),
    by omega, hy, ?_⟩
  intro z hz
  have hzk : z ∈ k.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
  exact ⟨by have := hk z hzk; omega, ht z (hkt.support_subset hz)⟩

private theorem rankedBand_restriction_adj {V : Type*} [Finite V]
    (G : SimpleGraph V) (r : V → ℤ) (C : Configuration G)
    (u v : rankedBandVertices r) (h : (openGraph G C).Adj u.val v.val) :
    (openGraph (rankedBandGraph G r)
      (embeddedConfigurationRestriction _ _ (rankedBandEmbedding r)
        (rankedBandGraph_map_le G r) C)).Adj u v := by
  let e : (rankedBandGraph G r).edgeSet :=
    ⟨s(u,v), (rankedBandGraph G r).mem_edgeSet.mpr (openGraph_le G C h)⟩
  obtain ⟨a, ha, haq⟩ := (openGraph_adj G C u.val v.val).mp h
  have he : embeddedEdgeEmbedding _ _ (rankedBandEmbedding r)
      (rankedBandGraph_map_le G r) e = a := by
    apply Subtype.ext
    change Sym2.map Subtype.val s(u,v) = a.val
    exact haq.symm
  apply (openGraph_adj _ _ u v).mpr
  refine ⟨e, ?_, rfl⟩
  change e ∈ embeddedConfigurationRestriction _ _ (rankedBandEmbedding r)
    (rankedBandGraph_map_le G r) C
  rw [mem_embeddedConfigurationRestriction, he]
  exact ha

/-- EVERY actual square crossing restricts to an actual marked-cut connection
in the induced band. All edges are original sampled bonds. -/
theorem rankedBand_squareCrossingRestrictsToArcs
    (a : LatticeVertex) (N : ℕ)
    (r : RectangleVertex a N N → ℤ) (hstep : RankedBandEdges (rectangleGraph a N N) r)
    (hleft : ∀ v ∈ Square.squareLeftArc a N, r v ≤ 1)
    (hright : ∀ v ∈ Square.squareRightArc a N, 3 ≤ r v) :
    SquareCrossingRestrictsToArcs a N (rankedBandGraph (rectangleGraph a N N) r)
      (rankedBandEmbedding r) (rankedBandGraph_map_le _ r)
      (rankedBandFirstArc r) (rankedBandSecondArc r) := by
  intro C hC
  obtain ⟨u, hu, v, hv, hp⟩ := hC
  obtain ⟨p⟩ := (actualConnected_iff_walk _ _ u v).mp hp
  have hopen : RankedBandEdges (openGraph (rectangleGraph a N N) C) r :=
    fun x y h => hstep x y (openGraph_le _ C h)
  obtain ⟨x, y, t, _, hx, hy, ht⟩ := rankedBand_subwalk r hopen p (hleft u hu) (hright v hv)
  let tx : rankedBandVertices r := ⟨x, ht x t.start_mem_support⟩
  let ty : rankedBandVertices r := ⟨y, ht y t.end_mem_support⟩
  let f : ((openGraph (rectangleGraph a N N) C).induce (rankedBandVertices r)) →g
      openGraph (rankedBandGraph (rectangleGraph a N N) r)
        (embeddedConfigurationRestriction _ _ (rankedBandEmbedding r)
          (rankedBandGraph_map_le _ r) C) :=
    { toFun := id
      map_rel' := fun {u v} h => rankedBand_restriction_adj _ r C u v h }
  exact ⟨tx, hx, ty, hy, (t.induce (rankedBandVertices r) ht |>.map f).reachable⟩

end
end PottsContinuity.PlanarMixed
