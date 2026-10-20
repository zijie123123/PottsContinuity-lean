-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/TrifurcationSurgery.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.MappedTree
public import PottsContinuity.PD.RCInfinite.SurgeryExterior
public import PottsContinuity.PD.RCInfinite.UnionReachability
public import PottsContinuity.PD.RCInfinite.ExteriorBranches
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

theorem boxExitTripleCell_surgery_trifurcation {n : ℕ}
    (ω : LatticeConfiguration) (xs : Fin 3 → LatticeVertex)
    (exits : Fin 3 → BoxExit n) (hcell : ω ∈ boxExitTripleCell n xs exits)
    (U : Finset (BoxExitCarrier n)) (hTU : boxExitConnectorTerminals n ⊆ U)
    (H : SimpleGraph (U : Set (BoxExitCarrier n)))
    (hHG : H ≤ (boxExitConnectorGraph n exits).induce (U : Set (BoxExitCarrier n)))
    (v : U)
    (hsep : SeparatesThreeTerminals H
      (Finset.univ.image (boxExitPortalIn n U hTU)) v) :
    isTrifurcationAt
      (setEdges (boxIncidentEdges n)
        (boxTreeEdgeState H (boxExitSubembedding exits
          (boxExitTripleCell_outside_injective ω xs exits hcell) U)) ω)
      (boxExitSubembedding exits (boxExitTripleCell_outside_injective ω xs exits hcell) U v) := by
  classical
  let hdist := boxExitTripleCell_outside_injective ω xs exits hcell
  let f := boxExitSubembedding exits hdist U
  let port := boxExitPortalIn n U hTU
  let T' : Finset U := Finset.univ.image port
  let G := H.map f
  let η := setEdges (boxIncidentEdges n) (boxTreeEdgeState H f) ω
  let R := rcInfiniteOpenGraph η
  let E := exteriorOpenGraph ω n
  let vlat := f v
  have hsep' : SeparatesThreeTerminals H (T' : Set U) v := by
    simpa only [T', port] using hsep
  obtain ⟨ys, hys, hsepPair⟩ := hsep'
  have hportInj : Function.Injective port := by
    intro j k h
    exact Sum.inr.inj (congrArg Subtype.val h)
  have hysInj : Function.Injective ys := by
    intro j k heq
    by_contra hjk
    have hreach : (H.deleteIncidenceSet v).Reachable (ys j) (ys k) := by
      rw [heq]
    exact hsepPair j k hjk hreach
  have hTcard : T'.card = 3 := by
    rw [Finset.card_image_of_injective _ hportInj]
    simp
  have hYcard : (Finset.univ.image ys).card = 3 := by
    rw [Finset.card_image_of_injective _ hysInj]
    simp
  have hYsub : Finset.univ.image ys ⊆ T' := by
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact (hys j).2.1
  have hYeq : Finset.univ.image ys = T' :=
    Finset.eq_of_subset_of_card_le hYsub (by rw [hTcard, hYcard])
  have hcoverPortal (j : Fin 3) : ∃ k, ys k = port j := by
    have hjT : port j ∈ T' := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    have hjY : port j ∈ Finset.univ.image ys := by rw [hYeq]; exact hjT
    obtain ⟨k, _, hEq⟩ := Finset.mem_image.mp hjY
    exact ⟨k, hEq⟩
  have hvNotPortal (j : Fin 3) : v ≠ port j := by
    intro hv
    obtain ⟨k, hk⟩ := hcoverPortal j
    exact (hys k).2.2 (hk.trans hv.symm)
  have hvBox : vlat ∈ latticeBox (0, 0) n := by
    cases hval : v.val with
    | inl a =>
      have hfv : vlat = a.val := by
        change boxExitCarrierVertex exits v.val = a.val
        rw [hval]
        rfl
      exact hfv.symm ▸ a.property
    | inr j =>
      apply False.elim
      apply hvNotPortal j
      apply Subtype.ext
      simpa only [port, boxExitPortalIn] using hval
  have hjspec (k : Fin 3) : ∃! j, port j = ys k := by
    obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp (hys k).2.1
    refine ⟨j, hEq, ?_⟩
    intro l hl
    exact hportInj (hl.trans hEq.symm)
  choose js hjs using hjspec
  have hportalVal (k : Fin 3) : f (ys k) = boxExitOutside (exits (js k)) := by
    change boxExitCarrierVertex exits (ys k).val = boxExitOutside (exits (js k))
    rw [congrArg Subtype.val (hjs k).1.symm]
    simp [port, boxExitPortalIn, boxExitOutside, boxExitCarrierVertex]
  have hEvent (j : Fin 3) : ω ∈ boxExitWitnessEvent (xs j) (exits j) :=
    (Set.mem_iInter.mp hcell.2) j
  have hGsupport : ∀ ⦃x y⦄, (G.deleteIncidenceSet vlat).Adj x y →
      x ∈ Set.range f ∧ y ∈ Set.range f := by
    intro x y hxy
    have hGxy : G.Adj x y := SimpleGraph.deleteIncidenceSet_le G vlat hxy
    obtain ⟨a, b, _, hax, hby⟩ := (SimpleGraph.map_adj f H x y).mp hGxy
    exact ⟨⟨a, hax⟩, ⟨b, hby⟩⟩
  have hEunique : ∀ ⦃x y⦄, x ∈ Set.range f → y ∈ Set.range f →
      E.Reachable x y → x = y := by
    intro x y hx hy hxy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    by_cases hab : f a = f b
    · exact hab
    · have hout := exteriorReachable_distinct_endpoints_outside ω hxy hab
      rcases a with ⟨av, hav⟩
      rcases b with ⟨bv, hbv⟩
      cases av with
      | inl x =>
        have hxbox : f ⟨Sum.inl x, hav⟩ ∈ latticeBox (0, 0) n := by
          have hfx : f ⟨Sum.inl x, hav⟩ = x.val := rfl
          exact hfx.symm ▸ x.property
        exact (hout.1 hxbox).elim
      | inr j =>
        cases bv with
        | inl y =>
          have hybox : f ⟨Sum.inl y, hbv⟩ ∈ latticeBox (0, 0) n := by
            have hfy : f ⟨Sum.inl y, hbv⟩ = y.val := rfl
            exact hfy.symm ▸ y.property
          exact (hout.2 hybox).elim
        | inr k =>
          have hjk : j ≠ k := by
            intro hEq
            subst k
            exact hab rfl
          have hExt : (rcInfiniteOpenGraph ω).Reachable
              (boxExitOutside (exits j)) (boxExitOutside (exits k)) :=
            hxy.mono (exteriorOpenGraph_le ω n)
          have hconnection : (rcInfiniteOpenGraph ω).Reachable (xs j) (xs k) :=
            (hEvent j).2.1.trans (hExt.trans (hEvent k).2.1.symm)
          exact False.elim ((hcell.1.2 j k hjk) hconnection)
  have hGTreeLe : G ≤ R :=
    mapped_connector_tree_le_surgery_graph exits hdist U H hHG ω
  have hEtoRdel : E ≤ R.deleteIncidenceSet vlat := by
    have hEdel : E ≤ E.deleteIncidenceSet vlat := by
      intro x y hxy
      obtain ⟨_, hxout, hyout⟩ := (exteriorOpenGraph_adj ω n x y).mp hxy
      apply SimpleGraph.deleteIncidenceSet_adj.mpr
      refine ⟨hxy, ?_, ?_⟩
      · intro hEq
        apply hxout
        rw [hEq]
        exact hvBox
      · intro hEq
        apply hyout
        rw [hEq]
        exact hvBox
    exact hEdel.trans (exteriorOpenGraph_deleted_le_tree_surgery_deleted
      exits hdist U H ω vlat)
  have hGdelLe : G.deleteIncidenceSet vlat ≤ R.deleteIncidenceSet vlat := by
    intro x y hxy
    obtain ⟨hGxy, hxv, hyv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hxy
    exact SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hGTreeLe hGxy, hxv, hyv⟩
  have hdelSupLe : (G ⊔ E).deleteIncidenceSet vlat ≤
      G.deleteIncidenceSet vlat ⊔ E := by
    intro x y hxy
    obtain ⟨hsup, hxv, hyv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hxy
    rcases (SimpleGraph.sup_adj G E x y).mp hsup with hGxy | hExy
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl
        (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hGxy, hxv, hyv⟩))
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr hExy)
  have hModLeSup : R ≤ G ⊔ E :=
    surgery_graph_le_tree_sup_exterior exits hdist U H ω
  have hModDelLe : R.deleteIncidenceSet vlat ≤ G.deleteIncidenceSet vlat ⊔ E := by
    intro x y hxy
    obtain ⟨hRxy, hxv, hyv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hxy
    have hxy' : (G ⊔ E).deleteIncidenceSet vlat |>.Adj x y :=
      SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hModLeSup hRxy, hxv, hyv⟩
    exact hdelSupLe hxy'
  have hfirst (k : Fin 3) : ∃ u : U,
      H.Adj v u ∧ (H.deleteIncidenceSet v).Reachable u (ys k) := by
    obtain ⟨p, hp⟩ := (hys k).1.exists_isPath
    obtain ⟨u, hvu, q, rfl⟩ := p.exists_eq_cons_of_ne (hys k).2.2.symm
    have havoid : v ∉ q.support := (SimpleGraph.Walk.cons_isPath_iff hvu q).mp hp |>.2
    exact ⟨u, hvu, walk_reachable_deleteIncidenceSet q havoid⟩
  choose us hus hrem using hfirst
  have hAdj (k : Fin 3) : R.Adj vlat (f (us k)) := by
    have hmap : G.Adj (f v) (f (us k)) :=
      (SimpleGraph.map_adj_apply).2 (hus k)
    exact hGTreeLe hmap
  have hGdelReach (k : Fin 3) :
      (G.deleteIncidenceSet vlat).Reachable (f (us k)) (f (ys k)) :=
    (mapped_tree_delete_reachable_iff H f v (us k) (ys k)).2 (hrem k)
  have hGdelReachR (k : Fin 3) :
      (R.deleteIncidenceSet vlat).Reachable (f (us k)) (f (ys k)) :=
    (hGdelReach k).mono hGdelLe
  have hInfinite (k : Fin 3) :
      deletedInfiniteAt η vlat (f (us k)) := by
    obtain ⟨z, hyz, hInf⟩ := exteriorInfiniteAt_has_deleted_neighbor ω n
      (boxExitOutside (exits (js k))) (hEvent (js k)).2.2
    have hyzR : R.deleteIncidenceSet vlat |>.Adj
        (boxExitOutside (exits (js k))) z := by
      exact hEtoRdel hyz
    have hPortalEq : f (ys k) = boxExitOutside (exits (js k)) := hportalVal k
    have hbranch : (R.deleteIncidenceSet vlat).Reachable (f (us k))
        (boxExitOutside (exits (js k))) := by
      simpa only [hPortalEq] using hGdelReachR k
    change {w | (R.deleteIncidenceSet vlat).Reachable (f (us k)) w}.Infinite
    apply hInf.mono
    intro w hw
    have hzw : (E.deleteIncidenceSet (boxExitOutside (exits (js k)))).Reachable z w := hw
    have hzwE : E.Reachable z w :=
      hzw.mono (SimpleGraph.deleteIncidenceSet_le E (boxExitOutside (exits (js k))))
    have hzwR := hzwE.mono hEtoRdel
    exact hbranch.trans (hyzR.reachable.trans hzwR)
  have hsepBranches (j k : Fin 3) (hjk : j ≠ k) :
      ¬(R.deleteIncidenceSet vlat).Reachable (f (us j)) (f (us k)) := by
    intro hreach
    have hUnion := hreach.mono hModDelLe
    have hGreach := reachable_of_sup_of_external_components
      (G.deleteIncidenceSet vlat) E (Set.range f) hGsupport hEunique
      ⟨us j, rfl⟩ ⟨us k, rfl⟩ hUnion
    have htreeReach : (H.deleteIncidenceSet v).Reachable (us j) (us k) :=
      (mapped_tree_delete_reachable_iff H f v (us j) (us k)).1 hGreach
    exact hsepPair j k hjk ((hrem j).symm.trans (htreeReach.trans (hrem k)))
  refine ⟨fun k => f (us k), ?_, ?_⟩
  · intro k
    exact ⟨hAdj k, hInfinite k⟩
  · exact hsepBranches

end
end PottsContinuity.PD.RCInfinite
