-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygonCellExteriorConnectivity.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticePolygonCellConnectivity
public import PottsContinuity.FKC.Domains.LatticeBoxExteriorConnected
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Domains

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open PottsContinuity.FKC.LatticePolygon
open SimpleGraph

def cellComplementGraph (S : Finset LatticeVertex) :
    SimpleGraph {v : LatticeVertex // v ∉ S} :=
  squareLattice.induce {v | v ∉ S}

private theorem finite_vertex_set_subset_box (S : Finset LatticeVertex) :
    ∃ r : ℕ, S ⊆ latticeBox (0, 0) r := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
      obtain ⟨r, hr⟩ := ih
      let R := max r (max a.1.natAbs a.2.natAbs)
      refine ⟨R, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with hza | hz
      · subst z
        rw [mem_latticeBox]
        constructor
        · have hxn : a.1.natAbs ≤ R := by
            exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
          have hxc : (a.1.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast hxn
          have hRnonneg : (0 : ℤ) ≤ (R : ℤ) := Int.natCast_nonneg _
          constructor
          · by_cases hpos : 0 ≤ a.1
            · omega
            · rw [← Int.natAbs_neg,
                Int.natAbs_of_nonneg (show 0 ≤ -a.1 by omega)] at hxc
              omega
          · by_cases hpos : 0 ≤ a.1
            · rw [Int.natAbs_of_nonneg hpos] at hxc
              omega
            · omega
        · have hyn : a.2.natAbs ≤ R := by
            exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
          have hyc : (a.2.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast hyn
          have hRnonneg : (0 : ℤ) ≤ (R : ℤ) := Int.natCast_nonneg _
          constructor
          · by_cases hpos : 0 ≤ a.2
            · omega
            · rw [← Int.natAbs_neg,
                Int.natAbs_of_nonneg (show 0 ≤ -a.2 by omega)] at hyc
              omega
          · by_cases hpos : 0 ≤ a.2
            · rw [Int.natAbs_of_nonneg hpos] at hyc
              omega
            · omega
      · exact latticeBox_mono (0,0) (Nat.le_max_left _ _) (hr hz)

noncomputable def boundedCellComplementComponent (S B : Finset LatticeVertex)
    (c : LatticeVertex) (hc : c ∉ S) : Finset LatticeVertex := by
  classical
  exact B.filter fun z =>
    ∃ hz : z ∉ S, (cellComplementGraph S).Reachable ⟨c,hc⟩ ⟨z,hz⟩

private theorem latticeBond_faceBase_adjacent_local (e : LatticeBond) :
    squareLattice.Adj (e.faceBase true) (e.faceBase false) := by
  rcases e with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp [LatticeBond.faceBase, squareLattice]

private theorem boundedComponent_boundary_subset
    (S B : Finset LatticeVertex) (c : LatticeVertex) (hc : c ∉ S)
    (hbounded : ∀ z (hz : z ∉ S),
      (cellComplementGraph S).Reachable ⟨c,hc⟩ ⟨z,hz⟩ → z ∈ B) :
    latticeCellBoundaryBonds (boundedCellComplementComponent S B c hc) ⊆
      latticeCellBoundaryBonds S := by
  classical
  let T := boundedCellComplementComponent S B c hc
  intro e he
  rw [mem_latticeCellBoundaryBonds] at he ⊢
  change (e.faceBase true ∈ T) ≠ (e.faceBase false ∈ T) at he
  have hpropagate : ∀ a b : LatticeVertex, a ∉ S → b ∉ S →
      squareLattice.Adj a b → a ∈ T → b ∈ T := by
    intro a b ha hb hadj haT
    obtain ⟨haB, ⟨ha', hreach⟩⟩ := Finset.mem_filter.mp haT
    have hstep : (cellComplementGraph S).Reachable ⟨a,ha'⟩ ⟨b,hb⟩ := by
      refine ⟨Walk.cons ?_ Walk.nil⟩
      change squareLattice.Adj a b
      exact hadj
    have hreachB := hreach.trans hstep
    have hbB := hbounded b hb (hreachB)
    exact Finset.mem_filter.mpr ⟨hbB, ⟨hb,hreachB⟩⟩
  by_cases htT : e.faceBase true ∈ T
  · have htS : e.faceBase true ∉ S := by
      intro h
      obtain ⟨_, ⟨hnotS,_⟩⟩ := Finset.mem_filter.mp htT
      exact hnotS h
    by_cases hfS : e.faceBase false ∈ S
    · exact (by simp [htS, hfS])
    · have hfnot : e.faceBase false ∉ T := by
        intro h
        exact he (propext ⟨fun _ => h, fun _ => htT⟩)
      have hprop := hpropagate _ _ htS hfS
        (latticeBond_faceBase_adjacent_local e) htT
      exact False.elim (hfnot hprop)
  · have hfT : e.faceBase false ∈ T := by
      by_contra hnot
      exact he (propext ⟨fun h => False.elim (htT h),
        fun h => False.elim (hnot h)⟩)
    have hfS : e.faceBase false ∉ S := by
      intro h
      obtain ⟨_, ⟨hnotS,_⟩⟩ := Finset.mem_filter.mp hfT
      exact hnotS h
    by_cases htS : e.faceBase true ∈ S
    · exact (by simp [htS, hfS])
    · have htrueT : e.faceBase true ∈ T := by
        have hadj := (latticeBond_faceBase_adjacent_local e).symm
        have hprop := hpropagate _ _ hfS htS hadj hfT
        exact hprop
      exact False.elim (htT htrueT)

private theorem complement_component_not_bounded
    {v : LatticeVertex} {p : squareLattice.Walk v v} (hp : p.IsCycle)
    (S B : Finset LatticeVertex)
    (hcycle : latticeCellBoundaryGraph S = p.toSubgraph.spanningCoe)
    (c : LatticeVertex) (hc : c ∉ S)
    (hbounded : ∀ z (hz : z ∉ S),
      (cellComplementGraph S).Reachable ⟨c,hc⟩ ⟨z,hz⟩ → z ∈ B) : False := by
  classical
  let T := boundedCellComplementComponent S B c hc
  have hcreach : (cellComplementGraph S).Reachable ⟨c,hc⟩ ⟨c,hc⟩ := Walk.nil.reachable
  have hcB : c ∈ B := hbounded c hc hcreach
  have hTnonempty : T.Nonempty := by
    refine ⟨c, ?_⟩
    exact Finset.mem_filter.mpr ⟨hcB, ⟨hc,hcreach⟩⟩
  have hTBonds : latticeCellBoundaryBonds T ⊆ latticeCellBoundaryBonds S :=
    boundedComponent_boundary_subset S B c hc hbounded
  have hTle : latticeCellBoundaryGraph T ≤ p.toSubgraph.spanningCoe := by
    rw [← hcycle]
    exact (latticeCellBoundaryGraph_le_iff T S).2 hTBonds
  have hTeven : ∀ x : LatticeVertex, Even ((latticeCellBoundaryGraph T).neighborSet x).ncard :=
    latticeCellBoundaryGraph_even_degree T
  have hTnotbot : latticeCellBoundaryGraph T ≠ (⊥ : SimpleGraph LatticeVertex) := by
    intro hbot
    have hbonds : latticeCellBoundaryBonds T = latticeCellBoundaryBonds (∅ : Finset LatticeVertex) := by
      apply (latticeCellBoundaryGraph_eq_iff T ∅).mp
      rw [hbot, latticeCellBoundaryGraph_empty]
    have hTempty : T = ∅ := latticeCellBoundaryBonds_injective hbonds
    obtain ⟨x,hx⟩ := hTnonempty
    rw [hTempty] at hx
    simp at hx
  have hcyclecase := evenSubgraphOfCycle_eq_bot_or_cycle_of_finite_support p hp
    (latticeCellBoundaryGraph T) hTle hTeven
  have hTcycle : latticeCellBoundaryGraph T = p.toSubgraph.spanningCoe := by
    rcases hcyclecase with hbot | hfull
    · exact (hTnotbot hbot).elim
    · exact hfull
  have hTboundaries : latticeCellBoundaryBonds T = latticeCellBoundaryBonds S := by
    apply Finset.Subset.antisymm
    · exact hTBonds
    · apply (latticeCellBoundaryGraph_le_iff S T).mp
      rw [hcycle, ← hTcycle]
  have hTS : T = S := latticeCellBoundaryBonds_injective hTboundaries
  have hcT : c ∈ T := Finset.mem_filter.mpr ⟨hcB, ⟨hc,hcreach⟩⟩
  have : c ∈ S := by simpa [hTS] using hcT
  exact hc this

private theorem exists_reachable_exterior_of_box
    {v : LatticeVertex} {p : squareLattice.Walk v v} (hp : p.IsCycle)
    (S B : Finset LatticeVertex)
    (hcycle : latticeCellBoundaryGraph S = p.toSubgraph.spanningCoe)
    (c : LatticeVertex) (hc : c ∉ S) :
    ∃ z, ∃ hz : z ∉ S, z ∉ B ∧
      (cellComplementGraph S).Reachable ⟨c,hc⟩ ⟨z,hz⟩ := by
  classical
  by_contra h
  apply complement_component_not_bounded hp S B hcycle c hc
  intro z hz hreach
  by_contra hzB
  exact h ⟨z, hz, hzB, hreach⟩

theorem squareLattice_induce_latticePolygon_exteriorCellBases_connected
    {v : LatticeVertex} {p : squareLattice.Walk v v} (hp : p.IsCycle)
    (δ : PositiveMesh) :
    (squareLattice.induce
      {z : LatticeVertex | z ∉ (latticePolygonOfCycle hp).interiorCellBases δ}).Connected := by
  classical
  let P := latticePolygonOfCycle hp
  let S := P.interiorCellBases δ
  have hcycle : latticeCellBoundaryGraph S = p.toSubgraph.spanningCoe := by
    simpa [P, S] using latticeCellBoundaryGraph_interiorCellBases_eq_cycle hp δ
  obtain ⟨r, hSbox⟩ := finite_vertex_set_subset_box S
  let R : ℤ := (r : ℤ) + 1
  have hR : (r : ℤ) < R := by simp [R]
  have hanchorBox : (R,R) ∉ latticeBox (0,0) r := by
    rw [mem_latticeBox]
    omega
  have hanchorS : (R,R) ∉ S := by
    intro h
    exact hanchorBox (hSbox h)
  let anchor : {z : LatticeVertex // z ∉ S} := ⟨(R,R), hanchorS⟩
  let boxGraph := squareLattice.induce {z : LatticeVertex | z ∉ latticeBox (0,0) r}
  let lift : boxGraph →g cellComplementGraph S :=
    { toFun := fun z => ⟨z.1, fun hzS => z.2 (hSbox hzS)⟩
      map_rel' := by
        intro a b hab
        exact hab }
  rw [connected_iff_exists_forall_reachable]
  refine ⟨anchor, ?_⟩
  intro z
  obtain ⟨a, haS, haBox, hreachA⟩ :=
    exists_reachable_exterior_of_box hp S (latticeBox (0,0) r) hcycle
      anchor.1 anchor.2
  obtain ⟨b, hbS, hbBox, hreachB⟩ :=
    exists_reachable_exterior_of_box hp S (latticeBox (0,0) r) hcycle
      z.1 z.2
  have hboxConnected := squareLattice_induce_latticeBox_compl_connected r
  rw [connected_iff_exists_forall_reachable] at hboxConnected
  obtain ⟨q,hq⟩ := hboxConnected
  have hbox : boxGraph.Reachable ⟨a,haBox⟩ ⟨b,hbBox⟩ := by
    exact (hq ⟨a,haBox⟩).symm.trans (hq ⟨b,hbBox⟩)
  have hmid : (cellComplementGraph S).Reachable ⟨a,haS⟩ ⟨b,hbS⟩ := hbox.map lift
  exact hreachA.trans (hmid.trans hreachB.symm)

end PottsContinuity.FKC.Domains
