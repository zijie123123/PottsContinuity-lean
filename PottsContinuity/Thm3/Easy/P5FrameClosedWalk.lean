module

public import Mathlib
public import PottsContinuity.Thm3.Easy.P5FrameIntersections
public import PottsContinuity.PD.Duality.RayIndexSeparation
public import PottsContinuity.PlanarTopology.InterlacedPaths

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

/-- The vertex-inclusion graph hom from an open induced annulus graph to the
PD square lattice used by the ray-index API. -/
def p5ClosedWalkToSquareLattice (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    rcOpenGraph V ω →g PottsContinuity.PD.FK.squareLattice where
  toFun := fun z => z.1
  map_rel' := by
    intro z w hzw
    have h := PottsContinuity.RSW.rcOpenGraph_le_induced V ω hzw
    change squareLattice.Adj z.1 w.1 at h
    exact h

private theorem walk_between_support_vertices
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v a b : V}
    (p : G.Walk u v) (ha : a ∈ p.support) (hb : b ∈ p.support) :
    ∃ q : G.Walk a b, q.support ⊆ p.support := by
  let ia := p.support.idxOf a
  let ib := p.support.idxOf b
  by_cases hab : ia ≤ ib
  · let pb := p.takeUntil b hb
    have hindex : ia ≤ pb.length := by
      dsimp [pb, ia, ib]
      rw [SimpleGraph.Walk.length_takeUntil]
      exact hab
    have ha' : a ∈ pb.support := by
      have hget : pb.getVert ia = p.getVert ia :=
        p.getVert_takeUntil hb hindex
      have hget' : p.getVert ia = a := p.getVert_support_idxOf ha
      have hval : pb.getVert ia = a := hget.trans hget'
      rw [← hval]
      exact pb.getVert_mem_support ia
    refine ⟨pb.dropUntil a ha', ?_⟩
    intro x hx
    exact p.support_takeUntil_subset_support hb
      (pb.support_dropUntil_subset_support ha' hx)
  · let pa := p.takeUntil a ha
    have hindex : ib ≤ pa.length := by
      have hlt : ib < ia := Nat.lt_of_not_ge hab
      dsimp [pa, ia, ib]
      rw [SimpleGraph.Walk.length_takeUntil]
      exact hlt.le
    have hb' : b ∈ pa.support := by
      have hget : pa.getVert ib = p.getVert ib :=
        p.getVert_takeUntil ha hindex
      have hget' : p.getVert ib = b := p.getVert_support_idxOf hb
      have hval : pa.getVert ib = b := hget.trans hget'
      rw [← hval]
      exact pa.getVert_mem_support ib
    let q := pa.dropUntil b hb'
    refine ⟨q.reverse, ?_⟩
    intro x hx
    have hx' : x ∈ q.support := by
      simpa [q, SimpleGraph.Walk.support_reverse] using hx
    exact p.support_takeUntil_subset_support ha
      (pa.support_dropUntil_subset_support hb' hx')

private theorem p5_frame_crossings_closedWalk_data
    (n m : ℕ) (hnm : n + 2 ≤ 6 * m)
    (ω : (squareLattice.induce
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ))).edgeSet → Bool)
    (hTop : p5FrameCrossing n m 0 ω)
    (hBottom : p5FrameCrossing n m 1 ω)
    (hRight : p5FrameCrossing n m 2 ω)
    (hLeft : p5FrameCrossing n m 3 ω) :
    ∃ z : (p5aAnnulusVertexSet n : Set (ℤ × ℤ)),
      ∃ p : (rcOpenGraph (p5aAnnulusVertexSet n) ω).Walk z z,
        0 < p.length ∧
          rayIndex (0, 0)
            (p.map (p5ClosedWalkToSquareLattice (p5aAnnulusVertexSet n) ω)) = -1 := by
  obtain ⟨top, bottom, right, left, zTR, zBR, zBL, zTL,
      hTRtop, hTRright, hBRbottom, hBRright, hBLbottom, hBLleft,
      hTLtop, hTLleft, _, hTRy, _, hBRy, _, _, _, _⟩ :=
    p5_frame_crossings_coherent_adjacent_meet n m hnm ω hTop hBottom hRight hLeft
  have hTRneBR : zTR ≠ zBR := by
    intro h
    have hval := congrArg (fun z : (p5aAnnulusVertexSet n : Set (ℤ × ℤ)) => z.1.2) h
    have hTRlow := (Set.mem_Icc.mp hTRy).1
    have hBRhigh := (Set.mem_Icc.mp hBRy).2
    omega
  obtain ⟨pR, hpR⟩ := walk_between_support_vertices right.path hTRright hBRright
  obtain ⟨pB, hpB⟩ := walk_between_support_vertices bottom.path hBRbottom hBLbottom
  obtain ⟨pL, hpL⟩ := walk_between_support_vertices left.path hBLleft hTLleft
  obtain ⟨pT, hpT⟩ := walk_between_support_vertices top.path hTLtop hTRtop
  have hRpos : 0 < pR.length := by
    by_contra hnot
    have hzero : pR.length = 0 := Nat.eq_zero_of_not_pos hnot
    exact hTRneBR (SimpleGraph.Walk.eq_of_length_eq_zero hzero)
  let p := (((pR.append pB).append pL).append pT)
  have hpos : 0 < p.length := by
    dsimp [p]
    simp only [SimpleGraph.Walk.length_append]
    omega
  let φ := p5ClosedWalkToSquareLattice (p5aAnnulusVertexSet n) ω
  let pR' := pR.map φ
  let pB' := pB.map φ
  let pL' := pL.map φ
  let pT' := pT.map φ
  have hRSupport : ∀ x ∈ pR'.support, (0 : ℤ) ≤ x.1 := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    have h := right.inside y (hpR hy)
    simp only [p5FrameCrossingCorridor] at h
    have hx := (Set.mem_Icc.mp h.1).1
    have hbase : (0 : ℤ) ≤ (n : ℤ) + 2 + (m : ℤ) := by positivity
    change (0 : ℤ) ≤ y.1.1
    exact le_trans hbase hx
  have hBSupport : ∀ x ∈ pB'.support,
      (if x.2 < 0 then (1 : ℤ) else 0) = 1 := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    have h := bottom.inside y (hpB hy)
    simp only [p5FrameCrossingCorridor] at h
    have hyneg : y.1.2 < 0 := by
      have hyupper := (Set.mem_Icc.mp h.2).2
      omega
    change (if y.1.2 < 0 then (1 : ℤ) else 0) = 1
    simp [hyneg]
  have hLSupport : ∀ x ∈ pL'.support, x.1 < 0 := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    have h := left.inside y (hpL hy)
    simp only [p5FrameCrossingCorridor] at h
    have hxupper := (Set.mem_Icc.mp h.1).2
    have hbound : (-(n : ℤ) - 2 - (m : ℤ)) < 0 := by omega
    change y.1.1 < 0
    exact lt_of_le_of_lt hxupper hbound
  have hTSupport : ∀ x ∈ pT'.support,
      (if x.2 < 0 then (1 : ℤ) else 0) = 0 := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    have h := top.inside y (hpT hy)
    simp only [p5FrameCrossingCorridor] at h
    have hypos : 0 ≤ y.1.2 := by
      have hylower := (Set.mem_Icc.mp h.2).1
      omega
    change (if y.1.2 < 0 then (1 : ℤ) else 0) = 0
    simp [not_lt.mpr hypos]
  have hidxR : rayIndex (0, 0) pR' = -1 := by
    have htopp : ¬ (φ zTR).2 < 0 := by
      have h := (Set.mem_Icc.mp hTRy).1
      change ¬ zTR.1.2 < 0
      omega
    have hbottom : (φ zBR).2 < 0 := by
      have h := (Set.mem_Icc.mp hBRy).2
      change zBR.1.2 < 0
      omega
    have hformula := rayIndex_left_telescope (0, 0) pR' hRSupport
    dsimp at hformula
    rw [ite_eq_right htopp, ite_eq_left hbottom] at hformula
    omega
  have hidxB : rayIndex (0, 0) pB' = 0 :=
    rayIndex_zero_of_level (0, 0) pB' 1 hBSupport
  have hidxL : rayIndex (0, 0) pL' = 0 :=
    rayIndex_zero_of_right (0, 0) pL' hLSupport
  have hidxT : rayIndex (0, 0) pT' = 0 :=
    rayIndex_zero_of_level (0, 0) pT' 0 hTSupport
  have hmap : p.map φ = (((pR'.append pB').append pL').append pT') := by
    simp [p, pR', pB', pL', pT', SimpleGraph.Walk.map_append]
  have hindex : rayIndex (0, 0) (p.map φ) = -1 := by
    rw [hmap]
    simp only [PottsContinuity.PlanarTopology.rayIndex_append,
      hidxR, hidxB, hidxL, hidxT]
    norm_num
  exact ⟨zTR, p, hpos, hindex⟩

/-- The cyclic frame concatenation has horizontal-ray index `-1` at the
origin after mapping its annulus-graph walk into the square lattice. -/
theorem p5_frame_crossings_yield_closedWalk_rayIndex_eq_neg_one
    (n m : ℕ) (hnm : n + 2 ≤ 6 * m)
    (ω : (squareLattice.induce
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ))).edgeSet → Bool)
    (hTop : p5FrameCrossing n m 0 ω)
    (hBottom : p5FrameCrossing n m 1 ω)
    (hRight : p5FrameCrossing n m 2 ω)
    (hLeft : p5FrameCrossing n m 3 ω) :
    ∃ z : (p5aAnnulusVertexSet n : Set (ℤ × ℤ)),
      ∃ p : (rcOpenGraph (p5aAnnulusVertexSet n) ω).Walk z z,
        0 < p.length ∧
          rayIndex (0, 0)
            (p.map (p5ClosedWalkToSquareLattice (p5aAnnulusVertexSet n) ω)) = -1 :=
  p5_frame_crossings_closedWalk_data n m hnm ω hTop hBottom hRight hLeft

end PottsContinuity.Thm3.Easy
