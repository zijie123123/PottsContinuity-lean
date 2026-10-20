module

public import PottsContinuity.Thm3.Easy.P5FrameCycleExtract
public import PottsContinuity.FKC.Domains.LatticePolygonOfCycle

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

/-- The P5 frame walks yield the actual simple polygon carried by their
open annulus cycle. The remaining enclosure question is point location in its
bounded Jordan domain. -/
theorem p5_frame_crossings_yield_openSimplePolygon_rayIndex
    (n m : ℕ) (hnm : n + 2 ≤ 6 * m)
    (ω : (squareLattice.induce
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ))).edgeSet → Bool)
    (hTop : p5FrameCrossing n m 0 ω)
    (hBottom : p5FrameCrossing n m 1 ω)
    (hRight : p5FrameCrossing n m 2 ω)
    (hLeft : p5FrameCrossing n m 3 ω) :
    ∃ z : LatticeVertex, ∃ p : squareLattice.Walk z z,
      ∃ _hp : p.IsCycle,
        rayIndex (0, 0) p ≠ 0 ∧
        ∃ k : ℕ, ∃ P : FKC.LatticePolygon k,
          k + 3 = p.length ∧
          (∀ i : ZMod (k + 3), P.vertex i = p.getVert i.val) ∧
          (∀ i : ZMod (k + 3), P.vertex i ∈ p5aAnnulusVertexSet n) ∧
          (∀ i : ZMod (k + 3),
            (n : ℤ) < max |(P.vertex i).1| |(P.vertex i).2| ∧
              max |(P.vertex i).1| |(P.vertex i).2| ≤ 2 * (n : ℤ)) ∧
          (∀ i : ZMod (k + 3), ∃ hi hj,
            (rcOpenGraph (p5aAnnulusVertexSet n) ω).Adj
              ⟨P.vertex i, hi⟩ ⟨P.vertex (i + 1), hj⟩) := by
  obtain ⟨z₀, q₀, hqCycle, hqIndex⟩ :=
    p5_frame_crossings_yield_simpleClosedWalk_rayIndex_ne_zero
      n m hnm ω hTop hBottom hRight hLeft
  let φ := p5ClosedWalkToSquareLattice (p5aAnnulusVertexSet n) ω
  let p := q₀.map φ
  have hφInjective : Function.Injective φ := by
    intro a b h
    exact Subtype.ext h
  have hpCycle : p.IsCycle := by
    exact (q₀.isCycle_map_iff_of_injective hφInjective).2 hqCycle
  have hpIndex : rayIndex (0, 0) p ≠ 0 := hqIndex
  let ψ : PD.FK.squareLattice →g FKC.squareLattice := {
    toFun := id
    map_rel' := by
      intro a b hab
      exact (FKC.squareLattice_adj_iff a b).2
        ((PD.FK.squareLattice_adj_iff a b).1 hab)
  }
  let r := p.map ψ
  have hψInjective : Function.Injective ψ := by
    intro a b h
    exact h
  have hrCycle : r.IsCycle := by
    exact (p.isCycle_map_iff_of_injective hψInjective).2 hpCycle
  have hlenRP : r.length = p.length := by simp [r]
  have hlenPQ : p.length = q₀.length := by simp [p]
  have hlength : r.length = q₀.length := hlenRP.trans hlenPQ
  have hlen3 : r.length - 3 + 3 = r.length := by
    have h3 := hrCycle.three_le_length
    omega
  let P : FKC.LatticePolygon (r.length - 3) :=
    @FKC.latticePolygonOfCycle _ r hrCycle
  have hcurrentVertex (i : ZMod (r.length - 3 + 3)) :
      P.vertex i = (q₀.getVert i.val).val := by
    change r.getVert i.val = (q₀.getVert i.val).val
    rw [SimpleGraph.Walk.getVert_map, SimpleGraph.Walk.getVert_map]
    rfl
  have hnextVertex (i : ZMod (r.length - 3 + 3)) :
      P.vertex (i + 1) = (q₀.getVert (i.val + 1)).val := by
    rw [@FKC.latticePolygonOfCycle_vertex_succ _ r hrCycle i]
    rw [SimpleGraph.Walk.getVert_map, SimpleGraph.Walk.getVert_map]
    rfl
  have hvertices (i : ZMod (r.length - 3 + 3)) :
      P.vertex i ∈ p5aAnnulusVertexSet n := by
    rw [hcurrentVertex i]
    exact (q₀.getVert i.val).property
  have hpolygonWalk (i : ZMod (r.length - 3 + 3)) :
      P.vertex i = p.getVert i.val := by
    rw [hcurrentVertex i]
    change (q₀.getVert i.val).val = (q₀.map φ).getVert i.val
    rw [SimpleGraph.Walk.getVert_map]
    rfl
  have hradial (i : ZMod (r.length - 3 + 3)) :
      (n : ℤ) < max |(P.vertex i).1| |(P.vertex i).2| ∧
        max |(P.vertex i).1| |(P.vertex i).2| ≤ 2 * (n : ℤ) := by
    let v := P.vertex i
    have hv := hvertices i
    change v ∈ PottsContinuity.box (2 * n) \
      PottsContinuity.box (n + 1) at hv
    rw [Finset.mem_sdiff] at hv
    have hout :=
      (PottsContinuity.Foundations.mem_box_iff_abs_le (2 * n) v).mp hv.1
    have hnot : ¬ (|v.1| ≤ ((n + 1 : ℕ) : ℤ) ∧
        |v.2| ≤ ((n + 1 : ℕ) : ℤ)) := by
      intro hsmall
      exact hv.2
        ((PottsContinuity.Foundations.mem_box_iff_abs_le (n + 1) v).2 hsmall)
    have hgreater : ((n + 1 : ℕ) : ℤ) < max |v.1| |v.2| := by
      by_contra hnotGreater
      apply hnot
      have hmax := le_of_not_gt hnotGreater
      exact ⟨le_trans (le_max_left _ _) hmax,
        le_trans (le_max_right _ _) hmax⟩
    constructor
    · exact lt_of_lt_of_le (by omega) hgreater
    · change max |v.1| |v.2| ≤ 2 * (n : ℤ)
      apply max_le_iff.mpr
      constructor
      · exact le_trans hout.1 (by norm_num)
      · exact le_trans hout.2 (by norm_num)
  have hedgeOpen (i : ZMod (r.length - 3 + 3)) :
      (rcOpenGraph (p5aAnnulusVertexSet n) ω).Adj
        ⟨P.vertex i, hvertices i⟩ ⟨P.vertex (i + 1), hvertices (i + 1)⟩ := by
    have hiR : i.val < r.length := by
      have hi := i.val_lt
      omega
    have hi : i.val < q₀.length := by rw [← hlength]; exact hiR
    have hadj := q₀.adj_getVert_succ hi
    have hsource : (⟨P.vertex i, hvertices i⟩ :
        (p5aAnnulusVertexSet n : Set (ℤ × ℤ))) = q₀.getVert i.val := by
      apply Subtype.ext
      exact hcurrentVertex i
    have htarget : (⟨P.vertex (i + 1), hvertices (i + 1)⟩ :
        (p5aAnnulusVertexSet n : Set (ℤ × ℤ))) = q₀.getVert (i.val + 1) := by
      apply Subtype.ext
      exact hnextVertex i
    rw [hsource, htarget]
    exact hadj
  refine ⟨z₀.1, p, hpCycle, hpIndex, r.length - 3, P, ?_, hpolygonWalk,
    hvertices, hradial, ?_⟩
  · calc
      r.length - 3 + 3 = r.length := hlen3
      _ = p.length := hlenRP
  · intro i
    exact ⟨hvertices i, hvertices (i + 1), hedgeOpen i⟩

end PottsContinuity.Thm3.Easy
