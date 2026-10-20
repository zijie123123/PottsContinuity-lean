module

public import PottsContinuity.Thm3.Easy.P5AnnulusDoubleDualCandidate
public import PottsContinuity.DualityExt.PositiveAnnulusPrimalDMP

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity.PD.FK
open PottsContinuity.DualityExt

noncomputable section

private theorem annulusVertexSet_of_bounds
    (N : ℕ) (hN : 1 ≤ N) (x y : ℤ)
    (hxl : -(2 * (N : ℤ)) ≤ x) (hxu : x ≤ 2 * (N : ℤ))
    (hyl : -(2 * (N : ℤ)) ≤ y) (hyu : y ≤ 2 * (N : ℤ))
    (hout : (N : ℤ) ≤ x ∨ x ≤ -(N : ℤ) ∨
      (N : ℤ) ≤ y ∨ y ≤ -(N : ℤ)) :
    (x, y) ∈ annulusVertexSet N := by
  have hNm1 : ((N - 1 : ℕ) : ℤ) + 1 = (N : ℤ) := by
    exact_mod_cast Nat.sub_add_cancel hN
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [mem_latticeBox]
    simp only [zero_sub, zero_add]
    constructor <;> constructor <;> omega
  · intro hin
    have hi := (mem_latticeBox (0, 0) (x, y) (N - 1)).mp hin
    simp only [zero_sub, zero_add] at hi
    rcases hout with hx | hx | hy | hy <;> omega

private theorem annulusSourceGraph_edge_incident_first
    (N : ℕ) (z : {v : LatticeVertex // v ∈ annulusVertexSet N})
    (w : LatticeVertex) (hw : w ∈ annulusVertexSet N)
    (hadj : squareLattice.Adj z.1 w) :
    ∃ e : (annulusSourceGraph N).edgeSet, z ∈ e.1.toFinset := by
  let v : {v : LatticeVertex // v ∈ annulusVertexSet N} := ⟨w, hw⟩
  let e : (annulusSourceGraph N).edgeSet := ⟨s(z, v), by
    change squareLattice.Adj z.1 w
    exact hadj⟩
  refine ⟨e, ?_⟩
  change z ∈ (s(z, v)).toFinset
  simp

private theorem annulusAdj_x_pred (x y : ℤ) :
    squareLattice.Adj (x, y) (x - 1, y) := by
  change PottsContinuity.PD.FK.squareLattice.Adj (x, y) (x - 1, y)
  rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
  exact Or.inl ⟨Or.inr (by omega), rfl⟩

private theorem annulusAdj_x_succ (x y : ℤ) :
    squareLattice.Adj (x, y) (x + 1, y) := by
  change PottsContinuity.PD.FK.squareLattice.Adj (x, y) (x + 1, y)
  rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
  exact Or.inl ⟨Or.inl rfl, rfl⟩

private theorem annulusAdj_y_pred (x y : ℤ) :
    squareLattice.Adj (x, y) (x, y - 1) := by
  change PottsContinuity.PD.FK.squareLattice.Adj (x, y) (x, y - 1)
  rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
  exact Or.inr ⟨rfl, Or.inr (by omega)⟩

private theorem annulusAdj_y_succ (x y : ℤ) :
    squareLattice.Adj (x, y) (x, y + 1) := by
  change PottsContinuity.PD.FK.squareLattice.Adj (x, y) (x, y + 1)
  rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
  exact Or.inr ⟨rfl, Or.inl rfl⟩

 theorem annulusSourceGraph_vertex_has_incident_edge
    (N : ℕ) (hN : 2 ≤ N)
    (z : {v : LatticeVertex // v ∈ annulusVertexSet N}) :
    ∃ e : (annulusSourceGraph N).edgeSet, z ∈ e.1.toFinset := by
  have hzOuter := (mem_latticeBox (0, 0) z.1 (2 * N)).mp
    (Finset.mem_sdiff.mp z.2).1
  have hzInner : z.1 ∉ latticeBox (0, 0) (N - 1) :=
    (Finset.mem_sdiff.mp z.2).2
  simp only [zero_sub, zero_add] at hzOuter
  have hNint : (1 : ℤ) ≤ (N : ℤ) := by omega
  have hNm1 : ((N - 1 : ℕ) : ℤ) + 1 = (N : ℤ) := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ N)
  have hcase : (N : ℤ) ≤ z.1.1 ∨ z.1.1 ≤ -(N : ℤ) ∨
      (N : ℤ) ≤ z.1.2 ∨ z.1.2 ≤ -(N : ℤ) := by
    by_contra h
    push Not at h
    apply hzInner
    rw [mem_latticeBox]
    simp only [zero_sub, zero_add]
    omega
  rcases hzOuter with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  rcases hcase with hxp | hxn | hyp | hyn
  · by_cases hboundary : z.1.1 = 2 * (N : ℤ)
    · let w : LatticeVertex := (z.1.1 - 1, z.1.2)
      have hw : w ∈ annulusVertexSet N := by
        apply annulusVertexSet_of_bounds N (by omega) w.1 w.2 <;> simp only [w] <;> omega
      exact annulusSourceGraph_edge_incident_first N z w hw
        (annulusAdj_x_pred z.1.1 z.1.2)
    · let w : LatticeVertex := (z.1.1 + 1, z.1.2)
      have hw : w ∈ annulusVertexSet N := by
        apply annulusVertexSet_of_bounds N (by omega) w.1 w.2 <;> simp only [w] <;> omega
      exact annulusSourceGraph_edge_incident_first N z w hw
        (annulusAdj_x_succ z.1.1 z.1.2)
  · by_cases hboundary : z.1.1 = -(2 * (N : ℤ))
    · let w : LatticeVertex := (z.1.1 + 1, z.1.2)
      have hw : w ∈ annulusVertexSet N := by
        apply annulusVertexSet_of_bounds N (by omega) w.1 w.2 <;> simp only [w] <;> omega
      exact annulusSourceGraph_edge_incident_first N z w hw
        (annulusAdj_x_succ z.1.1 z.1.2)
    · let w : LatticeVertex := (z.1.1 - 1, z.1.2)
      have hw : w ∈ annulusVertexSet N := by
        apply annulusVertexSet_of_bounds N (by omega) w.1 w.2 <;> simp only [w] <;> omega
      exact annulusSourceGraph_edge_incident_first N z w hw
        (annulusAdj_x_pred z.1.1 z.1.2)
  · by_cases hboundary : z.1.2 = 2 * (N : ℤ)
    · let w : LatticeVertex := (z.1.1, z.1.2 - 1)
      have hw : w ∈ annulusVertexSet N := by
        apply annulusVertexSet_of_bounds N (by omega) w.1 w.2 <;> simp only [w] <;> omega
      exact annulusSourceGraph_edge_incident_first N z w hw
        (annulusAdj_y_pred z.1.1 z.1.2)
    · let w : LatticeVertex := (z.1.1, z.1.2 + 1)
      have hw : w ∈ annulusVertexSet N := by
        apply annulusVertexSet_of_bounds N (by omega) w.1 w.2 <;> simp only [w] <;> omega
      exact annulusSourceGraph_edge_incident_first N z w hw
        (annulusAdj_y_succ z.1.1 z.1.2)
  · by_cases hboundary : z.1.2 = -(2 * (N : ℤ))
    · let w : LatticeVertex := (z.1.1, z.1.2 + 1)
      have hw : w ∈ annulusVertexSet N := by
        apply annulusVertexSet_of_bounds N (by omega) w.1 w.2 <;> simp only [w] <;> omega
      exact annulusSourceGraph_edge_incident_first N z w hw
        (annulusAdj_y_succ z.1.1 z.1.2)
    · let w : LatticeVertex := (z.1.1, z.1.2 - 1)
      have hw : w ∈ annulusVertexSet N := by
        apply annulusVertexSet_of_bounds N (by omega) w.1 w.2 <;> simp only [w] <;> omega
      exact annulusSourceGraph_edge_incident_first N z w hw
        (annulusAdj_y_pred z.1.1 z.1.2)

def annulusCandidateDoubleDualShift (N : ℕ)
    (z : RectangleDualVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)) : LatticeVertex :=
  (z.1.1 + 1, z.1.2 + 1)

 theorem annulusCandidateDoubleDualShift_injective (N : ℕ) :
    Function.Injective (annulusCandidateDoubleDualShift N) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact add_right_cancel (congrArg Prod.fst h)
  · exact add_right_cancel (congrArg Prod.snd h)

 theorem annulusCandidateDoubleDualShift_mem_of_active
    (N : ℕ) (_hN : 2 ≤ N)
    (z : positiveActiveVertexSet
      (rectangleSubgraphDualGraph (annulusExpandedHostDualCandidateGraph_le_rectangle N))) :
    annulusCandidateDoubleDualShift N z.1 ∈ annulusVertexSet N := by
  let : DecidableEq (RectangleDualVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)) := fun a b => Classical.propDecidable (a = b)
  have hz := z.2
  unfold positiveActiveVertexSet at hz
  simp only [Set.mem_ofPred_eq] at hz
  rcases hz with ⟨d, hzd⟩
  let b := (annulusCandidateDoubleDualEdgeEquiv N).symm d
  have hp := p5aAnnulusCandidate_doubleDual_edge_pair_source N b
  have hmem : annulusCandidateDoubleDualShift N z.1 ∈
      Sym2.map (annulusCandidateDoubleDualShift N) d.1 := by
    rw [Sym2.mem_map]
    exact ⟨z.1, Sym2.mem_toFinset.mp hzd, rfl⟩
  have hdeq : d = annulusCandidateDoubleDualEdgeEquiv N b :=
    (Equiv.apply_symm_apply (annulusCandidateDoubleDualEdgeEquiv N) d).symm
  rw [hdeq] at hmem
  change annulusCandidateDoubleDualShift N z.1 ∈
    Sym2.map (fun x : RectangleDualVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1) => (x.1.1 + 1, x.1.2 + 1))
      (annulusCandidateDoubleDualEdgeEquiv N b).val at hmem
  rw [hp] at hmem
  obtain ⟨v, hv, hval⟩ := Sym2.mem_map.mp hmem
  exact hval.symm ▸ v.2

 theorem annulusCandidateDoubleDualInverseVertex_mem
    (N : ℕ) (v : {x : LatticeVertex // x ∈ annulusVertexSet N}) :
    (v.1.1 - 1, v.1.2 - 1) ∈
      rectangleDualExpanded (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1) := by
  have hv := (Finset.mem_sdiff.mp v.2).1
  rw [mem_latticeBox] at hv
  rw [rectangleDualExpanded, mem_latticeRectangle]
  simp only [annulusDualExpandedHostAnchor, annulusHostAnchor,
    ]
  rcases hv with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  constructor <;> constructor <;> omega

noncomputable def annulusCandidateDoubleDualInverseVertex
    (N : ℕ) (hN : 2 ≤ N)
    (v : {x : LatticeVertex // x ∈ annulusVertexSet N}) :
    positiveActiveVertexSet (rectangleSubgraphDualGraph
      (annulusExpandedHostDualCandidateGraph_le_rectangle N)) := by
  refine ⟨⟨(v.1.1 - 1, v.1.2 - 1), annulusCandidateDoubleDualInverseVertex_mem N v⟩, ?_⟩
  let : DecidableEq (RectangleDualVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)) := fun a b => Classical.propDecidable (a = b)
  unfold positiveActiveVertexSet
  simp only [Set.mem_ofPred_eq]
  let z : RectangleDualVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1) :=
    ⟨(v.1.1 - 1, v.1.2 - 1), annulusCandidateDoubleDualInverseVertex_mem N v⟩
  obtain ⟨b, hvb⟩ := annulusSourceGraph_vertex_has_incident_edge N hN v
  let d := annulusCandidateDoubleDualEdgeEquiv N b
  have hp := p5aAnnulusCandidate_doubleDual_edge_pair_source N b
  have hvmem : v.1 ∈ Sym2.map (fun x :
      {x : LatticeVertex // x ∈ annulusVertexSet N} => x.1) b.1 := by
    rw [Sym2.mem_map]
    exact ⟨v, Sym2.mem_toFinset.mp hvb, rfl⟩
  have hshiftmem : v.1 ∈ Sym2.map (annulusCandidateDoubleDualShift N)
      (annulusCandidateDoubleDualEdgeEquiv N b).val := by
    change v.1 ∈ Sym2.map (fun x : RectangleDualVertex
      (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1) =>
        (x.1.1 + 1, x.1.2 + 1))
        (annulusCandidateDoubleDualEdgeEquiv N b).val
    rw [hp]
    exact hvmem
  obtain ⟨x, hxd, hval⟩ := Sym2.mem_map.mp hshiftmem
  have hx : x.1 = (v.1.1 - 1, v.1.2 - 1) := by
    change (x.1.1 + 1, x.1.2 + 1) = v.1 at hval
    apply Prod.ext
    · have hcoord := congrArg Prod.fst hval
      omega
    · have hcoord := congrArg Prod.snd hval
      omega
  have hx' : x = z := by
    apply Subtype.ext
    exact hx
  have hfin : z ∈ d.1.toFinset := by
    rw [← hx']
    exact Sym2.mem_toFinset.mpr hxd
  exact ⟨d, hfin⟩

noncomputable def annulusCandidateDoubleDualActiveVertexEquiv
    (N : ℕ) (hN : 2 ≤ N) :
    positiveActiveVertexSet
      (rectangleSubgraphDualGraph (annulusExpandedHostDualCandidateGraph_le_rectangle N)) ≃
      {v : LatticeVertex // v ∈ annulusVertexSet N} := by
  classical
  refine Equiv.ofBijective
    (fun z => ⟨annulusCandidateDoubleDualShift N z.1,
      annulusCandidateDoubleDualShift_mem_of_active N hN z⟩) ?_
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact annulusCandidateDoubleDualShift_injective N (congrArg Subtype.val hxy)
  · intro v
    refine ⟨annulusCandidateDoubleDualInverseVertex N hN v, ?_⟩
    apply Subtype.ext
    change (v.1.1 - 1 + 1, v.1.2 - 1 + 1) = v.1
    exact Prod.ext (by omega) (by omega)

@[simp] theorem annulusCandidateDoubleDualActiveVertexEquiv_apply_val
    (N : ℕ) (hN : 2 ≤ N)
    (z : positiveActiveVertexSet
      (rectangleSubgraphDualGraph (annulusExpandedHostDualCandidateGraph_le_rectangle N))) :
    (annulusCandidateDoubleDualActiveVertexEquiv N hN z).1 =
      annulusCandidateDoubleDualShift N z.1 := rfl

theorem annulusCandidateDoubleDualActiveGraph_map_eq
    (N : ℕ) (hN : 2 ≤ N) :
    (positiveActiveGraph (rectangleSubgraphDualGraph
      (annulusExpandedHostDualCandidateGraph_le_rectangle N))).map
        (annulusCandidateDoubleDualActiveVertexEquiv N hN).toEmbedding =
      annulusSourceGraph N := by
  classical
  let H := rectangleSubgraphDualGraph
    (annulusExpandedHostDualCandidateGraph_le_rectangle N)
  let e := annulusCandidateDoubleDualActiveVertexEquiv N hN
  let source := annulusSourceGraph N
  apply SimpleGraph.ext
  funext u v
  apply propext
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨x, y, hxy, hxu, hyv⟩
    let d : H.edgeSet := ⟨s(x.1, y.1), H.mem_edgeSet.mpr hxy⟩
    let b := (annulusCandidateDoubleDualEdgeEquiv N).symm d
    have hp := p5aAnnulusCandidate_doubleDual_edge_pair_source N b
    have hdeq : annulusCandidateDoubleDualEdgeEquiv N b = d :=
      Equiv.apply_symm_apply (annulusCandidateDoubleDualEdgeEquiv N) d
    have hpair : Sym2.map (fun z : {z : LatticeVertex // z ∈ annulusVertexSet N} => z.1)
        (s(u, v)) = Sym2.map (fun z : {z : LatticeVertex // z ∈ annulusVertexSet N} => z.1)
          b.1 := by
      have hp' : Sym2.map (annulusCandidateDoubleDualShift N) d.1 =
          Sym2.map (fun z : {z : LatticeVertex // z ∈ annulusVertexSet N} => z.1)
            b.1 := by
        change Sym2.map (fun z : RectangleDualVertex (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1) => (z.1.1 + 1, z.1.2 + 1)) d.1 = _
        rw [← hdeq]
        exact hp
      have hxu' : u.1 = annulusCandidateDoubleDualShift N x.1 := by
        calc
          u.1 = (e x).1 := congrArg Subtype.val hxu.symm
          _ = annulusCandidateDoubleDualShift N x.1 := by
            simp [e]
      have hyv' : v.1 = annulusCandidateDoubleDualShift N y.1 := by
        calc
          v.1 = (e y).1 := congrArg Subtype.val hyv.symm
          _ = annulusCandidateDoubleDualShift N y.1 := by
            simp [e]
      simpa [d, hxu', hyv'] using hp'
    have hbpair : s(u, v) = b.1 :=
      (Sym2.map.injective Subtype.val_injective) hpair
    have hedge : s(u, v) ∈ source.edgeSet := hbpair.symm ▸ b.2
    exact source.mem_edgeSet.mp hedge
  · intro huv
    let b : source.edgeSet := ⟨s(u, v), source.mem_edgeSet.mpr huv⟩
    let d := annulusCandidateDoubleDualEdgeEquiv N b
    let x := e.symm u
    let y := e.symm v
    have hp := p5aAnnulusCandidate_doubleDual_edge_pair_source N b
    have hxu : annulusCandidateDoubleDualShift N x.1 = u.1 := by
      calc
        annulusCandidateDoubleDualShift N x.1 = (e x).1 := by
          simp [e]
        _ = u.1 := congrArg Subtype.val (Equiv.apply_symm_apply e u)
    have hyv : annulusCandidateDoubleDualShift N y.1 = v.1 := by
      calc
        annulusCandidateDoubleDualShift N y.1 = (e y).1 := by
          simp [e]
        _ = v.1 := congrArg Subtype.val (Equiv.apply_symm_apply e v)
    have hpair : Sym2.map (annulusCandidateDoubleDualShift N) d.1 =
        Sym2.map (annulusCandidateDoubleDualShift N) (s(x.1, y.1)) := by
      have hdeq : annulusCandidateDoubleDualEdgeEquiv N b = d := rfl
      have hp' : Sym2.map (fun z : RectangleDualVertex (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1) => (z.1.1 + 1, z.1.2 + 1)) d.1 =
          Sym2.map (fun z : {z : LatticeVertex // z ∈ annulusVertexSet N} => z.1)
            b.1 := by
        change Sym2.map (fun z : RectangleDualVertex (annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1) => (z.1.1 + 1, z.1.2 + 1))
          (annulusCandidateDoubleDualEdgeEquiv N b).val = _ at hp
        rw [← hdeq]
        exact hp
      have hp2 : Sym2.map (fun z : {z : LatticeVertex // z ∈ annulusVertexSet N} => z.1)
          b.1 = Sym2.map (annulusCandidateDoubleDualShift N) (s(x.1, y.1)) := by
        simp only [b, Sym2.map_mk]
        rw [← hxu, ← hyv]
      exact hp'.trans hp2
    have hd : d.1 = s(x.1, y.1) :=
      (Sym2.map.injective (annulusCandidateDoubleDualShift_injective N)) hpair
    have hedge : s(x.1, y.1) ∈ H.edgeSet := hd ▸ d.2
    have hxy : H.Adj x.1 y.1 := H.mem_edgeSet.mp hedge
    have hactive : (positiveActiveGraph H).Adj x y := by
      change H.Adj x.1 y.1
      exact hxy
    exact ⟨x, y, hactive, Equiv.apply_symm_apply e u,
      Equiv.apply_symm_apply e v⟩

theorem annulusCandidateDoubleDualActiveEdgeEquiv_eq
    (N : ℕ) (hN : 2 ≤ N) :
    p5aActiveDoubleDualToSourceEdgeEquiv N
        (annulusExpandedHostDualCandidateGraph_le_rectangle N)
        (annulusCandidateDoubleDualActiveVertexEquiv N hN)
        (annulusCandidateDoubleDualActiveGraph_map_eq N hN) =
      (annulusCandidateDoubleDualEdgeEquiv N).symm := by
  classical
  apply Equiv.ext
  intro d
  let hK := annulusExpandedHostDualCandidateGraph_le_rectangle N
  let H := rectangleSubgraphDualGraph hK
  let A := positiveActiveGraph H
  let e := annulusCandidateDoubleDualActiveVertexEquiv N hN
  let hgraph := annulusCandidateDoubleDualActiveGraph_map_eq N hN
  let b := (annulusCandidateDoubleDualEdgeEquiv N).symm d
  have hdb : annulusCandidateDoubleDualEdgeEquiv N b = d :=
    Equiv.apply_symm_apply (annulusCandidateDoubleDualEdgeEquiv N) d
  have hactive := Equiv.apply_symm_apply
    (positiveActiveEdgeToGraphEquiv H) d
  have hactivePair : Sym2.map (positiveActiveInclusion H)
      ((positiveActiveEdgeToGraphEquiv H).symm d).val = d.val := by
    exact congrArg Subtype.val hactive
  have hpair : Sym2.map (annulusCandidateDoubleDualShift N)
      d.val = Sym2.map (fun x : {v : LatticeVertex // v ∈ annulusVertexSet N} => x.1)
        b.val := by
    rw [← hdb]
    exact p5aAnnulusCandidate_doubleDual_edge_pair_source N b
  have hlabelsVal : Sym2.map (fun x : positiveActiveVertexSet H => (e x).1)
      ((positiveActiveEdgeToGraphEquiv H).symm d).val =
      Sym2.map (fun x : {v : LatticeVertex // v ∈ annulusVertexSet N} => x.1)
        b.val := by
    calc
      _ = Sym2.map (annulusCandidateDoubleDualShift N) d.val := by
        rw [← hactivePair, Sym2.map_map]
        congr 1
      _ = _ := hpair
  have hlabels : Sym2.map e
      ((positiveActiveEdgeToGraphEquiv H).symm d).val = b.val := by
    apply (Sym2.map.injective Subtype.val_injective)
    simpa only [Sym2.map_map, Function.comp_apply] using hlabelsVal
  have hlabels' := hlabels
  rw [← hdb] at hlabels'
  rw [← hdb]
  apply Subtype.ext
  change Sym2.map e
      ((positiveActiveEdgeToGraphEquiv H).symm
        (annulusCandidateDoubleDualEdgeEquiv N b)).val =
    ((annulusCandidateDoubleDualEdgeEquiv N).symm
      (annulusCandidateDoubleDualEdgeEquiv N b)).val
  rw [Equiv.symm_apply_apply]
  exact hlabels'

theorem annulusCandidateDoubleDualConfigurationMap_eq
    (N : ℕ) (hN : 2 ≤ N) :
    (annulusPrimalToEmbeddedDualConfigurationEquiv N
      (annulusExpandedHostDualCandidateGraph_le_rectangle N)
      (annulusCandidateDoubleDualActiveVertexEquiv N hN)
      (annulusCandidateDoubleDualActiveGraph_map_eq N hN)).trans
        (annulusCandidateToActualDualConfigurationEquiv N
          (annulusExpandedHostCarrierEquiv N)
          (annulusExpandedHostDualCandidateGraph_map_eq N)) =
      (isolatedExtensionConfigurationEquiv (annulusSourceGraph N)
        (annulusSourceEmbedding N)).trans
        (rectangleSubgraphDualConfigurationEquiv
          (annulusSourceGraph_map_le_host N)) := by
  apply p5aAnnulusCompositeDualMap_eq_of_edgeLabelAgreement
    (N := N)
    (hK := annulusExpandedHostDualCandidateGraph_le_rectangle N)
    (e := annulusCandidateDoubleDualActiveVertexEquiv N hN)
    (hgraph := annulusCandidateDoubleDualActiveGraph_map_eq N hN)
    (f := annulusExpandedHostCarrierEquiv N)
    (hIso := annulusExpandedHostDualCandidateGraph_map_eq N)
  intro d
  let hK := annulusExpandedHostDualCandidateGraph_le_rectangle N
  let hIso := annulusExpandedHostDualCandidateGraph_map_eq N
  let e := annulusCandidateDoubleDualActiveVertexEquiv N hN
  let hgraph := annulusCandidateDoubleDualActiveGraph_map_eq N hN
  let f := annulusExpandedHostCarrierEquiv N
  let g := p5aCandidateToActualDualEdgeEquiv N f hIso
  let b := (p5aSourceToActualDualEdgeEquiv N).symm d
  have hb : p5aSourceToActualDualEdgeEquiv N b = d :=
    Equiv.apply_symm_apply _ d
  have hdouble : annulusCandidateDoubleDualEdgeEquiv N b =
      rectangleSubgraphDualEdgeEmbedding hK (g.symm d) := by
    change rectangleSubgraphDualEdgeEquiv hK
        ((p5aCandidateToActualDualEdgeEquiv N f hIso).symm
          ((p5aSourceToActualDualEdgeEquiv N) b)) =
      rectangleSubgraphDualEdgeEquiv hK (g.symm d)
    rw [hb]
  have hleft : p5aActiveDoubleDualToSourceEdgeEquiv N hK e hgraph
      (rectangleSubgraphDualEdgeEmbedding hK (g.symm d)) = b := by
    rw [← hdouble]
    rw [annulusCandidateDoubleDualActiveEdgeEquiv_eq N hN]
    exact Equiv.symm_apply_apply _ b
  simpa [hK, hIso, e, hgraph, f, g, b] using hleft

end

end PottsContinuity.Thm3.Easy
