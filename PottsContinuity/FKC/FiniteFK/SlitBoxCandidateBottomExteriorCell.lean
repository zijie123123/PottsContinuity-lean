-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateBottomExteriorCell.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateHorizontalStrips
public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

def bottomExteriorBaseHom (n : ℕ)
    (A : Configuration (slitBoxGraph n)) [Fintype (slitBoxGraph n).edgeSet
    ] (hA : A = Finset.univ) :
    slitBoxGraph n →g openGraph (slitBoxGraph n) A where
  toFun := id
  map_rel' := by
    intro x y hxy
    apply (openGraph_adj (slitBoxGraph n) A x y).2
    change s(x, y) ∈ Subtype.val '' (↑A : Set (slitBoxGraph n).edgeSet)
    rw [hA]
    exact ⟨⟨s(x, y), (slitBoxGraph n).mem_edgeSet.mpr hxy⟩, Finset.mem_univ _, rfl⟩

private theorem return_bottom_row_x_ge (n a k : ℕ) (ha : a ≤ n) (hk : k ≤ n)
    {z : LatticeVertex}
    (hz : z ∈ (slitBoxExteriorReturnWalkNat n a k ha hk).val.support)
    (hzy : z.2 = -(n + 1 : ℤ)) : (a : ℤ) ≤ z.1 := by
  unfold slitBoxExteriorReturnWalkNat at hz
  dsimp only at hz
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz1 | hzrest
  · obtain ⟨_, hlo, _⟩ := slitReturnVerticalUpWalk_support_bounds 0 (k : ℤ)
      (n + 1 - k) (by simpa only [SimpleGraph.Walk.support_copy] using hz1)
    have hk0 : (0 : ℤ) ≤ k := by omega
    have hnpos : (0 : ℤ) < n + 1 := by omega
    omega
  · rcases hzrest with hz2 | hzrest
    · obtain ⟨hy, _, _⟩ := slitReturnHorizontalRightWalk_support_bounds 0
        (n + 1 : ℤ) (n + 1) (by simpa [SimpleGraph.Walk.support_copy] using hz2)
      rw [hy] at hzy
      omega
    · rcases hzrest with hz3 | hzrest
      · have hx : z.1 = (n + 1 : ℤ) := by
          obtain ⟨hx, _, _⟩ := slitReturnVerticalUpWalk_support_bounds
            (n + 1 : ℤ) (-(n + 1 : ℤ)) (2 * (n + 1)) (by
              simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hz3)
          exact hx
        have ha' : (a : ℤ) ≤ n := by exact_mod_cast ha
        omega
      · rcases hzrest with hz4 | hz5
        · obtain ⟨hy, hlo, _⟩ := slitReturnHorizontalRightWalk_support_bounds
            (a : ℤ) (-(n + 1 : ℤ)) (n + 1 - a) (by
              simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hz4)
          rw [hy] at hzy
          exact hlo
        · obtain ⟨hx, _, _⟩ := slitReturnVerticalUpWalk_support_bounds
            (a : ℤ) (-(n + 1 : ℤ)) 1 (by
              simpa [SimpleGraph.Walk.support_copy] using hz5)
          exact hx.ge

private theorem candidate_bottom_row_support_x_ge
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u)
    {z : LatticeVertex}
    (hz : z ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX p).support)
    (hzy : z.2 = -(n + 1 : ℤ)) : u.val.1 ≤ z.1 := by
  classical
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  let f := bottomExteriorBaseHom n A rfl
  let t := p.val.1
  let pOpen : (openGraph (slitBoxGraph n) A).Walk u t :=
    (p.val.2 : (slitBoxGraph n).Walk u t).map f
  let mappedPath := pOpen.map (slitBoxOpenGraphToSquareLatticeHom n A)
  change z ∈ (mappedPath.append
    (slitBoxCanonicalReturnWalk n u huY huX t p.property.1)).support at hz
  have hsplit := (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz
  rcases hsplit with hpre | hret
  · have hmap : mappedPath.support = pOpen.support.map
      (slitBoxOpenGraphToSquareLatticeHom n A) :=
      SimpleGraph.Walk.support_map (f := slitBoxOpenGraphToSquareLatticeHom n A) pOpen
    rw [hmap] at hpre
    obtain ⟨v, hv, hzv⟩ := List.mem_map.mp hpre
    have hzval : v.val = z := by
      simpa [mappedPath, slitBoxOpenGraphToSquareLatticeHom] using hzv
    have hbox := v.property
    rw [mem_latticeRectangle] at hbox
    have hylo : -(n : ℤ) ≤ v.val.2 := by
      have htop : -(n : ℤ) + (2*n : ℕ) = (n : ℤ) := by push_cast; omega
      rw [htop] at hbox
      exact hbox.2.1
    have : z.2 = v.val.2 := congrArg Prod.snd hzval.symm
    omega
  · have ha : u.val.1.toNat ≤ n := by
      have hbox := u.property
      rw [mem_latticeRectangle] at hbox
      have htop : -(n : ℤ) + (2*n : ℕ) = (n : ℤ) := by push_cast; omega
      rw [htop] at hbox
      have hcast : (u.val.1.toNat : ℤ) ≤ n := by
        rw [Int.toNat_of_nonneg huX]
        exact hbox.1.2
      exact_mod_cast hcast
    have hk : t.val.2.toNat ≤ n := by
      have ht := (mem_slitBoxWiredArc_iff n t).mp p.property.1
      have hcast : (t.val.2.toNat : ℤ) ≤ n := by
        rw [Int.toNat_of_nonneg ht.2.1]
        exact ht.2.2
      exact_mod_cast hcast
    have hroute : z ∈
      (slitBoxExteriorReturnWalkNat n u.val.1.toNat t.val.2.toNat ha hk).val.support := by
      simpa [slitBoxCanonicalReturnWalk, SimpleGraph.Walk.support_copy] using hret
    have hrouteBound := return_bottom_row_x_ge n u.val.1.toNat t.val.2.toNat ha hk hroute hzy
    rw [Int.toNat_of_nonneg huX] at hrouteBound
    exact hrouteBound

/-- The cell immediately below the bottom row of a genuine candidate polygon
is exterior when its bottom endpoint lies strictly to the right of the slit. -/
theorem slitBoxFirstHitCandidate_bottom_exterior_cell
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u) :
    (0, -(n + 1 : ℤ)) ∉
      (slitBoxFirstHitCandidatePolygon n hn u huY (le_of_lt huX) p).interiorCellBases δ := by
  classical
  let P := slitBoxFirstHitCandidatePolygon n hn u huY (le_of_lt huX) p
  let cwalk := slitBoxFirstHitCandidateCycle n hn u huY (le_of_lt huX) p
  intro hz0
  have hc0 : (0, -(n + 1 : ℤ)) ∈ P.interiorCellBases δ := hz0
  let row := P.interiorCellBases δ |>.filter (fun z => z.2 = -(n + 1 : ℤ))
  have hrow0 : (0, -(n + 1 : ℤ)) ∈ row := by
    have hrowY : (-(n : ℤ) - 1) = -(n + 1 : ℤ) := by omega
    simpa [row, hrowY] using hc0
  obtain ⟨c, hcRow, hcMin⟩ := row.exists_min_image (fun z : LatticeVertex => z.1)
    ⟨(0, -(n + 1 : ℤ)), hrow0⟩
  have hcF : c ∈ P.interiorCellBases δ := (Finset.mem_filter.mp hcRow).1
  have hcY : c.2 = -(n + 1 : ℤ) := (Finset.mem_filter.mp hcRow).2
  have hcxle : c.1 ≤ 0 := by
    have := hcMin (0, -(n + 1 : ℤ)) hrow0
    simp only at this
    exact this
  let west : LatticeVertex := (c.1 - 1, c.2)
  have hwestNot : west ∉ P.interiorCellBases δ := by
    intro hw
    have hwestRow : west ∈ row := Finset.mem_filter.mpr ⟨hw, by simp [west, hcY]⟩
    have hmin := hcMin west hwestRow
    simp only [west] at hmin
    omega
  let e : Medial.LatticeBond := ⟨c, Medial.LatticeAxis.vertical⟩
  have htrue : e.faceBase true = c := by simp [e, Medial.LatticeBond.faceBase]
  have hfalse : e.faceBase false = west := by
    simp [e, west, Medial.LatticeBond.faceBase]
  have htrueDom : latticeCellCenter δ (e.faceBase true) ∈ P.domain δ := by
    rw [htrue, ← P.mem_interiorCellBases_iff δ]
    exact hcF
  have hfalseDom : latticeCellCenter δ (e.faceBase false) ∉ P.domain δ := by
    rw [hfalse, ← P.mem_interiorCellBases_iff δ]
    exact hwestNot
  have hdiff : (latticeCellCenter δ (e.faceBase true) ∈ P.domain δ) ≠
      (latticeCellCenter δ (e.faceBase false) ∈ P.domain δ) := by
    intro heq
    exact hfalseDom (heq ▸ htrueDom)
  obtain ⟨i, hi⟩ := (P.cellCenters_differ_iff_boundaryBond δ e).mp hdiff
  have hcy : cwalk.IsCycle :=
    slitBoxFirstHitCandidateCycle_isCycle n hn u huY (le_of_lt huX) p
  have hedge : e.toSym2 ∈ cwalk.edges := by
    apply (latticePolygonOfCycle_edge_iff hcy e.toSym2).2
    refine ⟨i, ?_⟩
    rw [hi]
    simpa [P, slitBoxFirstHitCandidatePolygon] using P.boundaryBond_toSym2 i
  have hcSupport : c ∈ cwalk.support := by
    have hsrc := cwalk.fst_mem_support_of_mem_edges hedge
    simpa [e, Medial.LatticeBond.toSym2, Medial.LatticeBond.source,
      Medial.LatticeBond.target] using hsrc
  have hbottom := candidate_bottom_row_support_x_ge n hn u huY
    (le_of_lt huX) p hcSupport hcY
  omega

end PottsContinuity.FKC.FiniteFK
