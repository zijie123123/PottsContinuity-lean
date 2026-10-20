/- Alpha-target specialization of CentralTargetDualPorts. The generic half-cell
   interval lemma is reused; all actual boundary bonds and ports are recomputed. -/
module

public import PottsContinuity.PlanarTopology.AlphaTargetRectangle
public import PottsContinuity.PlanarTopology.CentralTargetDualPorts

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC.Medial

/-- Cyclic successor in the central rectangle's exact finite index carrier. -/
theorem alphaTargetRectangle_next_val (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(130*k)+2*(128*k)-3)+3)) :
    (i+1).val = if i.val+1 < 516*k then i.val+1 else 0 := by
  have : NeZero ((2*(130*k)+2*(128*k)-3)+3) := ⟨by omega⟩
  have : Fact (1 < (2*(130*k)+2*(128*k)-3)+3) := ⟨by omega⟩
  have hn : (2*(130*k)+2*(128*k)-3)+3 = 516*k := by omega
  have hi := ZMod.val_lt i
  rw [ZMod.val_add,ZMod.val_one]
  conv_lhs => arg 2; rw [hn]
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · have he : i.val+1 = 516*k := by omega
    rw [he,Nat.mod_self]

/-- Explicit normalized original boundary bonds, with the lower/left endpoint
used also on the two sides traversed backwards. -/
theorem alphaTargetRectangle_boundaryBond (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(130*k)+2*(128*k)-3)+3)) :
    (alphaTargetRectanglePolygon k hk).boundaryBond i =
      if i.val < 66*k then ⟨(-(k : ℤ)+(i.val : ℤ),-64*(k : ℤ)),.horizontal⟩
      else if i.val < 194*k then ⟨(65*(k : ℤ),(i.val : ℤ)-130*(k : ℤ)),.vertical⟩
      else if i.val < 324*k then ⟨(259*(k : ℤ)-(i.val : ℤ)-1,64*(k : ℤ)),.horizontal⟩
      else if i.val < 452*k then ⟨(-65*(k : ℤ),388*(k : ℤ)-(i.val : ℤ)-1),.vertical⟩
      else ⟨((i.val : ℤ)-517*(k : ℤ),-64*(k : ℤ)),.horizontal⟩ := by
  have : NeZero ((2*(130*k)+2*(128*k)-3)+3) := ⟨by omega⟩
  have hi := ZMod.val_lt i
  apply LatticeBond.toSym2_injective
  rw [FKC.LatticePolygon.boundaryBond_toSym2,
    alphaTargetRectangle_vertex k hk i,alphaTargetRectangle_vertex k hk (i+1),
    alphaTargetRectangle_next_val k hk i]
  split_ifs <;>
    simp only [LatticeBond.toSym2,LatticeBond.source,LatticeBond.target,
      Sym2.eq_iff,Prod.mk.injEq] <;>
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,true_and,and_true] <;> omega

/-- Exact interior-cell classification for the central rectangle. -/
theorem alphaTargetRectangle_cell_center_iff (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) (c : FKC.LatticeVertex) :
    FKC.latticeCellCenter δ c ∈ (alphaTargetRectanglePolygon k hk).domain δ ↔
      (-65*(k : ℤ) ≤ c.1 ∧ c.1 < 65*(k : ℤ)) ∧
      (-64*(k : ℤ) ≤ c.2 ∧ c.2 < 64*(k : ℤ)) := by
  rw [alphaTargetRectanglePolygon_domain]
  change ((δ.val*(-65*(k : ℤ) : ℤ) < δ.val*((c.1 : ℝ)+1/2) ∧
    δ.val*((c.1 : ℝ)+1/2) < δ.val*(65*(k : ℤ) : ℤ)) ∧
    (δ.val*(-64*(k : ℤ) : ℤ) < δ.val*((c.2 : ℝ)+1/2) ∧
    δ.val*((c.2 : ℝ)+1/2) < δ.val*(64*(k : ℤ) : ℤ))) ↔ _
  simp only [mul_lt_mul_iff_right₀ δ.property,int_half_between_iff]

/-- The uniquely exterior-facing side is computed from actual Jordan cell
membership, not supplied as an orientation assumption. -/
theorem alphaTargetRectangle_outsideSide (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) (i : ZMod ((2*(130*k)+2*(128*k)-3)+3)) :
    (alphaTargetRectanglePolygon k hk).boundaryOutsideSide δ i =
      if i.val < 66*k then false else if i.val < 324*k then true else false := by
  let P := alphaTargetRectanglePolygon k hk
  have : NeZero ((2*(130*k)+2*(128*k)-3)+3) := ⟨by omega⟩
  have hi := ZMod.val_lt i
  have hout : ¬FKC.latticeCellCenter δ
      ((P.boundaryBond i).faceBase (P.boundaryOutsideSide δ i)) ∈ P.domain δ := by
    intro hin
    exact Set.disjoint_left.mp (P.disjoint_domain_exterior δ) hin
      (P.boundaryOutsideSide_spec δ i (FKC.latticeCellCenter_mem δ _))
  change ¬FKC.latticeCellCenter δ
      (((alphaTargetRectanglePolygon k hk).boundaryBond i).faceBase
        ((alphaTargetRectanglePolygon k hk).boundaryOutsideSide δ i)) ∈
          (alphaTargetRectanglePolygon k hk).domain δ at hout
  rw [alphaTargetRectangle_cell_center_iff,alphaTargetRectangle_boundaryBond] at hout
  cases hs : (alphaTargetRectanglePolygon k hk).boundaryOutsideSide δ i <;>
    simp only [hs] at hout
  all_goals split_ifs at hout ⊢ <;>
    simp only [LatticeBond.faceBase] at hout <;> first | rfl | omega

/-- Literal integer face bases of all exterior boundary ports. -/
theorem alphaTargetRectangle_exterior_face (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) (i : ZMod ((2*(130*k)+2*(128*k)-3)+3)) :
    ((alphaTargetRectanglePolygon k hk).boundaryBond i).faceBase
        ((alphaTargetRectanglePolygon k hk).boundaryOutsideSide δ i) =
      if i.val < 66*k then (-(k : ℤ)+(i.val : ℤ),-64*(k : ℤ)-1)
      else if i.val < 194*k then (65*(k : ℤ),(i.val : ℤ)-130*(k : ℤ))
      else if i.val < 324*k then (259*(k : ℤ)-(i.val : ℤ)-1,64*(k : ℤ))
      else if i.val < 452*k then (-65*(k : ℤ)-1,388*(k : ℤ)-(i.val : ℤ)-1)
      else ((i.val : ℤ)-517*(k : ℤ),-64*(k : ℤ)-1) := by
  rw [alphaTargetRectangle_boundaryBond,alphaTargetRectangle_outsideSide]
  split_ifs <;> simp only [LatticeBond.faceBase]; omega

/-- Literal face-base ports on the left complementary three-piece arc. -/
def alphaLeftDualPorts (k : ℕ) : Set FKC.LatticeVertex :=
  {z | (z.1 = -65*(k : ℤ)-1 ∧ -64*(k : ℤ) ≤ z.2 ∧ z.2 < 64*(k : ℤ)) ∨
    ((z.2 = -64*(k : ℤ)-1 ∨ z.2 = 64*(k : ℤ)) ∧
      -65*(k : ℤ) ≤ z.1 ∧ z.1 < -(k : ℤ))}

/-- Literal face-base ports on the right complementary three-piece arc. -/
def alphaRightDualPorts (k : ℕ) : Set FKC.LatticeVertex :=
  {z | (z.1 = 65*(k : ℤ) ∧ -64*(k : ℤ) ≤ z.2 ∧ z.2 < 64*(k : ℤ)) ∨
    ((z.2 = -64*(k : ℤ)-1 ∨ z.2 = 64*(k : ℤ)) ∧
      (k : ℤ) ≤ z.1 ∧ z.1 < 65*(k : ℤ))}

/-- The final exterior edge arc gives exactly the required side of the B/D
port condition (containment suffices for the existence theorem). -/
theorem alphaTargetRectangle_final_faces_subset (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) :
    polygonExteriorFaces (alphaTargetRectanglePolygon k hk) δ {i | 260*k ≤ i.val} ⊆
      alphaLeftDualPorts k := by
  have : NeZero ((2*(130*k)+2*(128*k)-3)+3) := ⟨by omega⟩
  rintro z ⟨i,hi,rfl⟩
  have hib := ZMod.val_lt i
  change 260*k ≤ i.val at hi
  rw [alphaTargetRectangle_exterior_face]
  split_ifs <;> simp only [alphaLeftDualPorts,Set.mem_ofPred_eq,
    true_and,true_or,or_true] <;> omega

/-- The first complementary exterior edge arc gives the required right-hand
face-base ports, excluding both central target segments. -/
theorem alphaTargetRectangle_middle_faces_subset (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) :
    polygonExteriorFaces (alphaTargetRectanglePolygon k hk) δ
        {i | 2*k ≤ i.val ∧ i.val < 258*k} ⊆ alphaRightDualPorts k := by
  rintro z ⟨i,hi,rfl⟩
  change 2*k ≤ i.val ∧ i.val < 258*k at hi
  rw [alphaTargetRectangle_exterior_face]
  split_ifs <;> simp only [alphaRightDualPorts,Set.mem_ofPred_eq,
    true_and,true_or,or_true] <;> omega

/-- Central-target dual existence with the exact integer B/D port
coordinates, on the actual identified rectangle domain graph. Transport to
PD's equivalent finite graph/configuration representations is not part of this statement. -/
theorem alphaTargetRectangle_coordinate_dual_exists (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (C : FKC.FiniteFK.Configuration
      (FKC.domainLatticeGraph δ ((alphaTargetRectanglePolygon k hk).domain δ)))
    (hno : ¬∃ u : FKC.DomainVertex δ ((alphaTargetRectanglePolygon k hk).domain δ),
      (u.val.2 = -64*(k : ℤ) ∧ -(k : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (k : ℤ)) ∧
      ∃ v : FKC.DomainVertex δ ((alphaTargetRectanglePolygon k hk).domain δ),
        (v.val.2 = 64*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ)) ∧
        FKC.FiniteFK.ActualConnected _ C u v) :
    ∃ x ∈ alphaLeftDualPorts k, ∃ y ∈ alphaRightDualPorts k,
      (domainClosedDualGraph C).Reachable x y := by
  obtain ⟨x,hx,y,hy,hxy⟩ := alphaTargetRectangle_indexed_dual_exists k hk δ C hno
  exact ⟨x,alphaTargetRectangle_final_faces_subset k hk δ hx,
    y,alphaTargetRectangle_middle_faces_subset k hk δ hy,hxy⟩

end PottsContinuity.PlanarTopology
