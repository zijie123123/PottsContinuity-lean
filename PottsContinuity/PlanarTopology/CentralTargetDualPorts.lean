module

public import PottsContinuity.PlanarTopology.CentralTargetRectangle

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC.Medial

/-- Cyclic successor in the central rectangle's exact finite index carrier. -/
theorem centralTargetRectangle_next_val (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(26*k)+2*(24*k)-3)+3)) :
    (i+1).val = if i.val+1 < 100*k then i.val+1 else 0 := by
  have : NeZero ((2*(26*k)+2*(24*k)-3)+3) := ⟨by omega⟩
  have : Fact (1 < (2*(26*k)+2*(24*k)-3)+3) := ⟨by omega⟩
  have hn : (2*(26*k)+2*(24*k)-3)+3 = 100*k := by omega
  have hi := ZMod.val_lt i
  rw [ZMod.val_add,ZMod.val_one]
  conv_lhs => arg 2; rw [hn]
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · have he : i.val+1 = 100*k := by omega
    rw [he,Nat.mod_self]

/-- Explicit normalized original boundary bonds, with the lower/left endpoint
used also on the two sides traversed backwards. -/
theorem centralTargetRectangle_boundaryBond (k : ℕ) (hk : 1 ≤ k)
    (i : ZMod ((2*(26*k)+2*(24*k)-3)+3)) :
    (centralTargetRectanglePolygon k hk).boundaryBond i =
      if i.val < 14*k then ⟨(-(k : ℤ)+(i.val : ℤ),-12*(k : ℤ)),.horizontal⟩
      else if i.val < 38*k then ⟨(13*(k : ℤ),(i.val : ℤ)-26*(k : ℤ)),.vertical⟩
      else if i.val < 64*k then ⟨(51*(k : ℤ)-(i.val : ℤ)-1,12*(k : ℤ)),.horizontal⟩
      else if i.val < 88*k then ⟨(-13*(k : ℤ),76*(k : ℤ)-(i.val : ℤ)-1),.vertical⟩
      else ⟨((i.val : ℤ)-101*(k : ℤ),-12*(k : ℤ)),.horizontal⟩ := by
  have : NeZero ((2*(26*k)+2*(24*k)-3)+3) := ⟨by omega⟩
  have hi := ZMod.val_lt i
  apply LatticeBond.toSym2_injective
  rw [FKC.LatticePolygon.boundaryBond_toSym2,
    centralTargetRectangle_vertex k hk i,centralTargetRectangle_vertex k hk (i+1),
    centralTargetRectangle_next_val k hk i]
  split_ifs <;>
    simp only [LatticeBond.toSym2,LatticeBond.source,LatticeBond.target,
      Sym2.eq_iff,Prod.mk.injEq] <;>
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,true_and,and_true] <;> omega

/-- A half-integer lies in an integer-ended open interval precisely when
its integer base is in the corresponding half-open integer interval. -/
theorem int_half_between_iff (a b c : ℤ) :
    ((a : ℝ) < (c : ℝ)+1/2 ∧ (c : ℝ)+1/2 < (b : ℝ)) ↔ a ≤ c ∧ c < b := by
  constructor
  · intro h
    constructor
    · by_contra hn
      have hh : (c : ℝ)+1 ≤ (a : ℝ) := by
        exact_mod_cast (show c+1 ≤ a by omega)
      linarith
    · by_contra hn
      have hh : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast (show b ≤ c by omega)
      linarith
  · rintro ⟨h0,h1⟩
    have hh0 : (a : ℝ) ≤ (c : ℝ) := by exact_mod_cast h0
    have hh1 : (c : ℝ)+1 ≤ (b : ℝ) := by
      exact_mod_cast (show c+1 ≤ b by omega)
    constructor <;> linarith

/-- Exact interior-cell classification for the central rectangle. -/
theorem centralTargetRectangle_cell_center_iff (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) (c : FKC.LatticeVertex) :
    FKC.latticeCellCenter δ c ∈ (centralTargetRectanglePolygon k hk).domain δ ↔
      (-13*(k : ℤ) ≤ c.1 ∧ c.1 < 13*(k : ℤ)) ∧
      (-12*(k : ℤ) ≤ c.2 ∧ c.2 < 12*(k : ℤ)) := by
  rw [centralTargetRectanglePolygon_domain]
  change ((δ.val*(-13*(k : ℤ) : ℤ) < δ.val*((c.1 : ℝ)+1/2) ∧
    δ.val*((c.1 : ℝ)+1/2) < δ.val*(13*(k : ℤ) : ℤ)) ∧
    (δ.val*(-12*(k : ℤ) : ℤ) < δ.val*((c.2 : ℝ)+1/2) ∧
    δ.val*((c.2 : ℝ)+1/2) < δ.val*(12*(k : ℤ) : ℤ))) ↔ _
  simp only [mul_lt_mul_iff_right₀ δ.property,int_half_between_iff]

/-- The uniquely exterior-facing side is computed from actual Jordan cell
membership, not supplied as an orientation assumption. -/
theorem centralTargetRectangle_outsideSide (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) (i : ZMod ((2*(26*k)+2*(24*k)-3)+3)) :
    (centralTargetRectanglePolygon k hk).boundaryOutsideSide δ i =
      if i.val < 14*k then false else if i.val < 64*k then true else false := by
  let P := centralTargetRectanglePolygon k hk
  have : NeZero ((2*(26*k)+2*(24*k)-3)+3) := ⟨by omega⟩
  have hi := ZMod.val_lt i
  have hout : ¬FKC.latticeCellCenter δ
      ((P.boundaryBond i).faceBase (P.boundaryOutsideSide δ i)) ∈ P.domain δ := by
    intro hin
    exact Set.disjoint_left.mp (P.disjoint_domain_exterior δ) hin
      (P.boundaryOutsideSide_spec δ i (FKC.latticeCellCenter_mem δ _))
  change ¬FKC.latticeCellCenter δ
      (((centralTargetRectanglePolygon k hk).boundaryBond i).faceBase
        ((centralTargetRectanglePolygon k hk).boundaryOutsideSide δ i)) ∈
          (centralTargetRectanglePolygon k hk).domain δ at hout
  rw [centralTargetRectangle_cell_center_iff,centralTargetRectangle_boundaryBond] at hout
  cases hs : (centralTargetRectanglePolygon k hk).boundaryOutsideSide δ i <;>
    simp only [hs] at hout
  all_goals split_ifs at hout ⊢ <;>
    simp only [LatticeBond.faceBase] at hout <;> first | rfl | omega

/-- Literal integer face bases of all exterior boundary ports. -/
theorem centralTargetRectangle_exterior_face (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) (i : ZMod ((2*(26*k)+2*(24*k)-3)+3)) :
    ((centralTargetRectanglePolygon k hk).boundaryBond i).faceBase
        ((centralTargetRectanglePolygon k hk).boundaryOutsideSide δ i) =
      if i.val < 14*k then (-(k : ℤ)+(i.val : ℤ),-12*(k : ℤ)-1)
      else if i.val < 38*k then (13*(k : ℤ),(i.val : ℤ)-26*(k : ℤ))
      else if i.val < 64*k then (51*(k : ℤ)-(i.val : ℤ)-1,12*(k : ℤ))
      else if i.val < 88*k then (-13*(k : ℤ)-1,76*(k : ℤ)-(i.val : ℤ)-1)
      else ((i.val : ℤ)-101*(k : ℤ),-12*(k : ℤ)-1) := by
  rw [centralTargetRectangle_boundaryBond,centralTargetRectangle_outsideSide]
  split_ifs <;> simp only [LatticeBond.faceBase]; omega

/-- Literal face-base ports on the left complementary three-piece arc. -/
def centralLeftDualPorts (k : ℕ) : Set FKC.LatticeVertex :=
  {z | (z.1 = -13*(k : ℤ)-1 ∧ -12*(k : ℤ) ≤ z.2 ∧ z.2 < 12*(k : ℤ)) ∨
    ((z.2 = -12*(k : ℤ)-1 ∨ z.2 = 12*(k : ℤ)) ∧
      -13*(k : ℤ) ≤ z.1 ∧ z.1 < -(k : ℤ))}

/-- Literal face-base ports on the right complementary three-piece arc. -/
def centralRightDualPorts (k : ℕ) : Set FKC.LatticeVertex :=
  {z | (z.1 = 13*(k : ℤ) ∧ -12*(k : ℤ) ≤ z.2 ∧ z.2 < 12*(k : ℤ)) ∨
    ((z.2 = -12*(k : ℤ)-1 ∨ z.2 = 12*(k : ℤ)) ∧
      (k : ℤ) ≤ z.1 ∧ z.1 < 13*(k : ℤ))}

/-- The final exterior edge arc gives exactly the required side of the B/D
port condition (containment suffices for the existence theorem). -/
theorem centralTargetRectangle_final_faces_subset (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) :
    polygonExteriorFaces (centralTargetRectanglePolygon k hk) δ {i | 52*k ≤ i.val} ⊆
      centralLeftDualPorts k := by
  have : NeZero ((2*(26*k)+2*(24*k)-3)+3) := ⟨by omega⟩
  rintro z ⟨i,hi,rfl⟩
  have hib := ZMod.val_lt i
  change 52*k ≤ i.val at hi
  rw [centralTargetRectangle_exterior_face]
  split_ifs <;> simp only [centralLeftDualPorts,Set.mem_ofPred_eq,
    true_and,true_or,or_true] <;> omega

/-- The first complementary exterior edge arc gives the required right-hand
face-base ports, excluding both central target segments. -/
theorem centralTargetRectangle_middle_faces_subset (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh) :
    polygonExteriorFaces (centralTargetRectanglePolygon k hk) δ
        {i | 2*k ≤ i.val ∧ i.val < 50*k} ⊆ centralRightDualPorts k := by
  rintro z ⟨i,hi,rfl⟩
  change 2*k ≤ i.val ∧ i.val < 50*k at hi
  rw [centralTargetRectangle_exterior_face]
  split_ifs <;> simp only [centralRightDualPorts,Set.mem_ofPred_eq,
    true_and,true_or,or_true] <;> omega

/-- Central-target dual existence with the exact integer B/D port
coordinates, on the actual identified rectangle domain graph. Transport to
PD's equivalent finite graph/configuration representations is not part of this statement. -/
theorem centralTargetRectangle_coordinate_dual_exists (k : ℕ) (hk : 1 ≤ k)
    (δ : FKC.PositiveMesh)
    (C : FKC.FiniteFK.Configuration
      (FKC.domainLatticeGraph δ ((centralTargetRectanglePolygon k hk).domain δ)))
    (hno : ¬∃ u : FKC.DomainVertex δ ((centralTargetRectanglePolygon k hk).domain δ),
      (u.val.2 = -12*(k : ℤ) ∧ -(k : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (k : ℤ)) ∧
      ∃ v : FKC.DomainVertex δ ((centralTargetRectanglePolygon k hk).domain δ),
        (v.val.2 = 12*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ)) ∧
        FKC.FiniteFK.ActualConnected _ C u v) :
    ∃ x ∈ centralLeftDualPorts k, ∃ y ∈ centralRightDualPorts k,
      (domainClosedDualGraph C).Reachable x y := by
  obtain ⟨x,hx,y,hy,hxy⟩ := centralTargetRectangle_indexed_dual_exists k hk δ C hno
  exact ⟨x,centralTargetRectangle_final_faces_subset k hk δ hx,
    y,centralTargetRectangle_middle_faces_subset k hk δ hy,hxy⟩

end PottsContinuity.PlanarTopology
