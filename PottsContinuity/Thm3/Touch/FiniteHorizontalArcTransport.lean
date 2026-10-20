module

public import PottsContinuity.Thm3.Touch.FiniteHorizontalHalfGraph

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open PottsContinuity.PD.FK
open PottsContinuity.Thm3.Prop4
open PottsContinuity.FKC
open PottsContinuity.PlanarTopology

/-- A vertex in the horizontal polygon domain has the exact bounds of its
rectangle carrier. -/
theorem horizontalLeftPolygonVertex_rectBounds (n L : ℕ)
    (hn : 1 ≤ n) (hL : 2 ≤ L) (δ : FKC.PositiveMesh)
    (v : FKC.DomainVertex δ
      ((horizontalLeftSplitPolygon n L hn (by omega)).domain δ)) :
    (-(L : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ 0) ∧
      (0 ≤ v.val.2 ∧ v.val.2 ≤ (2*n : ℤ)) := by
  have hbase : FKC.latticeEmbed δ v.val ∈ closure
      ((rectangleLatticePolygon (-(L : ℤ), 0) L (2*n)
        (by omega) (by omega)).domain δ) := by
    rw [horizontalLeftSplitPolygon_domain_eq n L hn (by omega) δ]
    exact v.property
  have hrect := (rectangleLatticePolygon_vertex_iff (-(L : ℤ), 0) L (2*n)
    (by omega) (by omega) δ v.val).mp hbase
  rcases hrect with ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩
  constructor <;> constructor <;> omega

/-- The polygon-domain vertex viewed on the finite column carrier. -/
def horizontalLeftPolygonWindowVertex (n L : ℕ)
    (hn : 1 ≤ n) (hL : 2 ≤ L) (δ : FKC.PositiveMesh)
    (v : FKC.DomainVertex δ
      ((horizontalLeftSplitPolygon n L hn (by omega)).domain δ)) :
    TiltedColumnVertex n L 0 := by
  have hb := horizontalLeftPolygonVertex_rectBounds n L hn hL δ v
  have hstrip : v.val ∈ tiltedStripVertices (2*n) 0 := by
    simp only [tiltedStripVertices, Set.mem_ofPred_eq, tiltedHeight]
    norm_num
    exact ⟨by exact_mod_cast hb.2.1, by exact_mod_cast hb.2.2⟩
  have hwidth : |v.val.1| ≤ (L : ℤ) := by
    rw [abs_le]
    constructor
    · exact hb.1.1
    · have hLZ : 0 ≤ (L : ℤ) := by exact_mod_cast (Nat.zero_le L)
      omega
  exact ⟨v.val,
    (mem_tiltedColumnWindow_iff (2*n) L 0 (by norm_num) v.val).2
      ⟨hstrip, hwidth⟩⟩

@[simp] theorem horizontalLeftPolygonWindowVertex_val (n L : ℕ)
    (hn : 1 ≤ n) (hL : 2 ≤ L) (δ : FKC.PositiveMesh)
    (v : FKC.DomainVertex δ
      ((horizontalLeftSplitPolygon n L hn (by omega)).domain δ)) :
    (horizontalLeftPolygonWindowVertex n L hn hL δ v).val = v.val := rfl

/-- Direct coordinate graph isomorphism from the polygon closure graph to
the induced left half graph. -/
def horizontalLeftPolygonDirectGraphIso (n L : ℕ)
    (hn : 1 ≤ n) (hL : 2 ≤ L) (δ : FKC.PositiveMesh) :
    FKC.domainLatticeGraph δ
        ((horizontalLeftSplitPolygon n L hn (by omega)).domain δ) ≃g
      tiltedColumnLeftHalfGraph n L 0 where
  toFun v := by
    let z := horizontalLeftPolygonWindowVertex n L hn hL δ v
    have hb := horizontalLeftPolygonVertex_rectBounds n L hn hL δ v
    exact ⟨z.val,
      (mem_tiltedColumnLeftHalfDomain n L 0 z.val).mpr
        ⟨z.property, hb.1.2⟩⟩
  invFun z := by
    have hleft := (mem_tiltedColumnLeftHalfDomain n L 0 z.val).mp z.property
    have hwindow := (mem_tiltedColumnWindow_iff (2*n) L 0 (by norm_num) z.val).mp hleft.1
    have hy := hwindow.1
    simp only [tiltedStripVertices, Set.mem_ofPred_eq, tiltedHeight] at hy
    norm_num at hy
    have hx := abs_le.mp hwindow.2
    have hbounds :
        (-(L : ℤ) ≤ z.val.1 ∧ z.val.1 ≤ 0) ∧
          (0 ≤ z.val.2 ∧ z.val.2 ≤ (2*n : ℤ)) := by
      constructor
      · exact ⟨hx.1, hleft.2⟩
      · exact ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩
    have hbase : FKC.latticeEmbed δ z.val ∈ closure
        ((rectangleLatticePolygon (-(L : ℤ), 0) L (2*n)
          (by omega) (by omega)).domain δ) := by
      apply (rectangleLatticePolygon_vertex_iff (-(L : ℤ), 0) L (2*n)
        (by omega) (by omega) δ z.val).mpr
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega
    have hdom := horizontalLeftSplitPolygon_domain_eq n L hn (by omega) δ
    rw [hdom] at hbase
    exact ⟨z.val, hbase⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro u v
    rw [FKC.domainLatticeGraph_adj_iff]
    simp only [tiltedColumnLeftHalfGraph, SimpleGraph.induce_adj,
      horizontalLeftPolygonWindowVertex_val, FKC.domainVertexEmbed]
    change PD.FK.squareLattice.Adj u.val v.val ↔
      FKC.squareLattice.Adj u.val v.val ∧
        segment ℝ (FKC.latticeEmbed δ u.val) (FKC.latticeEmbed δ v.val) ⊆
          closure ((horizontalLeftSplitPolygon n L hn (by omega)).domain δ)
    have hadjIso : FKC.squareLattice.Adj u.val v.val ↔
        PD.FK.squareLattice.Adj u.val v.val := by
      rw [FKC.squareLattice_adj_iff, PD.FK.squareLattice_adj_iff]
    constructor
    · intro hadj
      refine ⟨hadjIso.mpr hadj, ?_⟩
      have hc : Convex ℝ (closure
          ((horizontalLeftSplitPolygon n L hn (by omega)).domain δ)) := by
        rw [← horizontalLeftSplitPolygon_domain_eq n L hn (by omega) δ,
          rectangleLatticePolygon_closure (-(L : ℤ), 0) L (2*n)
            (by omega) (by omega) δ]
        exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
          ((convex_Icc _ _).linear_preimage Complex.imLm)
      exact hc.segment_subset u.property v.property
    · intro h
      exact hadjIso.mp h.1

@[simp] theorem horizontalLeftPolygonDirectGraphIso_val (n L : ℕ)
    (hn : 1 ≤ n) (hL : 2 ≤ L) (δ : FKC.PositiveMesh)
    (v : FKC.DomainVertex δ
      ((horizontalLeftSplitPolygon n L hn (by omega)).domain δ)) :
    (horizontalLeftPolygonDirectGraphIso n L hn hL δ v).val = v.val := rfl

/-- The finite-column representative of a vertex in the induced left half. -/
abbrev TiltedColumnLeftHalfVertex (n L : ℕ) :=
  {z : ℤ × ℤ // z ∈ tiltedColumnLeftHalfDomain n L 0}

def horizontalLeftHalfColumnVertex (n L : ℕ)
    (v : TiltedColumnLeftHalfVertex n L) : TiltedColumnVertex n L 0 :=
  ⟨v.val, (mem_tiltedColumnLeftHalfDomain n L 0 v.val).mp v.property |>.1⟩

@[simp] theorem horizontalLeftHalfColumnVertex_val (n L : ℕ)
    (v : TiltedColumnLeftHalfVertex n L) :
    (horizontalLeftHalfColumnVertex n L v).val = v.val := rfl

end PottsContinuity.Thm3.Touch
