module

public import PottsContinuity.Thm3.OuterCircuit.RootPaths
public import PottsContinuity.Thm3.RSW.PolygonBoxBounds

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open Set

noncomputable section

/-- The closed coordinate box extended by half a cell in each direction. -/
def outerCircuitClosedHalfCellBox (c : FKC.LatticeVertex) (r : ℕ) : Set ℂ :=
  Complex.re ⁻¹' Icc ((c.1:ℝ) - (r:ℝ) - 1/2) ((c.1:ℝ) + (r:ℝ) + 1/2) ∩
    Complex.im ⁻¹' Icc ((c.2:ℝ) - (r:ℝ) - 1/2) ((c.2:ℝ) + (r:ℝ) + 1/2)

theorem outerCircuitClosedHalfCellBox_convex (c : FKC.LatticeVertex) (r : ℕ) :
    Convex ℝ (outerCircuitClosedHalfCellBox c r) := by
  exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

private theorem outerCircuitLatticeSegment_disjoint_halfCellBox
    (c u v : FKC.LatticeVertex) (r : ℕ)
    (hadj : FKC.squareLattice.Adj u v)
    (hu : (r:ℤ) < max |u.1-c.1| |u.2-c.2|)
    (hv : (r:ℤ) < max |v.1-c.1| |v.2-c.2|) :
    Disjoint (segment ℝ (FKC.latticeEmbed ⟨1,zero_lt_one⟩ u)
      (FKC.latticeEmbed ⟨1,zero_lt_one⟩ v))
      (outerCircuitClosedHalfCellBox c r) := by
  apply Set.disjoint_left.mpr
  intro z hz hbox
  change (((c.1:ℝ)-(r:ℝ)-1/2 ≤ z.re ∧ z.re ≤ (c.1:ℝ)+(r:ℝ)+1/2) ∧
    ((c.2:ℝ)-(r:ℝ)-1/2 ≤ z.im ∧ z.im ≤ (c.2:ℝ)+(r:ℝ)+1/2)) at hbox
  rcases lattice_edge_outside_box_common_side c u v r hadj hu hv with h | h | h | h
  · have huI : u.1 ≤ c.1 - (r:ℤ) - 1 := by omega
    have hvI : v.1 ≤ c.1 - (r:ℤ) - 1 := by omega
    have huR : (FKC.latticeEmbed ⟨1,zero_lt_one⟩ u).re <
        (c.1:ℝ)-(r:ℝ)-1/2 := by
      simp only [FKC.latticeEmbed_re, one_mul]
      have huRcast : (u.1:ℝ) ≤ (c.1:ℝ)-(r:ℝ)-1 := by exact_mod_cast huI
      linarith
    have hvR : (FKC.latticeEmbed ⟨1,zero_lt_one⟩ v).re <
        (c.1:ℝ)-(r:ℝ)-1/2 := by
      simp only [FKC.latticeEmbed_re, one_mul]
      have hvRcast : (v.1:ℝ) ≤ (c.1:ℝ)-(r:ℝ)-1 := by exact_mod_cast hvI
      linarith
    have hzR : z.re < (c.1:ℝ)-(r:ℝ)-1/2 :=
      ((convex_Iio ((c.1:ℝ)-(r:ℝ)-1/2)).linear_preimage Complex.reLm).segment_subset huR hvR hz
    exact (not_lt_of_ge hbox.1.1) hzR
  · have huI : c.1 + (r:ℤ) + 1 ≤ u.1 := by omega
    have hvI : c.1 + (r:ℤ) + 1 ≤ v.1 := by omega
    have huR : (c.1:ℝ)+(r:ℝ)+1/2 <
        (FKC.latticeEmbed ⟨1,zero_lt_one⟩ u).re := by
      simp only [FKC.latticeEmbed_re, one_mul]
      have huRcast : (c.1:ℝ)+(r:ℝ)+1 ≤ (u.1:ℝ) := by exact_mod_cast huI
      linarith
    have hvR : (c.1:ℝ)+(r:ℝ)+1/2 <
        (FKC.latticeEmbed ⟨1,zero_lt_one⟩ v).re := by
      simp only [FKC.latticeEmbed_re, one_mul]
      have hvRcast : (c.1:ℝ)+(r:ℝ)+1 ≤ (v.1:ℝ) := by exact_mod_cast hvI
      linarith
    have hzR : (c.1:ℝ)+(r:ℝ)+1/2 < z.re :=
      ((convex_Ioi ((c.1:ℝ)+(r:ℝ)+1/2)).linear_preimage Complex.reLm).segment_subset huR hvR hz
    exact (not_lt_of_ge hbox.1.2) hzR
  · have huI : u.2 ≤ c.2 - (r:ℤ) - 1 := by omega
    have hvI : v.2 ≤ c.2 - (r:ℤ) - 1 := by omega
    have huR : (FKC.latticeEmbed ⟨1,zero_lt_one⟩ u).im <
        (c.2:ℝ)-(r:ℝ)-1/2 := by
      simp only [FKC.latticeEmbed_im, one_mul]
      have huRcast : (u.2:ℝ) ≤ (c.2:ℝ)-(r:ℝ)-1 := by exact_mod_cast huI
      linarith
    have hvR : (FKC.latticeEmbed ⟨1,zero_lt_one⟩ v).im <
        (c.2:ℝ)-(r:ℝ)-1/2 := by
      simp only [FKC.latticeEmbed_im, one_mul]
      have hvRcast : (v.2:ℝ) ≤ (c.2:ℝ)-(r:ℝ)-1 := by exact_mod_cast hvI
      linarith
    have hzR : z.im < (c.2:ℝ)-(r:ℝ)-1/2 :=
      ((convex_Iio ((c.2:ℝ)-(r:ℝ)-1/2)).linear_preimage Complex.imLm).segment_subset huR hvR hz
    exact (not_lt_of_ge hbox.2.1) hzR
  · have huI : c.2 + (r:ℤ) + 1 ≤ u.2 := by omega
    have hvI : c.2 + (r:ℤ) + 1 ≤ v.2 := by omega
    have huR : (c.2:ℝ)+(r:ℝ)+1/2 <
        (FKC.latticeEmbed ⟨1,zero_lt_one⟩ u).im := by
      simp only [FKC.latticeEmbed_im, one_mul]
      have huRcast : (c.2:ℝ)+(r:ℝ)+1 ≤ (u.2:ℝ) := by exact_mod_cast huI
      linarith
    have hvR : (c.2:ℝ)+(r:ℝ)+1/2 <
        (FKC.latticeEmbed ⟨1,zero_lt_one⟩ v).im := by
      simp only [FKC.latticeEmbed_im, one_mul]
      have hvRcast : (c.2:ℝ)+(r:ℝ)+1 ≤ (v.2:ℝ) := by exact_mod_cast hvI
      linarith
    have hzR : (c.2:ℝ)+(r:ℝ)+1/2 < z.im :=
      ((convex_Ioi ((c.2:ℝ)+(r:ℝ)+1/2)).linear_preimage Complex.imLm).segment_subset huR hvR hz
    exact (not_lt_of_ge hbox.2.2) hzR

theorem outerCircuitPolygon_carrier_disjoint_halfCellBox {m : ℕ}
    (P : FKC.LatticePolygon m) (c : FKC.LatticeVertex) (r : ℕ)
    (hout : ∀ i : ZMod (m+3),
      (r:ℤ) < max |(P.vertex i).1-c.1| |(P.vertex i).2-c.2|) :
    Disjoint (P.carrier ⟨1,zero_lt_one⟩)
      (outerCircuitClosedHalfCellBox c r) := by
  apply Set.disjoint_left.mpr
  intro z hz hbox
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  exact Set.disjoint_left.mp
    (outerCircuitLatticeSegment_disjoint_halfCellBox c (P.vertex i)
      (P.vertex (i+1)) r (P.adjacent i) (hout i) (hout (i+1))) hi hbox

theorem outerCircuitPolygon_halfCellBox_subset_domain {m : ℕ}
    (P : FKC.LatticePolygon m) (c : FKC.LatticeVertex) (r : ℕ)
    (hcenter : FKC.latticeEmbed ⟨1,zero_lt_one⟩ c ∈ P.domain ⟨1,zero_lt_one⟩)
    (hout : ∀ i : ZMod (m+3),
      (r:ℤ) < max |(P.vertex i).1-c.1| |(P.vertex i).2-c.2|) :
    outerCircuitClosedHalfCellBox c r ⊆ P.domain ⟨1,zero_lt_one⟩ := by
  apply PlanarTopology.subset_open_of_preconnected_frontier_disjoint
    (outerCircuitClosedHalfCellBox_convex c r).isPreconnected
    (P.isJordanDomain ⟨1,zero_lt_one⟩).isOpen
  · rw [P.frontier_domain]
    exact (outerCircuitPolygon_carrier_disjoint_halfCellBox P c r hout).symm
  · refine ⟨FKC.latticeEmbed ⟨1,zero_lt_one⟩ c, ?_, hcenter⟩
    simp only [outerCircuitClosedHalfCellBox, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Icc, FKC.latticeEmbed_re,
      FKC.latticeEmbed_im, one_mul]
    constructor <;> constructor <;>
      have hr : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg _ <;> linarith

theorem outerCircuitHostEdge_faceCenters_in_halfCellBox {n : ℕ}
    (x y : OuterCircuitHostVertex n)
    (hxy : (lemma4AmbientGraph n).Adj x y)
    (hx : -(7*n:ℤ) ≤ x.val.1 ∧ x.val.1 ≤ 7*n ∧
      -(7*n:ℤ) ≤ x.val.2 ∧ x.val.2 ≤ 7*n)
    (_hy : -(7*n:ℤ) ≤ y.val.1 ∧ y.val.1 ≤ 7*n ∧
      -(7*n:ℤ) ≤ y.val.2 ∧ y.val.2 ≤ 7*n) :
    FKC.latticeCellCenter ⟨1,zero_lt_one⟩
        ((outerCircuitHostEdgeBond ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩).faceBase true) ∈
        (outerCircuitClosedHalfCellBox (0,0) (7*n)) ∧
      FKC.latticeCellCenter ⟨1,zero_lt_one⟩
        ((outerCircuitHostEdgeBond ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩).faceBase false) ∈
        (outerCircuitClosedHalfCellBox (0,0) (7*n)) := by
  have hstar := outerCircuitHostEdgeBond_faceBases_mem_fourCellStar x y hxy
  have hcenter {b : FKC.LatticeVertex}
      (hmem : b ∈ outerCircuitFourCellStar x.val) :
      FKC.latticeCellCenter ⟨1,zero_lt_one⟩ b ∈
        outerCircuitClosedHalfCellBox (0,0) (7*n) := by
    simp only [outerCircuitFourCellStar, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have hfirst := congrArg Prod.fst hmem
      have hsecond := congrArg Prod.snd hmem
      have hb1lo : -(7*n:ℤ)-1 ≤ b.1 := by omega
      have hb1hi : b.1 ≤ 7*n := by omega
      have hb2lo : -(7*n:ℤ)-1 ≤ b.2 := by omega
      have hb2hi : b.2 ≤ 7*n := by omega
      have hb1loR : -(7*(n:ℝ))-1 ≤ (b.1:ℝ) := by exact_mod_cast hb1lo
      have hb1hiR : (b.1:ℝ) ≤ 7*(n:ℝ) := by exact_mod_cast hb1hi
      have hb2loR : -(7*(n:ℝ))-1 ≤ (b.2:ℝ) := by exact_mod_cast hb2lo
      have hb2hiR : (b.2:ℝ) ≤ 7*(n:ℝ) := by exact_mod_cast hb2hi
      simp only [outerCircuitClosedHalfCellBox, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_Icc, FKC.latticeCellCenter,
        one_mul]
      constructor <;> constructor <;> push_cast <;> linarith
  exact ⟨hcenter hstar.1, hcenter hstar.2⟩

end
end PottsContinuity.OuterCircuit
