module

public import PottsContinuity.Thm3.OuterCircuit.ResidualGraph
public import PottsContinuity.Thm3.RSW.Lemma4SourceEvents
public import PottsContinuity.Thm3.RSW.PolygonBoxBounds
public import PottsContinuity.Thm3.RSW.PolygonOuterBox
public import PottsContinuity.Exploration.FiniteEnvelopeMaxSelector

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Exploration
open PottsContinuity.FKC.Medial

noncomputable section

local instance outerCircuitClosureEdgeFintype (n : ℕ) :
    Fintype (lemma4AmbientGraph n).edgeSet := Fintype.ofFinite _

local instance outerCircuitClosureEdgeDecidableEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _

theorem outerCircuitSelectorReveal_eq_candidateOutside {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p)) :
    outerCircuitSelectorReveal C = outerCircuitOutside (outerCircuitCandidateInside p) := by
  have hmax : envelopeMaxCandidate outerCircuitSelectorValid
      outerCircuitSelectorInside C = some (.inl p) := by
    simpa [outerCircuitMaximumCandidate] using hselected
  change envelopeMaxRevealMap outerCircuitSelectorValid
    outerCircuitSelectorInside outerCircuitOutside C = _
  unfold envelopeMaxRevealMap
  rw [hmax]
  rfl

theorem outerCircuitMaximumCandidate_selected_of_outer_event {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (hC : C ∈ lemma4OuterAnnulusEvent n) :
    ∃ p : OuterCircuitPolygonCode n,
      outerCircuitMaximumCandidate C = some (.inl p) ∧
      outerCircuitCandidateValid C p := by
  obtain ⟨p, hp⟩ := (lemma4OuterAnnulusEvent_iff_candidate_exists C).mp hC
  have hsome : ∃ i : OuterCircuitSelectorIndex n,
      outerCircuitMaximumCandidate C = some i := by
    apply (envelopeMaxCandidate_exists_iff outerCircuitSelectorValid
      outerCircuitSelectorInside C).2
    exact ⟨.inl p, hp⟩
  obtain ⟨i, hi⟩ := hsome
  have hvalid := (envelopeMaxCandidate_spec outerCircuitSelectorValid
    outerCircuitSelectorInside C i hi).1
  cases i with
  | inl q => exact ⟨q, hi, hvalid⟩
  | inr S => exact False.elim hvalid

theorem outerCircuitUnrevealedEdge_faceBases_in_candidateInterior {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    (e : (lemma4AmbientGraph n).edgeSet)
    (he : e ∉ outerCircuitSelectorReveal C) :
    (outerCircuitHostEdgeBond e).faceBase true ∈
        (outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩ ∧
      (outerCircuitHostEdgeBond e).faceBase false ∈
        (outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩ := by
  have hnotOutside : e ∉ outerCircuitOutside (outerCircuitCandidateInside p) := by
    rw [outerCircuitSelectorReveal_eq_candidateOutside C p hselected] at he
    exact he
  have hboth :
      (∃ x ∈ outerCircuitCandidateInside p,
        x.val = (outerCircuitHostEdgeBond e).faceBase true) ∧
      (∃ y ∈ outerCircuitCandidateInside p,
        y.val = (outerCircuitHostEdgeBond e).faceBase false) := by
    apply Classical.not_not.mp
    intro hnotBoth
    apply hnotOutside
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa [outerCircuitOutside] using hnotBoth⟩
  rcases hboth with ⟨⟨x, hx, hval⟩, ⟨y, hy, hval'⟩⟩
  constructor
  · have hx' : x.val ∈ (outerCircuitCodePolygon p).interiorCellBases
      ⟨1, zero_lt_one⟩ := by
      simpa [outerCircuitCandidateInside] using hx
    rw [← hval]
    exact hx'
  · have hy' : y.val ∈ (outerCircuitCodePolygon p).interiorCellBases
      ⟨1, zero_lt_one⟩ := by
      simpa [outerCircuitCandidateInside] using hy
    rw [← hval']
    exact hy'

theorem outerCircuitFourCellStar_mem_iff_center
    (F : Finset FKC.LatticeVertex) (x : FKC.LatticeVertex)
    (hstar :
      ((x ∈ F) ↔ ((x.1 - 1, x.2) ∈ F)) ∧
      ((x ∈ F) ↔ ((x.1, x.2 - 1) ∈ F)) ∧
      (((x.1 - 1, x.2) ∈ F) ↔ ((x.1 - 1, x.2 - 1) ∈ F)) ∧
      (((x.1, x.2 - 1) ∈ F) ↔ ((x.1 - 1, x.2 - 1) ∈ F)))
    {y : FKC.LatticeVertex} (hy : y ∈ outerCircuitFourCellStar x) :
    (x ∈ F ↔ y ∈ F) := by
  simp only [outerCircuitFourCellStar, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact hstar.1
  · exact hstar.2.1
  · exact hstar.1.trans hstar.2.2.1

theorem outerCircuitCandidateInteriorBase_coordinate_bounds {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    (c : FKC.LatticeVertex)
    (hc : c ∈ (outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩) :
    -(14*n : ℤ) - 1 ≤ c.1 ∧ c.1 ≤ (14*n : ℤ) + 1 ∧
    -(14*n : ℤ) - 1 ≤ c.2 ∧ c.2 ≤ (14*n : ℤ) + 1 := by
  let P := outerCircuitCodePolygon p
  have hvalid : outerCircuitCandidateValid C p := by
    have h := (envelopeMaxCandidate_spec outerCircuitSelectorValid
      outerCircuitSelectorInside C (.inl p) (by
        simpa [outerCircuitMaximumCandidate] using hselected)).1
    exact h
  have hvertex : ∀ i : ZMod (p.1.val + 3),
      max |(P.vertex i).1 - (0, 0).1| |(P.vertex i).2 - (0, 0).2| ≤
        ((14*n : ℕ) : ℤ) := by
    intro i
    simpa only [Prod.fst, Prod.snd, sub_zero, Nat.cast_mul, Nat.cast_ofNat] using
      (hvalid.2.1 i).2
  have hclosure := RSW.latticePolygon_closure_subset_outer_box
    P (0, 0) (14*n) hvertex
  have hcenter : FKC.latticeCellCenter ⟨1, zero_lt_one⟩ c ∈ P.domain ⟨1, zero_lt_one⟩ :=
    (P.mem_interiorCellBases_iff ⟨1, zero_lt_one⟩ c).mp hc
  have hbox := hclosure (subset_closure hcenter)
  simp only [RSW.complexClosedBox, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_Icc, FKC.latticeCellCenter, one_mul,
    ] at hbox
  have hxlR : (-((14*n : ℕ) : ℝ) - 1) ≤ (c.1 : ℝ) := by
    linarith [hbox.1.1]
  have hxuR : (c.1 : ℝ) ≤ ((14*n : ℕ) : ℝ) + 1 := by
    linarith [hbox.1.2]
  have hylR : (-((14*n : ℕ) : ℝ) - 1) ≤ (c.2 : ℝ) := by
    linarith [hbox.2.1]
  have hyuR : (c.2 : ℝ) ≤ ((14*n : ℕ) : ℝ) + 1 := by
    linarith [hbox.2.2]
  have hxl : -(14*n : ℤ) - 1 ≤ c.1 := by exact_mod_cast hxlR
  have hxu : c.1 ≤ (14*n : ℤ) + 1 := by exact_mod_cast hxuR
  have hyl : -(14*n : ℤ) - 1 ≤ c.2 := by exact_mod_cast hylR
  have hyu : c.2 ≤ (14*n : ℤ) + 1 := by exact_mod_cast hyuR
  exact ⟨hxl, hxu, hyl, hyu⟩

theorem outerCircuitCandidateInteriorBase_mem_host {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    (hn : 1 ≤ n) (c : FKC.LatticeVertex)
    (hc : c ∈ (outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩) :
    c ∈ PD.box (56*n) := by
  rcases outerCircuitCandidateInteriorBase_coordinate_bounds C p hselected c hc with
    ⟨hxl, hxu, hyl, hyu⟩
  have hxlo : -(56*(n:ℤ)) ≤ c.1 := by omega
  have hxhi : c.1 ≤ 56*(n:ℤ) := by omega
  have hylo : -(56*(n:ℤ)) ≤ c.2 := by omega
  have hyhi : c.2 ≤ 56*(n:ℤ) := by omega
  rw [PD.box]
  simp only [Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩

theorem outerCircuitResidualVertex_closed_of_selected {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    (hn : 1 ≤ n)
    {x : OuterCircuitHostVertex n}
    (hx : outerCircuitResidualVertex C x)
    (hnotB : ¬ outerCircuitResidualBoundaryVertex C x)
    {y : OuterCircuitHostVertex n}
    (hxy : (lemma4AmbientGraph n).Adj x y) :
    ∃ z : OuterCircuitResidualVertices n C,
      z.val = y ∧
        (outerCircuitResidualGraph C).Adj ⟨x, hx⟩ z := by
  rcases hx with ⟨y₀, hxy₀⟩ | ⟨p₀, hp₀, j₀, hxj₀⟩
  · have hxy₀' : (lemma4AmbientGraph n).Adj x y₀ :=
      (outerCircuitUnrevealedAmbientGraph_adj C x y₀).mp hxy₀ |>.1
    have he₀ : (⟨s(x,y₀), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy₀'⟩ :
        (lemma4AmbientGraph n).edgeSet) ∉ outerCircuitSelectorReveal C :=
      (outerCircuitUnrevealedAmbientGraph_adj C x y₀).mp hxy₀ |>.2
    have hfaces₀ := outerCircuitUnrevealedEdge_faceBases_in_candidateInterior
      C p hselected _ he₀
    have hstar := FKC.Domains.latticeCellBoundaryGraph_isolated_vertex_four_cells_agree
      ((outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩) x.val
      (outerCircuitPolygon_no_boundary_graph_adjacency
        (outerCircuitCodePolygon p) ⟨1, zero_lt_one⟩ x.val (by
          intro i hi
          apply hnotB
          exact ⟨p, hselected, ⟨i, hi⟩⟩))
    have hstar₀ := outerCircuitHostEdgeBond_faceBases_mem_fourCellStar x y₀ hxy₀'
    have hxCenter : x.val ∈ (outerCircuitCodePolygon p).interiorCellBases
        ⟨1, zero_lt_one⟩ :=
      (outerCircuitFourCellStar_mem_iff_center
        ((outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩)
        x.val hstar hstar₀.1).mpr
        hfaces₀.1
    have hfaceTrue : (outerCircuitHostEdgeBond
        ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩).faceBase true ∈
        (outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩ :=
      outerCircuitFourCellStar_all_of_center_mem _ x.val hstar hxCenter
        (outerCircuitHostEdgeBond_faceBases_mem_fourCellStar x y hxy).1
    have hfaceFalse : (outerCircuitHostEdgeBond
        ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩).faceBase false ∈
        (outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩ :=
      outerCircuitFourCellStar_all_of_center_mem _ x.val hstar hxCenter
        (outerCircuitHostEdgeBond_faceBases_mem_fourCellStar x y hxy).2
    let e : (lemma4AmbientGraph n).edgeSet :=
      ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩
    have hnotReveal : e ∉ outerCircuitSelectorReveal C := by
      by_contra hmem
      have hout : e ∈ outerCircuitOutside (outerCircuitCandidateInside p) := by
        rw [← outerCircuitSelectorReveal_eq_candidateOutside C p hselected]
        exact hmem
      have hnotBoth := (Finset.mem_filter.mp hout).2
      change ¬ ((∃ z ∈ outerCircuitCandidateInside p,
          z.val = (outerCircuitHostEdgeBond e).faceBase true) ∧
        (∃ z ∈ outerCircuitCandidateInside p,
          z.val = (outerCircuitHostEdgeBond e).faceBase false)) at hnotBoth
      let ztrue : OuterCircuitHostVertex n :=
        ⟨(outerCircuitHostEdgeBond e).faceBase true,
          outerCircuitCandidateInteriorBase_mem_host C p hselected hn _ hfaceTrue⟩
      let zfalse : OuterCircuitHostVertex n :=
        ⟨(outerCircuitHostEdgeBond e).faceBase false,
          outerCircuitCandidateInteriorBase_mem_host C p hselected hn _ hfaceFalse⟩
      have hztrue : ztrue ∈ outerCircuitCandidateInside p := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change (outerCircuitHostEdgeBond e).faceBase true ∈
          (outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩
        exact hfaceTrue
      have hzfalse : zfalse ∈ outerCircuitCandidateInside p := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change (outerCircuitHostEdgeBond e).faceBase false ∈
          (outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩
        exact hfaceFalse
      exact hnotBoth ⟨⟨ztrue, hztrue, rfl⟩, ⟨zfalse, hzfalse, rfl⟩⟩
    have hnew : (outerCircuitUnrevealedAmbientGraph C).Adj x y :=
      (outerCircuitUnrevealedAmbientGraph_adj C x y).2 ⟨hxy, by
        simpa only [e] using hnotReveal⟩
    refine ⟨⟨y, Or.inl ⟨x, hnew.symm⟩⟩, rfl, ?_⟩
    change (outerCircuitUnrevealedAmbientGraph C).Adj x y
    exact hnew
  · apply False.elim
    apply hnotB
    exact ⟨p₀, hp₀, ⟨j₀, hxj₀⟩⟩

theorem outerCircuitResidualVertex_coordinate_bounds_of_selected {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    {x : OuterCircuitHostVertex n}
    (hx : outerCircuitResidualVertex C x)
    (hnotB : ¬ outerCircuitResidualBoundaryVertex C x) :
    -(14*n : ℤ) - 2 ≤ x.val.1 ∧ x.val.1 ≤ (14*n : ℤ) + 2 ∧
    -(14*n : ℤ) - 2 ≤ x.val.2 ∧ x.val.2 ≤ (14*n : ℤ) + 2 := by
  rcases hx with ⟨y₀, hxy₀⟩ | ⟨p₀, hp₀, j₀, hxj₀⟩
  · have hxy₀' : (lemma4AmbientGraph n).Adj x y₀ :=
      (outerCircuitUnrevealedAmbientGraph_adj C x y₀).mp hxy₀ |>.1
    have he₀ : (⟨s(x,y₀), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy₀'⟩ :
        (lemma4AmbientGraph n).edgeSet) ∉ outerCircuitSelectorReveal C :=
      (outerCircuitUnrevealedAmbientGraph_adj C x y₀).mp hxy₀ |>.2
    have hfaces₀ := outerCircuitUnrevealedEdge_faceBases_in_candidateInterior
      C p hselected _ he₀
    have hstar₀ := outerCircuitHostEdgeBond_faceBases_mem_fourCellStar x y₀ hxy₀'
    have hbase := outerCircuitCandidateInteriorBase_coordinate_bounds C p hselected _ hfaces₀.1
    have hmem := hstar₀.1
    simp only [outerCircuitFourCellStar, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have hxcoord := congrArg Prod.fst hmem
      have hycoord := congrArg Prod.snd hmem
      omega
  · exact False.elim (hnotB ⟨p₀, hp₀, ⟨j₀, hxj₀⟩⟩)

theorem outerCircuitResidualVertex_avoids_outerBoundary_of_selected {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    (hn : 1 ≤ n)
    {x : OuterCircuitHostVertex n}
    (hx : outerCircuitResidualVertex C x)
    (hnotB : ¬ outerCircuitResidualBoundaryVertex C x) :
    x ∉ (PD.FK.frozenBoundaryCondition
      (PottsContinuity.box (56*n)) 1).boundary := by
  have hcoord := outerCircuitResidualVertex_coordinate_bounds_of_selected
    C p hselected hx hnotB
  intro hboundary
  have hvertex : x.val ∈ PD.vertexBoundary (PottsContinuity.box (56*n)) := by
    change x ∈ PD.FK.frozenVertexBoundary (PottsContinuity.box (56*n)) at hboundary
    exact hboundary
  rcases hvertex with ⟨_, z, hxz, hzout⟩
  have hadj := (PD.FK.squareLattice_adj_iff x.val z).mp hxz
  have hzbox : z ∈ PottsContinuity.box (56*n) := by
    rw [PottsContinuity.box]
    simp only [Finset.mem_product, Finset.mem_Icc]
    rcases hadj with ⟨hxp | hpx, hy⟩ | ⟨hx, hyp | hpy⟩ <;>
      constructor <;> constructor <;> omega
  exact hzout hzbox

end
end PottsContinuity.OuterCircuit
