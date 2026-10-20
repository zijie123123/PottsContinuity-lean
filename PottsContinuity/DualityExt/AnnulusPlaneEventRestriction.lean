module

public import PottsContinuity.DualityExt.AnnulusFullBoxCrossingTransfer
public import PottsContinuity.PD.RCInfinite.Cylinders

@[expose] public section

namespace PottsContinuity.DualityExt
open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.RCInfinite
open MeasureTheory Filter Topology
noncomputable section
local instance annulusSourcePlaneConfigFintype (N : ℕ) : Fintype (Configuration (annulusSourceGraph N)) := Fintype.ofFinite _
local instance annulusSourcePlaneEdgeFintype (N : ℕ) : Fintype (annulusSourceGraph N).edgeSet := Fintype.ofFinite _
def annulusSourcePlaneEmbedding (N : ℕ) :
    {v : LatticeVertex // v ∈ annulusVertexSet N} ↪ LatticeVertex where
  toFun := Subtype.val
  inj' := Subtype.val_injective
theorem annulusSourcePlaneGraph_map_le_square (N : ℕ) :
    (annulusSourceGraph N).map (annulusSourcePlaneEmbedding N) ≤ PottsContinuity.PD.FK.squareLattice := by
  intro x y hxy
  obtain ⟨u, v, huv, rfl, rfl⟩ :=
    (SimpleGraph.map_adj (annulusSourcePlaneEmbedding N) (annulusSourceGraph N) x y).mp hxy
  exact huv
def annulusSourcePlaneConfiguration (N : ℕ) (ω : LatticeConfiguration) :
    Configuration (annulusSourceGraph N) := by
  classical
  exact Finset.univ.filter fun e =>
    ω (embeddedEdgeEmbedding (annulusSourceGraph N)
      PottsContinuity.PD.FK.squareLattice
      (annulusSourcePlaneEmbedding N)
      (annulusSourcePlaneGraph_map_le_square N) e) = true
private theorem annulusSourcePlaneConfiguration_adj (N : ℕ) (ω : LatticeConfiguration)
    (x y : {v : LatticeVertex // v ∈ annulusVertexSet N}) :
    (openGraph (annulusSourceGraph N) (annulusSourcePlaneConfiguration N ω)).Adj x y ↔
      ∃ hadj : PottsContinuity.PD.FK.squareLattice.Adj x.1 y.1,
        ω ⟨s(x.1, y.1), PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mpr hadj⟩ = true := by
  rw [openGraph_adj]
  constructor
  · intro h
    rcases (Set.mem_image Subtype.val
      (↑(annulusSourcePlaneConfiguration N ω) : Set (annulusSourceGraph N).edgeSet)
      (s(x, y))).mp h with ⟨e, heC, heq⟩
    have hee : (e : Sym2 {v : LatticeVertex // v ∈ annulusVertexSet N}) ∈
        (annulusSourceGraph N).edgeSet := e.2
    rw [heq] at hee
    have hadj' : (annulusSourceGraph N).Adj x y :=
      (annulusSourceGraph N).mem_edgeSet.mp hee
    have hadj : PottsContinuity.PD.FK.squareLattice.Adj x.1 y.1 :=
      (SimpleGraph.induce_adj (G := PottsContinuity.PD.FK.squareLattice)).mp hadj'
    have hEdge : embeddedEdgeEmbedding (annulusSourceGraph N) PottsContinuity.PD.FK.squareLattice
        (annulusSourcePlaneEmbedding N) (annulusSourcePlaneGraph_map_le_square N) e =
          ⟨s(x.1, y.1), PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mpr hadj⟩ := by
      apply Subtype.ext
      change Sym2.map (annulusSourcePlaneEmbedding N) e.val = s(x.1, y.1)
      rw [heq]
      rfl
    have hstate : ω (embeddedEdgeEmbedding (annulusSourceGraph N) PottsContinuity.PD.FK.squareLattice
        (annulusSourcePlaneEmbedding N) (annulusSourcePlaneGraph_map_le_square N) e) = true := by
      simpa [annulusSourcePlaneConfiguration] using heC
    refine ⟨hadj, ?_⟩
    rw [hEdge] at hstate
    exact hstate
  · rintro ⟨hadj, hstate⟩
    let e : (annulusSourceGraph N).edgeSet :=
      ⟨s(x, y), (SimpleGraph.induce_adj (G := PottsContinuity.PD.FK.squareLattice)).mpr hadj⟩
    have heq : (e : Sym2 {v : LatticeVertex // v ∈ annulusVertexSet N}) = s(x, y) := rfl
    have hEdge : embeddedEdgeEmbedding (annulusSourceGraph N) PottsContinuity.PD.FK.squareLattice
        (annulusSourcePlaneEmbedding N) (annulusSourcePlaneGraph_map_le_square N) e =
          ⟨s(x.1, y.1), PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mpr hadj⟩ := by
      apply Subtype.ext
      change Sym2.map (annulusSourcePlaneEmbedding N) e.val = s(x.1, y.1)
      rw [heq]
      rfl
    have heC : e ∈ annulusSourcePlaneConfiguration N ω := by
      change e ∈ Finset.univ.filter fun e =>
        ω (embeddedEdgeEmbedding (annulusSourceGraph N)
          PottsContinuity.PD.FK.squareLattice
          (annulusSourcePlaneEmbedding N) (annulusSourcePlaneGraph_map_le_square N) e) = true
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hEdge] at hstate
      exact hstate
    apply (Set.mem_image Subtype.val
      (↑(annulusSourcePlaneConfiguration N ω) : Set (annulusSourceGraph N).edgeSet)
      (s(x, y))).2
    exact ⟨e, heC, heq⟩
private theorem annulusSourcePlaneOpenGraph_eq (N : ℕ) (ω : LatticeConfiguration) :
    openGraph (annulusSourceGraph N) (annulusSourcePlaneConfiguration N ω) =
      (annulusOpenGraph N ω).induce (annulusVertexSet N : Set LatticeVertex) := by
  ext x y
  rw [annulusSourcePlaneConfiguration_adj]
  rw [SimpleGraph.induce_adj]
  simp [annulusOpenGraph, PottsContinuity.PD.FK.Medial.wholePlaneOpenPrimalGraph]

private theorem annulusOpenWalk_supported_in_source (N : ℕ) (ω : LatticeConfiguration)
    {u v : LatticeVertex} (p : (annulusOpenGraph N ω).Walk u v)
    (hu : u ∈ annulusVertexSet N) :
    ∀ z ∈ p.support, z ∈ annulusVertexSet N := by
  induction p with
  | nil =>
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact hu
  | @cons u v w hadj tail ih =>
      intro z hz
      have hadjOrig : (annulusOpenGraph N ω).Adj u v := hadj
      change u ∈ annulusVertexSet N ∧ v ∈ annulusVertexSet N ∧ _ at hadj
      have hs := SimpleGraph.Walk.support_cons hadjOrig tail
      rw [hs] at hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hu
      · exact ih hadj.2.1 z hz

def annulusSourcePlaneCrossingEvent (N : ℕ) : Set LatticeConfiguration :=
  {ω | annulusSourceFullBoxCrossingEvent N
    (annulusSourcePlaneConfiguration N ω)}

theorem annulusOpenCrossing_iff_sourcePlaneRestriction
    (N : ℕ) (hN : 1 ≤ N) (ω : LatticeConfiguration) :
    annulusOpenCrossing N ω ↔ ω ∈ annulusSourcePlaneCrossingEvent N := by
  constructor
  · rintro ⟨u, v, huBox, hvOuter, hcross⟩
    have hvNotBox : v ∉ latticeBox (0, 0) N := by
      intro hvBox
      have huv := (mem_latticeBox (0, 0) u N).mp huBox
      have hvv := (mem_latticeBox (0, 0) v N).mp hvBox
      rcases Finset.mem_filter.mp hvOuter with ⟨_, hside⟩
      rcases hside with hside | hside | hside | hside <;> omega
    have huv : u ≠ v := by
      intro heq
      subst v
      exact hvNotBox huBox
    rcases hcross with ⟨p⟩
    cases p with
    | nil => exact False.elim (huv rfl)
    | @cons u x v hfirst tail =>
      have huCarrier : u ∈ annulusVertexSet N := by
        change u ∈ annulusVertexSet N ∧ _ ∧ _ at hfirst
        exact hfirst.1
      have hsupport := annulusOpenWalk_supported_in_source N ω
        (SimpleGraph.Walk.cons hfirst tail) huCarrier
      have hvCarrier := hsupport v (by simp)
      let us : {z : LatticeVertex // z ∈ annulusVertexSet N} := ⟨u, huCarrier⟩
      let vs : {z : LatticeVertex // z ∈ annulusVertexSet N} := ⟨v, hvCarrier⟩
      have pSource : ((annulusOpenGraph N ω).induce
          (annulusVertexSet N : Set LatticeVertex)).Walk us vs := by
        exact (SimpleGraph.Walk.cons hfirst tail).induce
          (annulusVertexSet N : Set LatticeVertex) hsupport
      have pActual : (openGraph (annulusSourceGraph N)
          (annulusSourcePlaneConfiguration N ω)).Walk us vs := by
        rw [annulusSourcePlaneOpenGraph_eq]
        exact pSource
      have hActual : ActualConnected (annulusSourceGraph N)
          (annulusSourcePlaneConfiguration N ω) us vs := ⟨pActual⟩
      change ω ∈ {ω | annulusSourceFullBoxCrossingEvent N
        (annulusSourcePlaneConfiguration N ω)}
      refine ⟨us, vs, ?_, ?_, hActual⟩
      · exact huBox
      · exact hvOuter
  · rintro ⟨u, v, huBox, hvOuter, hconnected⟩
    obtain ⟨p⟩ := (actualConnected_iff_walk _ _ _ _).mp hconnected
    let hom : openGraph (annulusSourceGraph N)
        (annulusSourcePlaneConfiguration N ω) →g annulusOpenGraph N ω := {
      toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        have hadj := annulusSourcePlaneConfiguration_adj N ω x y |>.mp hxy
        refine ⟨x.2, y.2, ?_⟩
        change ∃ h : PottsContinuity.PD.FK.squareLattice.Adj x.1 y.1,
          ω ⟨s(x.1, y.1), PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mpr h⟩ = true
        exact hadj
    }
    have pPlane := p.map hom
    refine ⟨u.1, v.1, huBox, hvOuter, ?_⟩
    exact ⟨pPlane⟩

local instance annulusSourcePlaneEventEdgeFintype (N : ℕ) :
    Fintype (annulusSourceGraph N).edgeSet := Fintype.ofFinite _

theorem annulusSourcePlaneCrossingEvent_isCylinder (N : ℕ) :
    IsCylinder (annulusSourcePlaneCrossingEvent N) := by
  let F := Finset.univ.map (embeddedEdgeEmbedding (annulusSourceGraph N)
    PottsContinuity.PD.FK.squareLattice
    (annulusSourcePlaneEmbedding N) (annulusSourcePlaneGraph_map_le_square N))
  refine ⟨F, ?_⟩
  intro ω η hω
  have hrestriction : annulusSourcePlaneConfiguration N ω =
      annulusSourcePlaneConfiguration N η := by
    apply Finset.ext
    intro e
    simp only [annulusSourcePlaneConfiguration, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have he : embeddedEdgeEmbedding (annulusSourceGraph N)
        PottsContinuity.PD.FK.squareLattice
        (annulusSourcePlaneEmbedding N) (annulusSourcePlaneGraph_map_le_square N) e ∈ F := by
      exact Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩
    rw [hω _ he]
  change annulusSourceFullBoxCrossingEvent N
      (annulusSourcePlaneConfiguration N ω) ↔
    annulusSourceFullBoxCrossingEvent N
      (annulusSourcePlaneConfiguration N η)
  rw [hrestriction]

theorem annulusSourcePlaneCrossingEvent_isUpperSet (N : ℕ) :
    IsUpperSet (annulusSourcePlaneCrossingEvent N) := by
  intro ω η hω hcross
  change annulusSourceFullBoxCrossingEvent N
      (annulusSourcePlaneConfiguration N ω) at hcross
  have hsub : annulusSourcePlaneConfiguration N ω ⊆
      annulusSourcePlaneConfiguration N η := by
    intro e he
    simp only [annulusSourcePlaneConfiguration, Finset.mem_filter,
      Finset.mem_univ, true_and] at he ⊢
    have hstate := hω (embeddedEdgeEmbedding (annulusSourceGraph N)
      PottsContinuity.PD.FK.squareLattice
      (annulusSourcePlaneEmbedding N) (annulusSourcePlaneGraph_map_le_square N) e)
    exact (Bool.le_iff_imp.mp hstate) he
  rcases hcross with ⟨u, v, hu, hv, hconnected⟩
  change annulusSourceFullBoxCrossingEvent N
      (annulusSourcePlaneConfiguration N η)
  exact ⟨u, v, hu, hv, actualConnected_mono hsub hconnected⟩

theorem annulusOpenCrossing_isCylinder (N : ℕ) (hN : 1 ≤ N) :
    IsCylinder {ω : LatticeConfiguration | annulusOpenCrossing N ω} := by
  have hevent : {ω : LatticeConfiguration | annulusOpenCrossing N ω} =
      annulusSourcePlaneCrossingEvent N := by
    ext ω
    exact annulusOpenCrossing_iff_sourcePlaneRestriction N hN ω
  rw [hevent]
  exact annulusSourcePlaneCrossingEvent_isCylinder N

theorem annulusOpenCrossing_isUpperSet (N : ℕ) (hN : 1 ≤ N) :
    IsUpperSet {ω : LatticeConfiguration | annulusOpenCrossing N ω} := by
  have hevent : {ω : LatticeConfiguration | annulusOpenCrossing N ω} =
      annulusSourcePlaneCrossingEvent N := by
    ext ω
    exact annulusOpenCrossing_iff_sourcePlaneRestriction N hN ω
  rw [hevent]
  exact annulusSourcePlaneCrossingEvent_isUpperSet N

end
end PottsContinuity.DualityExt
