module

public import PottsContinuity.DualityExt.PositiveP5aAnnulusActualDualJordan
public import PottsContinuity.DualityExt.PositiveAnnulusPrimalDMP
public import PottsContinuity.PD.RCInfinite.BoxConnector
public import PottsContinuity.FKC.Domains.LatticePolygonInteriorNeighbor

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.FKC
open PottsContinuity.FKC.LatticePolygon
open OAI.SLEExactGauge

noncomputable section

private theorem p5a_polygon_vertex_not_mem_box
    {m : ℕ} (P : PottsContinuity.FKC.LatticePolygon m) (N : ℕ)
    (hN : 2 ≤ N)
    (hvertex : ∀ i : ZMod (m + 3),
      P.vertex i ∈ PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
    (i : ZMod (m + 3)) :
    P.vertex i ∉ PottsContinuity.FKC.latticeBox (0, 0) N := by
  have hi := hvertex i
  simp only [PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet,
    Finset.mem_sdiff] at hi
  rw [Nat.sub_add_cancel (by omega : 1 ≤ N)] at hi
  intro hbox
  have hcoordinates :=
    (PottsContinuity.FKC.mem_latticeBox (0, 0) (P.vertex i) N).mp hbox
  apply hi.2
  exact (PottsContinuity.Foundations.mem_box_iff_interval N
    (P.vertex i)).2 (by simpa using hcoordinates)

def p5aVertexBoxEmbedding (N : ℕ) :
    PottsContinuity.PD.FK.BoxVertex (0, 0) N → BoxVertex (0, 0) N :=
  fun z => ⟨z.val, by
    simpa only [PottsContinuity.PD.FK.BoxVertex,
      PottsContinuity.FKC.BoxVertex,
      PottsContinuity.PD.FK.latticeBox,
      PottsContinuity.FKC.latticeBox] using z.property⟩

def p5aBoxGraphHom (N : ℕ) :
    PottsContinuity.PD.FK.boxGraph (0, 0) N →g
      PottsContinuity.FKC.boxGraph (0, 0) N where
  toFun := p5aVertexBoxEmbedding N
  map_rel' := by
    intro a b hab
    rw [PottsContinuity.FKC.boxGraph_adj_iff]
    change PottsContinuity.FKC.squareLattice.Adj a.val b.val
    exact (PottsContinuity.FKC.squareLattice_adj_iff _ _).mpr
      ((PottsContinuity.PD.FK.squareLattice_adj_iff _ _).mp
        ((PottsContinuity.PD.FK.boxGraph_adj_iff (0, 0) N a b).mp hab))

/-- The polygon interior contains every primal vertex in the box enclosed by
its face-shell vertices. -/
theorem p5a_polygon_domain_contains_vertexBox
    {m : ℕ} (P : PottsContinuity.FKC.LatticePolygon m) (N : ℕ)
    (hN : 2 ≤ N)
    (hvertex : ∀ i : ZMod (m + 3),
      P.vertex i ∈ PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
    (horigin : latticeEmbed ⟨1, by norm_num⟩ (0, 0) ∈
      P.domain ⟨1, by norm_num⟩) :
    ∀ x ∈ PottsContinuity.FKC.latticeBox (0, 0) N,
      latticeEmbed ⟨1, by norm_num⟩ x ∈ P.domain ⟨1, by norm_num⟩ := by
  let δ : PottsContinuity.FKC.PositiveMesh := ⟨1, by norm_num⟩
  let G := PottsContinuity.FKC.boxGraph (0, 0) N
  have hnotCarrier (x : BoxVertex (0, 0) N) :
      PottsContinuity.FKC.latticeEmbed δ x.val ∉ P.carrier δ := by
    intro hcarrier
    obtain ⟨i, hi⟩ := (P.latticeEmbed_mem_carrier_iff δ x.val).mp hcarrier
    have houtside := p5a_polygon_vertex_not_mem_box P N hN hvertex i
    apply houtside
    rw [hi]
    exact x.property
  have hneighbor {a b : BoxVertex (0, 0) N}
      (hab : G.Adj a b) (ha : latticeEmbed δ a.val ∈ P.domain δ) :
      PottsContinuity.FKC.latticeEmbed δ b.val ∈ P.domain δ := by
    have hadjF : PottsContinuity.FKC.squareLattice.Adj a.val b.val :=
      (boxGraph_adj_iff (0, 0) N a b).mp hab
    have hclosure := P.interior_neighbor_segment_subset_closure δ hadjF ha
      (right_mem_segment ℝ (PottsContinuity.FKC.latticeEmbed δ a.val)
        (PottsContinuity.FKC.latticeEmbed δ b.val))
    rw [P.closure_domain δ] at hclosure
    rcases hclosure with hdomain | hcarrier
    · exact hdomain
    · exact False.elim (hnotCarrier b hcarrier)
  have hprop : ∀ {a b : BoxVertex (0, 0) N}, G.Walk a b →
      PottsContinuity.FKC.latticeEmbed δ a.val ∈ P.domain δ →
        PottsContinuity.FKC.latticeEmbed δ b.val ∈ P.domain δ := by
    intro a b w
    induction w with
    | nil => exact fun h => h
    | @cons a b c hab w ih =>
        intro ha
        exact ih (hneighbor hab ha)
  let u₀ : BoxVertex (0, 0) N :=
    ⟨(0, 0), PottsContinuity.FKC.center_mem_latticeBox (0, 0) N⟩
  have horigin' : PottsContinuity.FKC.latticeEmbed δ u₀.val ∈ P.domain δ := by
    simpa [u₀, δ] using horigin
  intro x hx
  let uₓ : BoxVertex (0, 0) N := ⟨x, hx⟩
  let u₀' : PottsContinuity.PD.FK.BoxVertex (0, 0) N :=
    ⟨(0, 0), PottsContinuity.PD.FK.center_mem_latticeBox (0, 0) N⟩
  let uₓ' : PottsContinuity.PD.FK.BoxVertex (0, 0) N :=
    ⟨x, by
      simpa only [PottsContinuity.PD.FK.latticeBox,
        PottsContinuity.FKC.latticeBox] using hx⟩
  have hreach :=
    (PottsContinuity.PD.RCInfinite.boxGraph_connected N).preconnected u₀' uₓ'
  have hreach' := hreach.map (p5aBoxGraphHom N)
  have he₀ : p5aBoxGraphHom N u₀' = u₀ := by
    change p5aVertexBoxEmbedding N u₀' = u₀
    apply Subtype.ext
    rfl
  have heₓ : p5aBoxGraphHom N uₓ' = uₓ := by
    change p5aVertexBoxEmbedding N uₓ' = uₓ
    apply Subtype.ext
    rfl
  rw [he₀, heₓ] at hreach'
  obtain ⟨w⟩ := hreach'
  simpa only [uₓ, δ] using hprop w horigin'

end
end PottsContinuity.DualityExt
