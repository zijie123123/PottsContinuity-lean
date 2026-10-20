module

public import PottsContinuity.PD.FK.Lattice
public import PottsContinuity.PD.Duality.RectangleDualAmbient
public import PottsContinuity.PD.Duality.RayIndex
public import PottsContinuity.DualityExt.PositiveFreeDomainComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open MeasureTheory

/-- Integer face bases whose centers lie in the square of radius `r` about
the primal origin. The corresponding dual vertices are at `(x+1/2,y+1/2)`. -/
def dualFaceBox (r : ℕ) : Finset LatticeVertex :=
  (Finset.Icc (-(r : ℤ)) ((r : ℤ) - 1)) ×ˢ
    (Finset.Icc (-(r : ℤ)) ((r : ℤ) - 1))

lemma mem_dualFaceBox (r : ℕ) (v : LatticeVertex) :
    v ∈ dualFaceBox r ↔
      -(r : ℤ) ≤ v.1 ∧ v.1 ≤ (r : ℤ) - 1 ∧
      -(r : ℤ) ≤ v.2 ∧ v.2 ≤ (r : ℤ) - 1 := by
  unfold dualFaceBox
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
    exact ⟨hx₁, hx₂, hy₁, hy₂⟩
  · rintro ⟨hx₁, hx₂, hy₁, hy₂⟩
    exact ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩

/-- The P5a annulus on the integer lattice, before its vertices are placed at
dual face centers. -/
def p5aAnnulusVertexSet (m : ℕ) : Finset LatticeVertex :=
  latticeBox (0, 0) (2 * m) \ latticeBox (0, 0) (m + 1)

/-- The dual annulus shell for `A_N = Λ_(2N) \\ Λ_(N-1)`, recorded in face-base
coordinates. -/
def dualFaceAnnulusShell (N : ℕ) : Finset LatticeVertex :=
  dualFaceBox (2 * N) \ dualFaceBox N

/-- The half-shifted P5a annulus at scale `N-1` fits in the exact dual face
shell. This is the coordinate inclusion used by the source at `N ≥ 4`; the
bound itself only needs `N ≥ 2`. -/
theorem p5a_annulus_faceShell_fit (N : ℕ) (hN : 2 ≤ N) :
    p5aAnnulusVertexSet (N - 1) ⊆ dualFaceAnnulusShell N := by
  intro v hv
  have hv' := Finset.mem_sdiff.mp hv
  have houter := (mem_latticeBox (0, 0) v (2 * (N - 1))).mp hv'.1
  have hnotInner : v ∉ latticeBox (0, 0) N := by
    intro h
    have hscale : N - 1 + 1 = N := Nat.sub_add_cancel (by omega)
    have h' : v ∈ latticeBox (0, 0) (N - 1 + 1) := by
      simpa [hscale] using h
    exact hv'.2 h'
  have hinner : ¬ (-(N : ℤ) ≤ v.1 ∧ v.1 ≤ (N : ℤ) - 1 ∧
      -(N : ℤ) ≤ v.2 ∧ v.2 ≤ (N : ℤ) - 1) := by
    intro h
    apply hnotInner
    rw [mem_latticeBox]
    omega
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [mem_dualFaceBox]
    omega
  · intro hsmall
    exact hinner ((mem_dualFaceBox N v).mp hsmall)

/-- The finite graph of P5a bonds at scale `N-1`. Its vertices are all
annulus sites, including sites incident to no edge of a particular state. -/
def p5aAnnulusFaceGraph (N : ℕ) :
    SimpleGraph {v : LatticeVertex // v ∈ p5aAnnulusVertexSet (N - 1)} :=
  squareLattice.induce (p5aAnnulusVertexSet (N - 1) : Set LatticeVertex)

/-- The square host for the face-base carrier of the dual annulus. -/
def p5aAnnulusHostAnchor (N : ℕ) : LatticeVertex :=
  (-(2 * (N : ℤ)), -(2 * (N : ℤ)))

theorem p5a_annulus_vertex_mem_dualHost (N : ℕ) (hN : 2 ≤ N)
    {v : LatticeVertex} (hv : v ∈ p5aAnnulusVertexSet (N - 1)) :
    v ∈ rectangleDualExpanded (p5aAnnulusHostAnchor N) (4 * N) (4 * N) := by
  have hbox := (mem_latticeBox (0, 0) v (2 * (N - 1))).mp
    (Finset.mem_sdiff.mp hv).1
  rw [rectangleDualExpanded, mem_latticeRectangle]
  simp only [p5aAnnulusHostAnchor]
  rcases hbox with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  constructor <;> constructor <;> omega

theorem p5a_annulus_vertex_mem_dualHostInterior (N : ℕ) (hN : 2 ≤ N)
    {v : LatticeVertex} (hv : v ∈ p5aAnnulusVertexSet (N - 1)) :
    v ∈ rectangleDualInterior (p5aAnnulusHostAnchor N) (4 * N) (4 * N) := by
  unfold rectangleDualInterior
  apply Finset.mem_filter.mpr
  refine ⟨p5a_annulus_vertex_mem_dualHost N hN hv, ?_⟩
  have hbox := (mem_latticeBox (0, 0) v (2 * (N - 1))).mp
    (Finset.mem_sdiff.mp hv).1
  simp only [p5aAnnulusHostAnchor]
  rcases hbox with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  omega

/-- Face-base embedding of the P5a graph into the rectangle dual carrier. -/
def p5aAnnulusFaceBaseEmbedding (N : ℕ) (hN : 2 ≤ N) :
    {v : LatticeVertex // v ∈ p5aAnnulusVertexSet (N - 1)} ↪
      RectangleDualVertex (p5aAnnulusHostAnchor N) (4 * N) (4 * N) where
  toFun v := ⟨v.1, p5a_annulus_vertex_mem_dualHost N hN v.2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    change x.1 = y.1
    exact congrArg (fun z : RectangleDualVertex
      (p5aAnnulusHostAnchor N) (4 * N) (4 * N) => z.1) h

theorem p5a_annulus_faceGraph_map_le_dualHost (N : ℕ) (hN : 2 ≤ N) :
    (p5aAnnulusFaceGraph N).map (p5aAnnulusFaceBaseEmbedding N hN) ≤
      rectangleDualGraph (p5aAnnulusHostAnchor N) (4 * N) (4 * N) := by
  intro u v huv
  have hmap := SimpleGraph.map_adj (p5aAnnulusFaceBaseEmbedding N hN)
    (p5aAnnulusFaceGraph N) u v
  rcases hmap.mp huv with ⟨x, y, hxy, rfl, rfl⟩
  change squareLattice.Adj x.1 y.1 at hxy
  have hamb : (rectangleDualAmbientGraph (p5aAnnulusHostAnchor N)
      (4 * N) (4 * N)).Adj
      (p5aAnnulusFaceBaseEmbedding N hN x)
      (p5aAnnulusFaceBaseEmbedding N hN y) := by
    apply (rectangleDualAmbientGraph_adj_iff _ _ _ _ _).2
    exact hxy
  exact rectangleDualAmbient_adj_actual_of_left_interior
    (p5aAnnulusHostAnchor N) (4 * N) (4 * N)
    (p5aAnnulusFaceBaseEmbedding N hN x)
    (p5aAnnulusFaceBaseEmbedding N hN y)
    (p5a_annulus_vertex_mem_dualHostInterior N hN x.2) hamb

noncomputable section

local instance p5aAnnulusSourceFintype (N : ℕ) :
    Fintype {v : LatticeVertex // v ∈ p5aAnnulusVertexSet (N - 1)} :=
  Fintype.ofFinset _ (fun _ => Iff.rfl)

local instance p5aAnnulusHostDualFintype (N : ℕ) :
    Fintype (RectangleDualVertex (p5aAnnulusHostAnchor N) (4 * N) (4 * N)) :=
  Fintype.ofFinset _ (fun _ => Iff.rfl)

local instance p5aAnnulusSourceEdgeFintype (N : ℕ) :
    Fintype (p5aAnnulusFaceGraph N).edgeSet := Fintype.ofFinite _

local instance p5aAnnulusHostDualEdgeFintype (N : ℕ) :
    Fintype (rectangleDualGraph (p5aAnnulusHostAnchor N) (4 * N) (4 * N)).edgeSet :=
  Fintype.ofFinite _

end

end PottsContinuity.DualityExt
