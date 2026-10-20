module

public import PottsContinuity.Thm3.Easy.P5AnnulusDoubleDualActiveGeometry
public import PottsContinuity.DualityExt.AnnulusWiredBoxDMP
public import PottsContinuity.DualityExt.PositiveAnnulusPrimalPartition
public import PottsContinuity.PD.Duality.DualCylinderLaw

@[expose] public section

open PottsContinuity.PD.FK
open PottsContinuity.DualityExt
namespace PottsContinuity.DualityExt
noncomputable section

def annulusCandidateDualTranslatePlus (u : LatticeVertex) : LatticeVertex :=
  (u.1 + 1, u.2 + 1)

def annulusCandidateDualTranslateMinus (u : LatticeVertex) : LatticeVertex :=
  (u.1 - 1, u.2 - 1)

private theorem annulusCandidateDualTranslatePlus_adj (u v : LatticeVertex)
    (h : squareLattice.Adj u v) :
    squareLattice.Adj (annulusCandidateDualTranslatePlus u) (annulusCandidateDualTranslatePlus v) := by
  change PottsContinuity.PD.FK.squareLattice.Adj
    (annulusCandidateDualTranslatePlus u) (annulusCandidateDualTranslatePlus v)
  exact (squareLattice_adj_translate_iff (1, 1) u v).2 h

private theorem annulusCandidateDualTranslateMinus_adj (u v : LatticeVertex)
    (h : squareLattice.Adj u v) :
    squareLattice.Adj (annulusCandidateDualTranslateMinus u) (annulusCandidateDualTranslateMinus v) := by
  have htU : annulusCandidateDualTranslateMinus u = latticeTranslate (-1, -1) u := by
    ext <;> simp [latticeTranslate, annulusCandidateDualTranslateMinus, sub_eq_add_neg]
  have htV : annulusCandidateDualTranslateMinus v = latticeTranslate (-1, -1) v := by
    ext <;> simp [latticeTranslate, annulusCandidateDualTranslateMinus, sub_eq_add_neg]
  rw [htU, htV]
  exact (squareLattice_adj_translate_iff (-1, -1) u v).2 h

private theorem latticeRectangle_translate_iff (a c v : LatticeVertex)
    (w h : ℕ) :
    latticeTranslate a v ∈ PottsContinuity.PD.FK.latticeRectangle
      (latticeTranslate a c) w h ↔
      v ∈ PottsContinuity.PD.FK.latticeRectangle c w h := by
  rw [PottsContinuity.PD.FK.mem_latticeRectangle,
    PottsContinuity.PD.FK.mem_latticeRectangle]
  simp only [latticeTranslate]
  omega

private theorem vertexBoundary_latticeRectangle_translate_iff
    (a c v : LatticeVertex) (w h : ℕ) :
    latticeTranslate a v ∈ PottsContinuity.PD.vertexBoundary
        (PottsContinuity.PD.FK.latticeRectangle (latticeTranslate a c) w h) ↔
      v ∈ PottsContinuity.PD.vertexBoundary
        (PottsContinuity.PD.FK.latticeRectangle c w h) := by
  simp only [PottsContinuity.PD.vertexBoundary, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hv, y, hadj, hy⟩
    have hcancel : latticeTranslate a (latticeTranslate (-a) y) = y :=
      (latticeTranslationIso a).apply_symm_apply y
    refine ⟨(latticeRectangle_translate_iff a c v w h).mp hv,
      latticeTranslate (-a) y, ?_, ?_⟩
    · apply (squareLattice_adj_translate_iff a v
        (latticeTranslate (-a) y)).mp
      simpa only [hcancel] using hadj
    · intro hm
      apply hy
      simpa only [hcancel] using
        (latticeRectangle_translate_iff a c (latticeTranslate (-a) y) w h).mpr hm
  · rintro ⟨hv, y, hadj, hy⟩
    refine ⟨(latticeRectangle_translate_iff a c v w h).mpr hv,
      latticeTranslate a y, (squareLattice_adj_translate_iff a v y).mpr hadj, ?_⟩
    exact fun hm => hy ((latticeRectangle_translate_iff a c y w h).mp hm)

noncomputable def annulusCandidateDualOuterHostVertexEquiv (N : ℕ) :
    RectangleDualVertex (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1) ≃
    RectangleVertex (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N) (4 * N + 2) (4 * N + 2) := by
  refine {
    toFun := fun z => ⟨annulusCandidateDualTranslatePlus z.1, ?_⟩
    invFun := fun z => ⟨annulusCandidateDualTranslateMinus z.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have hz : z.1 ∈ PottsContinuity.PD.FK.rectangleDualExpanded
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 1) (4 * N + 1) := z.2
    change z.1 ∈ PottsContinuity.PD.FK.latticeRectangle
      ((PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N).1 - 1,
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N).2 - 1)
      (4 * N + 2) (4 * N + 2) at hz
    rw [PottsContinuity.PD.FK.mem_latticeRectangle] at hz
    change annulusCandidateDualTranslatePlus z.1 ∈ PottsContinuity.PD.FK.latticeRectangle
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N) (4 * N + 2) (4 * N + 2)
    rw [PottsContinuity.PD.FK.mem_latticeRectangle]
    dsimp [annulusCandidateDualTranslatePlus]
    simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
      annulusHostAnchor] at hz ⊢
    rcases hz with ⟨⟨hx₁,hx₂⟩,⟨hy₁,hy₂⟩⟩
    constructor <;> constructor <;> omega
  · have hz : z.1 ∈ PottsContinuity.PD.FK.latticeRectangle
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N) (4 * N + 2) (4 * N + 2) := z.2
    rw [PottsContinuity.PD.FK.mem_latticeRectangle] at hz
    change annulusCandidateDualTranslateMinus z.1 ∈ PottsContinuity.PD.FK.rectangleDualExpanded
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)
    change (z.1.1 - 1, z.1.2 - 1) ∈
      PottsContinuity.PD.FK.latticeRectangle
        ((PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N).1 - 1,
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N).2 - 1)
        (4 * N + 2) (4 * N + 2)
    rw [PottsContinuity.PD.FK.mem_latticeRectangle]
    dsimp [annulusCandidateDualTranslateMinus]
    simp only [PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
      annulusHostAnchor] at hz ⊢
    rcases hz with ⟨⟨hx₁,hx₂⟩,⟨hy₁,hy₂⟩⟩
    constructor <;> constructor <;> omega
  · intro z
    apply Subtype.ext
    apply Prod.ext <;> simp [annulusCandidateDualTranslateMinus, annulusCandidateDualTranslatePlus]
  · intro z
    apply Subtype.ext
    apply Prod.ext <;> simp [annulusCandidateDualTranslateMinus, annulusCandidateDualTranslatePlus]

theorem annulusCandidateDualOuterHostBoundary_iff (N : ℕ)
    (z : RectangleDualVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)) :
    z.1 ∈ rectangleDualBoundary
        (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
        (4 * N + 1) (4 * N + 1) ↔
      (annulusCandidateDualOuterHostVertexEquiv N z).1 ∈
        PottsContinuity.PD.vertexBoundary
          (PottsContinuity.PD.FK.latticeRectangle
            (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
            (4 * N + 2) (4 * N + 2)) := by
  have hbd := PottsContinuity.PD.Duality.rectangleDualBoundary_eq_vertexBoundary
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 1) (4 * N + 1) z.1
  have htr := vertexBoundary_latticeRectangle_translate_iff (1, 1)
    ((PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N).1 - 1,
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N).2 - 1)
    z.1 (4 * N + 2) (4 * N + 2)
  calc
    _ ↔ z.1 ∈ PottsContinuity.PD.vertexBoundary
        (rectangleDualExpanded
          (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
          (4 * N + 1) (4 * N + 1)) := hbd
    _ ↔ annulusCandidateDualTranslatePlus z.1 ∈
        PottsContinuity.PD.vertexBoundary
          (PottsContinuity.PD.FK.latticeRectangle
            (latticeTranslate (1, 1)
              ((PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N).1 - 1,
                (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N).2 - 1))
            (4 * N + 2) (4 * N + 2)) := by
          simpa [annulusCandidateDualTranslatePlus,
            PottsContinuity.PD.FK.rectangleDualExpanded,
            latticeTranslate, Nat.add_assoc] using htr.symm
    _ ↔ (annulusCandidateDualOuterHostVertexEquiv N z).1 ∈
        PottsContinuity.PD.vertexBoundary
          (PottsContinuity.PD.FK.latticeRectangle
            (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
            (4 * N + 2) (4 * N + 2)) := by
          rw [show latticeTranslate (1, 1)
            ((PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N).1 - 1,
              (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N).2 - 1) =
            PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N by
              simp [latticeTranslate,
                PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor,
                annulusHostAnchor]]
          rfl

theorem annulusCandidateDualAmbient_extraEdge_endpoints_outerBoundary
    (N : ℕ)
    (u v : RectangleDualVertex
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1))
    (hadj : (rectangleDualAmbientGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)).Adj u v)
    (hnot : ¬ (rectangleDualGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)).Adj u v) :
    (annulusCandidateDualOuterHostVertexEquiv N u).1 ∈
        PottsContinuity.PD.vertexBoundary
          (PottsContinuity.PD.FK.latticeRectangle
            (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
            (4 * N + 2) (4 * N + 2)) ∧
      (annulusCandidateDualOuterHostVertexEquiv N v).1 ∈
        PottsContinuity.PD.vertexBoundary
          (PottsContinuity.PD.FK.latticeRectangle
            (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
            (4 * N + 2) (4 * N + 2)) := by
  have hb := PottsContinuity.PD.FK.rectangleDualAmbient_extraEdge_endpoints_boundary
    (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
    (4 * N + 1) (4 * N + 1) u v hadj hnot
  exact ⟨(annulusCandidateDualOuterHostBoundary_iff N
    ⟨u.1, u.2⟩).mp hb.1,
    (annulusCandidateDualOuterHostBoundary_iff N
      ⟨v.1, v.2⟩).mp hb.2⟩

theorem annulusCandidateDualAmbientGraph_map_toOuterRectangle_eq (N : ℕ) :
    (rectangleDualAmbientGraph
      (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)).map
        (annulusCandidateDualOuterHostVertexEquiv N).toEmbedding =
      rectangleGraph (PottsContinuity.Thm3.Easy.annulusDualExpandedHostAnchor N) (4 * N + 2) (4 * N + 2) := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨x,y,hxy,rfl,rfl⟩
    apply (rectangleGraph_adj_iff _ _ _ _ _).2
    have ha := (rectangleDualAmbientGraph_adj_iff _ _ _ _ _).mp hxy
    have hb := annulusCandidateDualTranslatePlus_adj x.1 y.1 ha
    change squareLattice.Adj
      ((annulusCandidateDualOuterHostVertexEquiv N).toEmbedding x).1
      ((annulusCandidateDualOuterHostVertexEquiv N).toEmbedding y).1
    rw [show ((annulusCandidateDualOuterHostVertexEquiv N).toEmbedding x).1 =
      annulusCandidateDualTranslatePlus x.1 from rfl,
      show ((annulusCandidateDualOuterHostVertexEquiv N).toEmbedding y).1 =
      annulusCandidateDualTranslatePlus y.1 from rfl]
    exact hb
  · intro huv
    have ha := (rectangleGraph_adj_iff _ _ _ _ _).mp huv
    refine ⟨(annulusCandidateDualOuterHostVertexEquiv N).symm u,
      (annulusCandidateDualOuterHostVertexEquiv N).symm v, ?_, ?_, ?_⟩
    · apply (rectangleDualAmbientGraph_adj_iff _ _ _ _ _).2
      have hb := annulusCandidateDualTranslateMinus_adj u.1 v.1 ha
      change squareLattice.Adj
        ((annulusCandidateDualOuterHostVertexEquiv N).symm u).1
        ((annulusCandidateDualOuterHostVertexEquiv N).symm v).1
      rw [show ((annulusCandidateDualOuterHostVertexEquiv N).symm u).1 =
        annulusCandidateDualTranslateMinus u.1 from rfl,
        show ((annulusCandidateDualOuterHostVertexEquiv N).symm v).1 =
        annulusCandidateDualTranslateMinus v.1 from rfl]
      exact hb
    · simp
    · simp
end
end PottsContinuity.DualityExt
