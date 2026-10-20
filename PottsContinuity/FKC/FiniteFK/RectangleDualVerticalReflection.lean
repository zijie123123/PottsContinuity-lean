-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleDualVerticalReflection.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleFKDuality
public import PottsContinuity.FKC.FiniteFK.RectangleVerticalReflection
public import PottsContinuity.FKC.FiniteFK.RectangleFlowDimension
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

 theorem rectangleDualVerticalReflection_mem (a : LatticeVertex) (w h : ℕ)
    (z : RectangleDualVertex a w h) :
    (z.val.1, 2 * a.2 + (h : ℤ) - 1 - z.val.2) ∈ rectangleDualExpanded a w h := by
  have hz := (mem_latticeRectangle (a.1 - 1, a.2 - 1) z.val (w + 1) (h + 1)).mp z.property
  change (z.val.1, 2 * a.2 + (h : ℤ) - 1 - z.val.2) ∈
    latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1)
  rw [mem_latticeRectangle]
  refine ⟨hz.1, ?_⟩
  constructor <;> omega

/-- The true face-base reflection. The `-1` is required because dual vertices
are centered at faces rather than at primal vertices. -/
def rectangleDualVerticalReflectionVertexEquiv (a : LatticeVertex) (w h : ℕ) :
    RectangleDualVertex a w h ≃ RectangleDualVertex a w h where
  toFun z := ⟨(z.val.1, 2 * a.2 + (h : ℤ) - 1 - z.val.2),
    rectangleDualVerticalReflection_mem a w h z⟩
  invFun z := ⟨(z.val.1, 2 * a.2 + (h : ℤ) - 1 - z.val.2),
    rectangleDualVerticalReflection_mem a w h z⟩
  left_inv z := by
    apply Subtype.ext
    ext <;> simp
  right_inv z := by
    apply Subtype.ext
    ext <;> simp

@[simp] theorem rectangleDualVerticalReflectionVertexEquiv_val
    (a : LatticeVertex) (w h : ℕ) (z : RectangleDualVertex a w h) :
    (rectangleDualVerticalReflectionVertexEquiv a w h z).val =
      (z.val.1, 2 * a.2 + (h : ℤ) - 1 - z.val.2) := rfl

 def rectangleReflectPrimalBond (a : LatticeVertex) (h : ℕ)
    (b : LatticeBond) : LatticeBond :=
  match b.axis with
  | .horizontal => ⟨(b.base.1, 2 * a.2 + (h : ℤ) - b.base.2), .horizontal⟩
  | .vertical => ⟨(b.base.1, 2 * a.2 + (h : ℤ) - b.base.2 - 1), .vertical⟩

 theorem rectangleReflectPrimalBond_in_mem (a : LatticeVertex) (w h : ℕ)
    (b : RectanglePrimalBond a w h) :
    (rectangleReflectPrimalBond a h b.1).source ∈ latticeRectangle a w h ∧
      (rectangleReflectPrimalBond a h b.1).target ∈ latticeRectangle a w h := by
  rcases b with ⟨⟨⟨x,y⟩, ax⟩, hmem⟩
  cases ax
  · have hs := (mem_latticeRectangle a (x,y) w h).mp hmem.1
    have ht := (mem_latticeRectangle a (x+1,y) w h).mp hmem.2
    simp only [rectangleReflectPrimalBond, LatticeBond.source, LatticeBond.target]
    constructor <;> rw [mem_latticeRectangle] <;> constructor <;> omega
  · have hs := (mem_latticeRectangle a (x,y) w h).mp hmem.1
    have ht := (mem_latticeRectangle a (x,y+1) w h).mp hmem.2
    simp only [rectangleReflectPrimalBond, LatticeBond.source, LatticeBond.target]
    constructor <;> rw [mem_latticeRectangle] <;> constructor <;> omega

 def rectangleReflectDualBond (a : LatticeVertex) (h : ℕ)
    (d : LatticeBond) : LatticeBond :=
  match d.axis with
  | .horizontal => ⟨(d.base.1, 2 * a.2 + (h : ℤ) - 1 - d.base.2), .horizontal⟩
  | .vertical => ⟨(d.base.1, 2 * a.2 + (h : ℤ) - 2 - d.base.2), .vertical⟩

private theorem dualBond_reflection_commute (a : LatticeVertex) (h : ℕ)
    (b : LatticeBond) :
    dualBondOfPrimal (rectangleReflectPrimalBond a h b) =
      rectangleReflectDualBond a h (dualBondOfPrimal b) := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> simp [dualBondOfPrimal, rectangleReflectPrimalBond,
    rectangleReflectDualBond] <;> omega

 def rectangleDualReflectPrimalEdge (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) : rectanglePrimalEdgeCarrier a w h :=
  rectanglePrimalEdgeBondEquiv a w h |>.symm
    ⟨rectangleReflectPrimalBond a h (rectanglePrimalEdgeBond a w h e),
      rectangleReflectPrimalBond_in_mem a w h
        ⟨rectanglePrimalEdgeBond a w h e,
          rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩⟩

private theorem rectangleReflectPrimalBond_toSym2 (a : LatticeVertex) (h : ℕ)
    (b : LatticeBond) :
    (rectangleReflectPrimalBond a h b).toSym2 =
      Sym2.map (fun z : LatticeVertex => (z.1, 2 * a.2 + (h : ℤ) - z.2)) b.toSym2 := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax
  · simp [rectangleReflectPrimalBond, LatticeBond.toSym2,
      LatticeBond.source, LatticeBond.target]
  · apply Sym2.eq_iff.mpr
    right
    constructor <;> simp [rectangleReflectPrimalBond,
      LatticeBond.source, LatticeBond.target]; omega

private theorem rectangleDualReflectPrimalEdge_bond (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) :
    rectanglePrimalEdgeBond a w h (rectangleDualReflectPrimalEdge a w h e) =
      rectangleReflectPrimalBond a h (rectanglePrimalEdgeBond a w h e) := by
  let b' : RectanglePrimalBond a w h :=
    ⟨rectangleReflectPrimalBond a h (rectanglePrimalEdgeBond a w h e),
      rectangleReflectPrimalBond_in_mem a w h
        ⟨rectanglePrimalEdgeBond a w h e,
          rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩⟩
  have heq := congrArg Subtype.val
    ((rectanglePrimalEdgeBondEquiv a w h).apply_symm_apply b')
  change rectanglePrimalEdgeBond a w h (rectangleDualReflectPrimalEdge a w h e) = _
  exact heq

 def rectangleDualReflectEdge (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) : RectangleDualEdgeCarrier a w h :=
  rectanglePrimalDualEdgeEquiv a w h
    (rectangleDualReflectPrimalEdge a w h e.primalEdge)

private theorem rectangleDualReflectPrimalEdge_eq_iso (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet) :
    rectangleDualReflectPrimalEdge a w h (e : rectanglePrimalEdgeCarrier a w h) =
      (configurationIsoEdgeEquiv (rectangleGraphVerticalReflectionIso a w h) e :
        rectanglePrimalEdgeCarrier a w h) := by
  let ec : rectanglePrimalEdgeCarrier a w h := e
  let em : rectanglePrimalEdgeCarrier a w h :=
    configurationIsoEdgeEquiv (rectangleGraphVerticalReflectionIso a w h) e
  apply (rectanglePrimalEdgeBondEquiv a w h).injective
  apply Subtype.ext
  apply LatticeBond.toSym2_injective
  change (rectanglePrimalEdgeBond a w h (rectangleDualReflectPrimalEdge a w h ec)).toSym2 =
    (rectanglePrimalEdgeBond a w h em).toSym2
  rw [rectangleDualReflectPrimalEdge_bond, rectangleReflectPrimalBond_toSym2]
  rw [rectanglePrimalEdgeBond_toSym2_public a w h ec]
  rw [rectanglePrimalEdgeBond_toSym2_public a w h em]
  dsimp [em, configurationIsoEdgeEquiv, SimpleGraph.Iso.mapEdgeSet,
    SimpleGraph.Hom.mapEdgeSet]
  rw [Sym2.map_map]
  change Sym2.map
      ((fun z : LatticeVertex => (z.1, 2 * a.2 + (h : ℤ) - z.2)) ∘
        (fun z : RectangleVertex a w h => z.val)) e.1 =
    Sym2.map (fun z : RectangleVertex a w h => z.val)
      (Sym2.map (rectangleVerticalReflectionVertexEquiv a w h) e.1)
  simp [Sym2.map_map, Function.comp_def, rectangleVerticalReflectionVertexEquiv_val]

private theorem rectangleDualVerticalReflectionEdge_crossing (a : LatticeVertex)
    (w h : ℕ) (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDualReflectEdge a w h e).crossingBond =
      rectangleReflectDualBond a h e.crossingBond := by
  rcases e with ⟨pe, d, hd⟩
  subst d
  change dualBondOfPrimal (rectanglePrimalEdgeBond a w h
      (rectangleDualReflectPrimalEdge a w h pe)) =
    rectangleReflectDualBond a h (dualBondOfPrimal (rectanglePrimalEdgeBond a w h pe))
  have hbond : rectanglePrimalEdgeBond a w h
      (rectangleDualReflectPrimalEdge a w h pe) =
      rectangleReflectPrimalBond a h (rectanglePrimalEdgeBond a w h pe) := by
    let b' : RectanglePrimalBond a w h :=
      ⟨rectangleReflectPrimalBond a h (rectanglePrimalEdgeBond a w h pe),
        rectangleReflectPrimalBond_in_mem a w h
          ⟨rectanglePrimalEdgeBond a w h pe,
            rectanglePrimalEdgeBond_endpoints_mem_public a w h pe⟩⟩
    have heq := congrArg Subtype.val
      ((rectanglePrimalEdgeBondEquiv a w h).apply_symm_apply b')
    change rectanglePrimalEdgeBond a w h (rectangleDualReflectPrimalEdge a w h pe) = _
    exact heq
  rw [hbond, dualBond_reflection_commute]

private theorem rectangleDualReflectEdge_pair (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    s((rectangleDualVerticalReflectionVertexEquiv a w h)
        (rectangleDualEdgeSource a w h e),
      (rectangleDualVerticalReflectionVertexEquiv a w h)
        (rectangleDualEdgeTarget a w h e)) =
      rectangleDualCarrierPair a w h (rectangleDualReflectEdge a w h e) := by
  apply Sym2.eq_iff.mpr
  rcases e with ⟨pe, ⟨⟨x,y⟩, ax⟩, hc⟩
  cases ax
  · left
    constructor <;> apply Subtype.ext <;>
      simp [rectangleDualVerticalReflectionVertexEquiv_val,
        rectangleDualEdgeSource_val, rectangleDualEdgeTarget_val,
        rectangleDualVerticalReflectionEdge_crossing, rectangleReflectDualBond,
        LatticeBond.source, LatticeBond.target]
  · right
    constructor <;> apply Subtype.ext <;>
      simp [rectangleDualVerticalReflectionVertexEquiv_val,
        rectangleDualEdgeSource_val, rectangleDualEdgeTarget_val,
        rectangleDualVerticalReflectionEdge_crossing, rectangleReflectDualBond,
        LatticeBond.source, LatticeBond.target] <;> omega

def rectangleDualGraphVerticalReflectionIso (a : LatticeVertex) (w h : ℕ) :
    rectangleDualGraph a w h ≃g rectangleDualGraph a w h where
  toEquiv := rectangleDualVerticalReflectionVertexEquiv a w h
  map_rel_iff' := by
    intro u v
    rw [rectangleDualGraph_adj_iff, rectangleDualGraph_adj_iff]
    constructor
    · rintro ⟨e, he⟩
      refine ⟨rectangleDualReflectEdge a w h e, ?_⟩
      have hm := congrArg (Sym2.map (rectangleDualVerticalReflectionVertexEquiv a w h)) he
      simp only [rectangleDualCarrierPair, Sym2.map_mk] at hm
      rw [rectangleDualReflectEdge_pair] at hm
      have hu : rectangleDualVerticalReflectionVertexEquiv a w h
          (rectangleDualVerticalReflectionVertexEquiv a w h u) = u :=
        (rectangleDualVerticalReflectionVertexEquiv a w h).left_inv u
      have hv : rectangleDualVerticalReflectionVertexEquiv a w h
          (rectangleDualVerticalReflectionVertexEquiv a w h v) = v :=
        (rectangleDualVerticalReflectionVertexEquiv a w h).left_inv v
      rw [hu, hv] at hm
      exact hm
    · intro he
      rcases he with ⟨e, he⟩
      refine ⟨rectangleDualReflectEdge a w h e, ?_⟩
      have hm := congrArg (Sym2.map (rectangleDualVerticalReflectionVertexEquiv a w h)) he
      simp only [rectangleDualCarrierPair, Sym2.map_mk] at hm
      rw [rectangleDualReflectEdge_pair] at hm
      exact hm

private theorem rectangleDualGraphEdgeEquiv_reflection (a : LatticeVertex)
    (w h : ℕ) (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualGraphEdgeEquiv a w h (rectangleDualReflectEdge a w h e) =
      configurationIsoEdgeEquiv (rectangleDualGraphVerticalReflectionIso a w h)
        (rectangleDualGraphEdgeEquiv a w h e) := by
  apply Subtype.ext
  change rectangleDualCarrierPair a w h (rectangleDualReflectEdge a w h e) =
    Sym2.map (rectangleDualVerticalReflectionVertexEquiv a w h)
      (rectangleDualCarrierPair a w h e)
  rw [← rectangleDualReflectEdge_pair]
  simp [rectangleDualCarrierPair]

theorem rectanglePrimalDualConfiguration_reflection_commute
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h)) :
    configurationIso (rectangleDualGraphVerticalReflectionIso a w h)
        (rectanglePrimalDualConfigurationEquiv a w h A) =
      rectanglePrimalDualConfigurationEquiv a w h
        (configurationIso (rectangleGraphVerticalReflectionIso a w h) A) := by
  classical
  let A₀ : Finset (rectanglePrimalEdgeCarrier a w h) := by
    exact A
  let A₁ : Finset (rectanglePrimalEdgeCarrier a w h) := by
    exact configurationIso (rectangleGraphVerticalReflectionIso a w h) A
  apply Finset.ext
  intro d
  let E := (rectangleDualGraphEdgeEquiv a w h).trans
    (configurationIsoEdgeEquiv (rectangleDualGraphVerticalReflectionIso a w h))
  obtain ⟨e, rfl⟩ := E.surjective d
  rw [rectanglePrimalDualConfigurationEquiv_apply,
    rectanglePrimalDualConfigurationEquiv_apply]
  change configurationIsoEdgeEquiv
      (rectangleDualGraphVerticalReflectionIso a w h)
        (rectangleDualGraphEdgeEquiv a w h e) ∈
      Finset.map (configurationIsoEdgeEquiv
        (rectangleDualGraphVerticalReflectionIso a w h)).toEmbedding
        (rectangleDualConfiguration a w h A₀) ↔
    configurationIsoEdgeEquiv
      (rectangleDualGraphVerticalReflectionIso a w h)
        (rectangleDualGraphEdgeEquiv a w h e) ∈
      rectangleDualConfiguration a w h A₁
  have hmap : rectangleDualReflectPrimalEdge a w h e.primalEdge ∈ A₁ ↔
    e.primalEdge ∈ A₀ := by
    rw [rectangleDualReflectPrimalEdge_eq_iso a w h e.primalEdge]
    change (configurationIsoEdgeEquiv (rectangleGraphVerticalReflectionIso a w h)
        e.primalEdge) ∈ Finset.map
          (configurationIsoEdgeEquiv (rectangleGraphVerticalReflectionIso a w h)).toEmbedding A₀ ↔
      e.primalEdge ∈ A₀
    rw [Finset.mem_map]
    constructor
    · rintro ⟨x, hx, hxeq⟩
      have hx' : x = e.primalEdge :=
        (configurationIsoEdgeEquiv
          (rectangleGraphVerticalReflectionIso a w h)).injective hxeq
      subst x
      exact hx
    · intro hx
      exact ⟨e.primalEdge, hx, rfl⟩
  have hleft : configurationIsoEdgeEquiv
      (rectangleDualGraphVerticalReflectionIso a w h)
        (rectangleDualGraphEdgeEquiv a w h e) ∈
      Finset.map (configurationIsoEdgeEquiv
        (rectangleDualGraphVerticalReflectionIso a w h)).toEmbedding
        (rectangleDualConfiguration a w h A₀) ↔
    rectangleDualGraphEdgeEquiv a w h e ∈ rectangleDualConfiguration a w h A₀ := by
    rw [Finset.mem_map]
    constructor
    · rintro ⟨x, hx, hxeq⟩
      have hx' : x = rectangleDualGraphEdgeEquiv a w h e :=
        (configurationIsoEdgeEquiv
          (rectangleDualGraphVerticalReflectionIso a w h)).injective hxeq
      simpa [hx'] using hx
    · intro hx
      exact ⟨rectangleDualGraphEdgeEquiv a w h e, hx, rfl⟩
  rw [hleft, ← rectangleDualGraphEdgeEquiv_reflection,
    mem_rectangleDualConfiguration, mem_rectangleDualConfiguration]
  exact (not_congr hmap).symm

end
end PottsContinuity.FKC.FiniteFK
