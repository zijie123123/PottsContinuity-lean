module

public import PottsContinuity.Thm1.ShellBoxComparison
public import PottsContinuity.PD.FK.BoxLaw
public import PottsContinuity.PD.FK.SubgraphComparison

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

/-- The shell-graph event that every edge of `F` is open. -/
def pottsESAllOpenCylinderEvent (V : Finset (ℤ × ℤ))
    (F : Finset PD.FK.squareLattice.edgeSet) : Set (Configuration (pottsESGraph V)) :=
  {A | ∀ e ∈ F, ∀ g : (pottsESGraph V).edgeSet,
    ((pottsESEdgeEquiv V).symm g).1 = e.1 → g ∈ A}

theorem pottsESAllOpenCylinderEvent_upper (V : Finset (ℤ × ℤ))
    (F : Finset PD.FK.squareLattice.edgeSet) :
    IsUpperSet (pottsESAllOpenCylinderEvent V F) := by
  intro A B hAB hA e he g hEdge
  exact hAB (hA e he g hEdge)

theorem pottsESBoxEmbeddedEdge_original (V : Finset (ℤ × ℤ))
    (r : ℕ) (hV : latticeBox (0, 0) r ⊆ V)
    (e : (boxGraph (0, 0) r).edgeSet) :
    ((pottsESEdgeEquiv V).symm
      (embeddedEdgeEmbedding (boxGraph (0, 0) r) (pottsESGraph V)
        (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) e)).1 =
      (boxEdgeEmbedding (0, 0) r e).1 := by
  let g := embeddedEdgeEmbedding (boxGraph (0, 0) r) (pottsESGraph V)
    (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) e
  let f : PottsESVertex V → Option (ℤ × ℤ) := Option.map Subtype.val
  have hmap₁ : Sym2.map f g.1 = Sym2.map some
      (((pottsESEdgeEquiv V).symm g).1) := by
    simpa [g, f] using pottsESEdgeEquiv_map_forget V ((pottsESEdgeEquiv V).symm g)
  have hmap₂ : Sym2.map f g.1 = Sym2.map some (boxEdgeEmbedding (0, 0) r e).1 := by
    change Sym2.map f
      (embeddedEdgeEmbedding (boxGraph (0, 0) r) (pottsESGraph V)
        (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) e).1 = _
    rw [embeddedEdgeEmbedding_coe]
    change Sym2.map f (Sym2.map (pottsESBoxEmbedding V r hV) e.1) =
      Sym2.map some (Sym2.map Subtype.val e.1)
    rw [Sym2.map_map, Sym2.map_map]
    congr 1
  apply (Sym2.map.injective (Option.some_injective (ℤ × ℤ)))
  exact hmap₁.symm.trans hmap₂

theorem pottsESBoxEdge_shellWitness (V : Finset (ℤ × ℤ)) (r : ℕ)
    (hV : latticeBox (0, 0) r ⊆ V)
    (e : (boxGraph (0, 0) r).edgeSet) :
    ∃ g : (pottsESGraph V).edgeSet,
      ((pottsESEdgeEquiv V).symm g).1 = (boxEdgeEmbedding (0, 0) r e).1 := by
  refine ⟨embeddedEdgeEmbedding (boxGraph (0, 0) r) (pottsESGraph V)
    (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) e, ?_⟩
  exact pottsESBoxEmbeddedEdge_original V r hV e

theorem pottsESBoxRestriction_cylinder_iff
    (V : Finset (ℤ × ℤ)) (r : ℕ)
    (hV : latticeBox (0, 0) r ⊆ V)
    (F : Finset PD.FK.squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding (0, 0) r))
    (A : Configuration (pottsESGraph V)) :
    embeddedConfigurationRestriction (boxGraph (0, 0) r) (pottsESGraph V)
      (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) A ∈
        wiredBoxCylinderEvent (0, 0) r F ↔
      A ∈ pottsESAllOpenCylinderEvent V F := by
  constructor
  · intro hA e he g hEdge
    obtain ⟨f, hf⟩ := Set.mem_range.mp (hF e he)
    have hfOpen := hA e he f hf
    have hgEq : g = embeddedEdgeEmbedding (boxGraph (0, 0) r) (pottsESGraph V)
        (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) f := by
      apply (pottsESEdgeEquiv V).symm.injective
      apply Subtype.ext
      calc
        ((pottsESEdgeEquiv V).symm g).1 = e.1 := hEdge
        _ = (boxEdgeEmbedding (0, 0) r f).1 := congrArg Subtype.val hf.symm
        _ = ((pottsESEdgeEquiv V).symm
          (embeddedEdgeEmbedding (boxGraph (0, 0) r) (pottsESGraph V)
            (pottsESBoxEmbedding V r hV)
            (pottsESBoxEmbedding_map_le V r hV) f)).1 :=
              (pottsESBoxEmbeddedEdge_original V r hV f).symm
    have hrestrict :=
      (mem_embeddedConfigurationRestriction _ _ _ _ A f).mp hfOpen
    rw [hgEq]
    exact hrestrict
  · intro hA e he f hf
    have hEdge := pottsESBoxEmbeddedEdge_original V r hV f
    have hOpen := hA e he
      (embeddedEdgeEmbedding (boxGraph (0, 0) r) (pottsESGraph V)
        (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) f)
      (by
        calc
          ((pottsESEdgeEquiv V).symm
            (embeddedEdgeEmbedding (boxGraph (0, 0) r) (pottsESGraph V)
              (pottsESBoxEmbedding V r hV)
              (pottsESBoxEmbedding_map_le V r hV) f)).1 =
              (boxEdgeEmbedding (0, 0) r f).1 := hEdge
          _ = e.1 := congrArg Subtype.val hf)
    exact (mem_embeddedConfigurationRestriction _ _ _ _ A f).mpr hOpen

theorem pottsESWiredShell_allOpenProbability_le_wiredBox
    (V : Finset (ℤ × ℤ)) (θ : Parameters) (r : ℕ)
    (hV : latticeBox (0, 0) r ⊆ V)
    (F : Finset PD.FK.squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding (0, 0) r)) :
    (measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
      (pottsESAllOpenCylinderEvent V F)).toReal ≤
    (measure (boxGraph (0, 0) r) θ
      (BoundaryCondition.wired (boxVertexBoundary (0, 0) r))
      (wiredBoxCylinderEvent (0, 0) r F)).toReal := by
  have hevent :
      {A | embeddedConfigurationRestriction (boxGraph (0, 0) r) (pottsESGraph V)
        (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) A ∈
          wiredBoxCylinderEvent (0, 0) r F} =
        pottsESAllOpenCylinderEvent V F := by
    ext A
    exact pottsESBoxRestriction_cylinder_iff V r hV F hF A
  rw [← hevent]
  exact pottsESWiredShell_allOpen_le_wiredBox V θ r hV F

end

end PottsContinuity.Thm1
