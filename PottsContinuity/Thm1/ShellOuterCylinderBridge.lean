module

public import PottsContinuity.Thm1.ShellCylinderBridge
public import PottsContinuity.PD.FK.WiredBoxLaw

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

private theorem pottsESShellAdj_endpoints (V : Finset (ℤ × ℤ))
    {x y : PottsESVertex V} (hxy : (pottsESGraph V).Adj x y) :
    ∃ a b : PottsESSite V, x = some a ∧ y = some b := by
  let edge : (pottsESGraph V).edgeSet := ⟨s(x, y), (pottsESGraph V).mem_edgeSet.mpr hxy⟩
  let e := (pottsESEdgeEquiv V).symm edge
  have hedge : ((pottsESEdgeEquiv V e).1) = s(x, y) := by
    have heq := congrArg Subtype.val (Equiv.apply_symm_apply (pottsESEdgeEquiv V) edge)
    exact heq
  have hedgeMap :
      Sym2.map (fun z : PottsESVertex V => Option.map Subtype.val z) (s(x, y)) =
        Sym2.map some e.1 := by
    calc
      Sym2.map (fun z : PottsESVertex V => Option.map Subtype.val z) (s(x, y)) =
          Sym2.map (fun z : PottsESVertex V => Option.map Subtype.val z)
            ((pottsESEdgeEquiv V e).1) := by rw [hedge]
      _ = Sym2.map some e.1 := pottsESEdgeEquiv_map_forget V e
  have hxMap : Option.map Subtype.val x ∈ Sym2.map some e.1 := by
    rw [← hedgeMap]
    simp
  have hyMap : Option.map Subtype.val y ∈ Sym2.map some e.1 := by
    rw [← hedgeMap]
    simp
  obtain ⟨a, ha, hxa⟩ := Sym2.mem_map.mp hxMap
  obtain ⟨b, hb, hyb⟩ := Sym2.mem_map.mp hyMap
  cases x with
  | none => simp at hxa
  | some x =>
    have hax : a = x.val := Option.some.inj hxa
    subst a
    cases y with
    | none => simp at hyb
    | some y =>
      have hby : b = y.val := Option.some.inj hyb
      subst b
      exact ⟨x, y, rfl, rfl⟩

private theorem pottsESShellEdge_map_forget (V : Finset (ℤ × ℤ))
    (g : (pottsESGraph V).edgeSet) :
    Sym2.map some
        (Sym2.map (fun x => (pottsESShellToBoxEmbedding V x).val) g.1) =
      Sym2.map (fun x : PottsESVertex V => Option.map Subtype.val x) g.1 := by
  induction h : g.1 using Sym2.ind with
  | _ x y =>
    have hmem : s(x, y) ∈ (pottsESGraph V).edgeSet := by
      rw [← h]
      exact g.property
    have hxy : (pottsESGraph V).Adj x y := (pottsESGraph V).mem_edgeSet.mp hmem
    obtain ⟨a, b, rfl, rfl⟩ := pottsESShellAdj_endpoints V hxy
    simp only [Sym2.map_mk, Option.map_some]
    apply Sym2.eq_iff.mpr
    exact Or.inl ⟨rfl, rfl⟩

theorem pottsESShellEmbeddedEdge_original (V : Finset (ℤ × ℤ))
    (g : (pottsESGraph V).edgeSet) :
    (boxEdgeEmbedding (0, 0) (pottsESShellComparisonRadius V)
      (embeddedEdgeEmbedding (pottsESGraph V)
        (boxGraph (0, 0) (pottsESShellComparisonRadius V))
        (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) g)).1 =
      ((pottsESEdgeEquiv V).symm g).1 := by
  let e := (pottsESEdgeEquiv V).symm g
  simp only [boxEdgeEmbedding, boxGraphEmbedding,
    SimpleGraph.Embedding.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet_coe,
    RelEmbedding.coe_toRelHom, embeddedEdgeEmbedding_coe,
    Function.Embedding.sym2Map_apply]
  rw [Sym2.map_map]
  apply Sym2.map.injective (Option.some_injective (ℤ × ℤ))
  have he : (pottsESEdgeEquiv V e).1 = g.1 :=
    congrArg Subtype.val (Equiv.apply_symm_apply (pottsESEdgeEquiv V) g)
  calc
    Sym2.map some
        (Sym2.map (fun x => (pottsESShellToBoxEmbedding V x).val) g.1) =
        Sym2.map (fun x : PottsESVertex V => Option.map Subtype.val x) g.1 :=
      pottsESShellEdge_map_forget V g
    _ = Sym2.map some e.1 := by
      rw [← he]
      exact pottsESEdgeEquiv_map_forget V e

/-- A box configuration restricts to the shell cylinder event exactly when
its open edges realize the same lattice-edge cylinder. -/
theorem pottsESShellRestriction_cylinder_iff
    (V : Finset (ℤ × ℤ))
    (F : Finset PD.FK.squareLattice.edgeSet)
    (hF : ∀ e ∈ F, ∃ g : (pottsESGraph V).edgeSet,
      ((pottsESEdgeEquiv V).symm g).1 = e.1)
    (A : Configuration (boxGraph (0, 0) (pottsESShellComparisonRadius V))) :
    embeddedConfigurationRestriction (pottsESGraph V)
      (boxGraph (0, 0) (pottsESShellComparisonRadius V))
      (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) A ∈
        pottsESAllOpenCylinderEvent V F ↔
      A ∈ wiredBoxCylinderEvent (0, 0) (pottsESShellComparisonRadius V) F := by
  constructor
  · intro hA e he f hf
    obtain ⟨g, hg⟩ := hF e he
    have hgOpen := hA e he g hg
    have hbox : boxEdgeEmbedding (0, 0) (pottsESShellComparisonRadius V)
        (embeddedEdgeEmbedding (pottsESGraph V)
          (boxGraph (0, 0) (pottsESShellComparisonRadius V))
          (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) g) = e := by
      apply Subtype.ext
      rw [pottsESShellEmbeddedEdge_original]
      exact hg
    have hfeq := (boxEdgeEmbedding (0, 0) (pottsESShellComparisonRadius V)).injective
      (hbox.trans hf.symm)
    have hrestrict :=
      (mem_embeddedConfigurationRestriction _ _ _ _ A g).mp hgOpen
    rw [← hfeq]
    exact hrestrict
  · intro hA e he g hg
    obtain ⟨g₀, hg₀⟩ := hF e he
    have heq : g = g₀ := by
      apply (pottsESEdgeEquiv V).symm.injective
      apply Subtype.ext
      exact hg.trans hg₀.symm
    have hbox : boxEdgeEmbedding (0, 0) (pottsESShellComparisonRadius V)
        (embeddedEdgeEmbedding (pottsESGraph V)
          (boxGraph (0, 0) (pottsESShellComparisonRadius V))
          (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) g₀) = e := by
      apply Subtype.ext
      rw [pottsESShellEmbeddedEdge_original]
      exact hg₀
    have hOpen := hA e he
      (embeddedEdgeEmbedding (pottsESGraph V)
        (boxGraph (0, 0) (pottsESShellComparisonRadius V))
        (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) g₀)
      hbox
    have hrestrict :=
      (mem_embeddedConfigurationRestriction _ _ _ _ A g₀).mpr hOpen
    rw [heq]
    exact hrestrict

theorem wiredBox_allOpenProbability_le_pottsESWiredShell
    (V : Finset (ℤ × ℤ)) (θ : Parameters)
    (F : Finset PD.FK.squareLattice.edgeSet)
    (hF : ∀ e ∈ F, ∃ g : (pottsESGraph V).edgeSet,
      ((pottsESEdgeEquiv V).symm g).1 = e.1) :
    (measure (boxGraph (0, 0) (pottsESShellComparisonRadius V)) θ
      (BoundaryCondition.wired
        (boxVertexBoundary (0, 0) (pottsESShellComparisonRadius V)))
      (wiredBoxCylinderEvent (0, 0) (pottsESShellComparisonRadius V) F)).toReal ≤
    (measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
      (pottsESAllOpenCylinderEvent V F)).toReal := by
  have hevent :
      {A | embeddedConfigurationRestriction (pottsESGraph V)
        (boxGraph (0, 0) (pottsESShellComparisonRadius V))
        (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) A ∈
          pottsESAllOpenCylinderEvent V F} =
        wiredBoxCylinderEvent (0, 0) (pottsESShellComparisonRadius V) F := by
    ext A
    simpa only [Set.mem_ofPred_eq] using
      pottsESShellRestriction_cylinder_iff V F hF A
  rw [← hevent]
  exact wiredBox_restriction_le_pottsESWiredShell V θ
    (pottsESAllOpenCylinderEvent V F) (pottsESAllOpenCylinderEvent_upper V F)

end

end PottsContinuity.Thm1
