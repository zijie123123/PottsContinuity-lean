module

public import PottsContinuity.PlanarTopology.RectangleGraphBridge
public import PottsContinuity.PD.Duality.RectangleDualConfiguration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- Faithful translation of normalized unit bonds between the two shared
libraries. Both axes and every integer base are preserved. -/
def pdBondOfFKC (b : FKC.Medial.LatticeBond) : PD.FK.Medial.LatticeBond :=
  ⟨b.base,match b.axis with | .horizontal => .horizontal | .vertical => .vertical⟩

@[simp] theorem pdBondOfFKC_toSym2 (b : FKC.Medial.LatticeBond) :
    (pdBondOfFKC b).toSym2 = b.toSym2 := by
  cases b with | mk base axis => cases axis <;> rfl

@[simp] theorem pdBondOfFKC_faceBase (b : FKC.Medial.LatticeBond) (s : Bool) :
    (pdBondOfFKC b).faceBase s = b.faceBase s := by
  cases b with | mk base axis => cases axis <;> cases s <;> rfl

/-- Representation identity for PD's normalized rectangle bond.
Proof follows PD/Duality/RectangleDualCarrier's private normalization lemma;
this public bridge is needed only for comparison with FKC domain bonds. -/
theorem pd_rectanglePrimalEdgeBond_toSym2 (a : FKC.LatticeVertex) (w h : ℕ)
    (e : PD.FK.rectanglePrimalEdgeCarrier a w h) :
    (PD.FK.rectanglePrimalEdgeBond a w h e).toSym2 =
      Sym2.map (fun z : PD.FK.RectangleVertex a w h => z.val) e.val := by
  have he : PD.FK.Medial.latticeBondEdge (PD.FK.rectanglePrimalEdgeBond a w h e) =
      PD.FK.rectanglePrimalEdgeToSquareEdge a w h e :=
    Equiv.apply_symm_apply PD.FK.Medial.wholePlaneBondEdgeEquiv _
  have hv := congrArg Subtype.val he
  change (PD.FK.rectanglePrimalEdgeBond a w h e).toSym2 = _ at hv
  rw [hv]
  rfl

/-- Every genuinely closed original domain bond becomes a genuinely OPEN
edge of the true PD complementary dual. The hypothesis on the isomorphism
says only that its geometric integer coordinates agree. -/
theorem domain_closed_bond_to_pd_dual {δ : FKC.PositiveMesh} {D : Set ℂ}
    (a : FKC.LatticeVertex) (w h : ℕ)
    (e : PD.FK.rectangleGraph a w h ≃g FKC.domainLatticeGraph δ D)
    (he : ∀ u, (e u).val = u.val)
    (A : PD.FK.Configuration (PD.FK.rectangleGraph a w h))
    (b : FKC.Medial.DomainBond δ D)
    (hb : b.toGraphEdge ∉ FKC.FiniteFK.configurationIso e A) :
    ∃ u v : PD.FK.RectangleDualVertex a w h,
      u.val = b.val.faceBase false ∧ v.val = b.val.faceBase true ∧
      (PD.FK.openGraph (PD.FK.rectangleDualGraph a w h)
        (PD.FK.rectangleDualConfiguration a w h A)).Adj u v := by
  classical
  have hval : ∀ z, (e.symm z).val = z.val := by
    intro z
    have hz := he (e.symm z)
    rw [e.apply_symm_apply] at hz
    exact hz.symm
  let u := e.symm b.source
  let v := e.symm b.target
  have huv : (PD.FK.rectangleGraph a w h).Adj u v :=
    e.symm.toHom.map_adj ⟨b.val.adjacent,b.property⟩
  let pe : PD.FK.rectanglePrimalEdgeCarrier a w h :=
    ⟨s(u,v),(PD.FK.rectangleGraph a w h).mem_edgeSet.mpr huv⟩
  have hedge : FKC.FiniteFK.configurationIsoEdgeEquiv e pe = b.toGraphEdge := by
    apply Subtype.ext
    change s(e u,e v) = s(b.source,b.target)
    simp only [u,v,e.apply_symm_apply]
  have hclosed : pe ∉ A := by
    intro hp
    apply hb
    change b.toGraphEdge ∈ A.map (FKC.FiniteFK.configurationIsoEdgeEquiv e).toEmbedding
    exact Finset.mem_map.mpr ⟨pe,hp,hedge⟩
  have hbond : PD.FK.rectanglePrimalEdgeBond a w h pe = pdBondOfFKC b.val := by
    apply PD.FK.Medial.LatticeBond.toSym2_injective
    rw [pd_rectanglePrimalEdgeBond_toSym2,pdBondOfFKC_toSym2]
    change s(u.val,v.val) = s(b.val.source,b.val.target)
    rw [hval b.source,hval b.target]
    rfl
  let de := PD.FK.rectanglePrimalDualEdgeEquiv a w h pe
  refine ⟨PD.FK.rectangleDualEdgeSource a w h de,PD.FK.rectangleDualEdgeTarget a w h de,
    ?_,?_,?_⟩
  · rw [PD.FK.rectangleDualEdgeSource_faceBase]
    change (PD.FK.rectanglePrimalEdgeBond a w h pe).faceBase false = _
    rw [hbond,pdBondOfFKC_faceBase]
  · rw [PD.FK.rectangleDualEdgeTarget_faceBase]
    change (PD.FK.rectanglePrimalEdgeBond a w h pe).faceBase true = _
    rw [hbond,pdBondOfFKC_faceBase]
  · apply (PD.FK.openGraph_adj _ _ _ _).mpr
    refine ⟨PD.FK.rectangleDualGraphEdgeEquiv a w h de,?_,?_⟩
    · exact (PD.FK.mem_rectangleDualConfiguration a w h A de).mpr hclosed
    · rfl

/-- Literal closed-dual adjacency lifts to PD's true finite dual graph,
retaining the actual integer endpoint coordinates. -/
theorem domain_closed_dual_step_to_pd {δ : FKC.PositiveMesh} {D : Set ℂ}
    (a : FKC.LatticeVertex) (w h : ℕ)
    (e : PD.FK.rectangleGraph a w h ≃g FKC.domainLatticeGraph δ D)
    (he : ∀ u, (e u).val = u.val)
    (A : PD.FK.Configuration (PD.FK.rectangleGraph a w h))
    {x y : FKC.LatticeVertex}
    (hxy : (domainClosedDualGraph (FKC.FiniteFK.configurationIso e A)).Adj x y) :
    ∃ u v : PD.FK.RectangleDualVertex a w h, u.val = x ∧ v.val = y ∧
      (PD.FK.openGraph (PD.FK.rectangleDualGraph a w h)
        (PD.FK.rectangleDualConfiguration a w h A)).Adj u v := by
  obtain ⟨b,hb,hends⟩ := hxy
  obtain ⟨u,v,hu,hv,huv⟩ := domain_closed_bond_to_pd_dual a w h e he A b hb
  rcases hends with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact ⟨u,v,hu.trans hx.symm,hv.trans hy.symm,huv⟩
  · exact ⟨v,u,hv.trans hx.symm,hu.trans hy.symm,huv.symm⟩

/-- An actual closed-dual walk lifts to the true complementary finite dual,
starting from any representative of its initial integer face base. -/
theorem domain_closed_dual_reachable_to_pd {δ : FKC.PositiveMesh} {D : Set ℂ}
    (a : FKC.LatticeVertex) (w h : ℕ)
    (e : PD.FK.rectangleGraph a w h ≃g FKC.domainLatticeGraph δ D)
    (he : ∀ u, (e u).val = u.val)
    (A : PD.FK.Configuration (PD.FK.rectangleGraph a w h))
    {x y : FKC.LatticeVertex}
    (hxy : (domainClosedDualGraph (FKC.FiniteFK.configurationIso e A)).Reachable x y)
    (u : PD.FK.RectangleDualVertex a w h) (hu : u.val = x) :
    ∃ v : PD.FK.RectangleDualVertex a w h, v.val = y ∧
      (PD.FK.openGraph (PD.FK.rectangleDualGraph a w h)
        (PD.FK.rectangleDualConfiguration a w h A)).Reachable u v := by
  obtain ⟨p⟩ := hxy
  induction p generalizing u with
  | nil => exact ⟨u,hu,SimpleGraph.Reachable.refl u⟩
  | @cons x z y hxz p ih =>
    obtain ⟨r,s,hr,hs,hrs⟩ := domain_closed_dual_step_to_pd a w h e he A hxz
    have hru : r = u := Subtype.ext (hr.trans hu.symm)
    subst r
    obtain ⟨v,hv,hsv⟩ := ih s hs
    exact ⟨v,hv,hrs.reachable.trans hsv⟩

end PottsContinuity.PlanarTopology
