-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitScreenSupportSeparation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitScreenLocalSupport
public import PottsContinuity.FKC.FiniteFK.SlitScreenDualEdgeClassification
public import PottsContinuity.FKC.Medial.WholePlanePairing

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

private theorem slitScreenRight_crossed_x_bounds
    (m : ℕ) (d : LatticeBond)
    (hs : d.source ∈ slitScreenRightFaceBases m)
    (ht : d.target ∈ slitScreenRightFaceBases m) :
    (m : ℤ) ≤ (primalBondOfDual d).source.1 ∧
      (m : ℤ) ≤ (primalBondOfDual d).target.1 ∧
      ((m : ℤ) < (primalBondOfDual d).source.1 ∨
       (m : ℤ) < (primalBondOfDual d).target.1) := by
  rcases d with ⟨⟨x, y⟩, ax⟩
  cases ax with
  | horizontal =>
      change (x, y) ∈ slitScreenRightFaceBases m at hs
      change (x + 1, y) ∈ slitScreenRightFaceBases m at ht
      rcases Finset.mem_product.mp hs with ⟨hxs, _⟩
      rcases Finset.mem_Icc.mp hxs with ⟨hx0, _⟩
      simp only [primalBondOfDual, LatticeBond.source, LatticeBond.target]
      exact ⟨by omega, by omega, Or.inl (by omega)⟩
  | vertical =>
      change (x, y) ∈ slitScreenRightFaceBases m at hs
      change (x, y + 1) ∈ slitScreenRightFaceBases m at ht
      rcases Finset.mem_product.mp hs with ⟨hxs, _⟩
      rcases Finset.mem_Icc.mp hxs with ⟨hx0, _⟩
      simp only [primalBondOfDual, LatticeBond.source, LatticeBond.target]
      exact ⟨by omega, by omega, Or.inr (by omega)⟩

/-- Every edge in the actual right screen support has both slit endpoints at
x≥m, and at least one endpoint strictly to the right of x=m. -/
theorem slitScreenRight_support_edge_coordinates
    (m : ℕ) (e : (slitBoxGraph (16 * m)).edgeSet)
    (he : e ∈ slitScreenActualClosedGraphSupport m (slitScreenRightFaceBases m))
    (u v : SlitBoxVertex (16 * m)) (hev : s(u, v) = e.val) :
    (m : ℤ) ≤ u.val.1 ∧ (m : ℤ) ≤ v.val.1 ∧
      ((m : ℤ) < u.val.1 ∨ (m : ℤ) < v.val.1) := by
  simp only [slitScreenActualClosedGraphSupport, Finset.mem_filter,
    Finset.mem_univ, true_and] at he
  rcases he with ⟨d, hsource, htarget, hedge⟩
  have hbounds := slitScreenRight_crossed_x_bounds m d hsource htarget
  have heSym : Sym2.map Subtype.val e.val = s(u.val, v.val) := by
    have := congrArg (Sym2.map Subtype.val) hev
    simpa only [Sym2.map_mk] using this.symm
  have hpair : s((primalBondOfDual d).source, (primalBondOfDual d).target) =
      s(u.val, v.val) := by
    calc
      s((primalBondOfDual d).source, (primalBondOfDual d).target) =
          (latticeBondEdge (primalBondOfDual d)).val := rfl
      _ = (slitBoxEdgeEmbedding (16 * m) e).val := congrArg Subtype.val hedge
      _ = s(u.val, v.val) := heSym
  rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rcases hbounds with ⟨hsource, htarget, hstrict⟩
    have hux : (primalBondOfDual d).source.1 = u.val.1 := congrArg Prod.fst hu
    have hvx : (primalBondOfDual d).target.1 = v.val.1 := congrArg Prod.fst hv
    rcases hstrict with h | h <;> constructor <;> omega
  · rcases hbounds with ⟨hsource, htarget, hstrict⟩
    have hux : (primalBondOfDual d).source.1 = v.val.1 := congrArg Prod.fst hu
    have hvx : (primalBondOfDual d).target.1 = u.val.1 := congrArg Prod.fst hv
    rcases hstrict with h | h <;> constructor <;> omega

end
end PottsContinuity.FKC.FiniteFK
