-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxFinitePolygonCandidates.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteSimplePathCarrier
public import PottsContinuity.FKC.FiniteFK.SlitBoxCanonicalReturn
public import PottsContinuity.FKC.FiniteFK.SlitBoxFirstHitCycle
public import PottsContinuity.FKC.Domains.LatticePolygonOfCycle
public import PottsContinuity.FKC.Domains.LatticePolygonFiniteCellFilling
public import PottsContinuity.FKC.FiniteFK.SlitBoxFirstHitPathGeometry
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- Configuration-independent simple paths in the literal slit graph that
start at `u`, end on the wired arc, and first hit that arc at their endpoint. -/
abbrev SlitBoxFirstHitBaseCandidates (n : ℕ) (u : SlitBoxVertex n) :=
  FirstHitSimplePathCarrier (slitBoxGraph n) u (slitBoxWiredArc n : Set (SlitBoxVertex n))

def slitBoxBaseToAllOpenHom (n : ℕ)
    (A : Configuration (slitBoxGraph n)) [Fintype (slitBoxGraph n).edgeSet
    ] (hA : A = Finset.univ) :
    slitBoxGraph n →g openGraph (slitBoxGraph n) A where
  toFun := id
  map_rel' := by
    intro x y hxy
    apply (openGraph_adj (slitBoxGraph n) A x y).2
    change s(x, y) ∈ Subtype.val '' (↑A : Set (slitBoxGraph n).edgeSet)
    rw [hA]
    refine ⟨⟨s(x, y), (slitBoxGraph n).mem_edgeSet.mpr hxy⟩, ?_, rfl⟩
    exact Finset.mem_univ _

/-- The fixed explicit simple cycle obtained by mapping a base candidate's
original slit path and appending its canonical exterior return. -/
noncomputable def slitBoxFirstHitCandidateCycle
    (n : ℕ) (_hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u) :
    squareLattice.Walk u.val u.val := by
  classical
  letI : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  let hA : A = Finset.univ := rfl
  let f := slitBoxBaseToAllOpenHom n A hA
  let t := p.val.1
  exact (((p.val.2 : (slitBoxGraph n).Walk u t).map f).map
      (slitBoxOpenGraphToSquareLatticeHom n A)).append
    (slitBoxCanonicalReturnWalk n u huY huX t p.property.1)

theorem slitBoxFirstHitCandidateCycle_isCycle
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u) :
    (slitBoxFirstHitCandidateCycle n hn u huY huX p).IsCycle := by
  classical
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  let hA : A = Finset.univ := rfl
  let f := slitBoxBaseToAllOpenHom n A hA
  let t := p.val.1
  let pOpen : (openGraph (slitBoxGraph n) A).Walk u t :=
    (p.val.2 : (slitBoxGraph n).Walk u t).map f
  have hpOpen : pOpen.IsPath := p.val.2.property.map (by
    intro x y hxy
    exact hxy)
  have hfirst : ∀ x ∈ pOpen.support,
      x ∈ (slitBoxWiredArc n : Set (SlitBoxVertex n)) → x = t := by
    intro x hx hxArc
    have hxBase : x ∈ finiteSimplePathSupport p.val := by
      simpa [pOpen, finiteSimplePathSupport, SimpleGraph.Walk.support_map,
        slitBoxBaseToAllOpenHom, f] using hx
    exact p.property.2 x hxBase hxArc
  let r := slitBoxCanonicalReturnWalk n u huY huX t p.property.1
  have hr : r.IsPath := slitBoxCanonicalReturnWalk_isPath n hn u huY huX t p.property.1
  have hreturn : ∀ x ∈ r.support,
      x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) →
        x = u.val ∨ (x.1 = 0 ∧ 0 ≤ x.2 ∧ x.2 ≤ n) := by
    intro x hx hxBox
    exact slitBoxCanonicalReturnWalk_support_in_box n u huY huX t p.property.1 hx hxBox
  have hcorner : ((n + 1 : ℤ), (n + 1 : ℤ)) ∈ r.support :=
    slitBoxCanonicalReturnWalk_corner n u huY huX t p.property.1
  have hout : ((n + 1 : ℤ), (n + 1 : ℤ)) ∉
      latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) :=
    slitBoxCanonicalReturnWalk_outside_box n
  have hcycle := slitBox_firstHit_path_append_exterior_return_isCycle
    n hn A u huY t p.property.1 pOpen hpOpen hfirst r hr hreturn
    ⟨(n + 1, n + 1), hcorner, hout⟩
  change ((pOpen.map (slitBoxOpenGraphToSquareLatticeHom n A)).append r).IsCycle
  exact hcycle

/-- The exact ordered polygon associated with a fixed first-hit candidate. -/
noncomputable def slitBoxFirstHitCandidatePolygon
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u) :
    LatticePolygon ((slitBoxFirstHitCandidateCycle n hn u huY huX p).length - 3) :=
  latticePolygonOfCycle (slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p)

/-- The genuine domain-interior cell bases of the candidate's actual polygon. -/
noncomputable def slitBoxFirstHitCandidateInteriorCells
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u) : Finset LatticeVertex :=
  (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ

end PottsContinuity.FKC.FiniteFK
