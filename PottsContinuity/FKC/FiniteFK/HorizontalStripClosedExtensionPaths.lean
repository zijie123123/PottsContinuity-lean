-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedExtensionPaths.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleConfiguration
public import PottsContinuity.FKC.FiniteFK.HorizontalStripBlockerLocality
public import PottsContinuity.FKC.FiniteFK.HorizontalStripGoodEvent
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
noncomputable section

/-- An open primal edge in a closed-outside rectangle extension has both
strip endpoints inside the rectangle's horizontal collar. -/
theorem horizontalStripClosedExtension_openAdj_endpoint_bounds
    (N n : ℕ) (A : Finset (horizontalStripCutRectangle N n).edgeSet)
    {u v : horizontalStripVertex n}
    (hAdj : (horizontalStripOpenGraph n
      (horizontalStripRectanglePlaneExtension N n A)).Adj u v) :
    (-(N : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ N) ∧
      (-(N : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ N) := by
  classical
  change (wholePlaneOpenPrimalGraph
    (horizontalStripRectanglePlaneExtension N n A)).Adj u.val v.val at hAdj
  rcases hAdj with ⟨hadj, hopen⟩
  rcases LatticeBond.exists_of_adj hadj with ⟨b, hb⟩
  have hEdgeEq : (⟨b.toSym2, b.toSym2_mem_edgeSet⟩ : squareLattice.edgeSet) =
      ⟨s(u.val, v.val), squareLattice.mem_edgeSet.mpr hadj⟩ := by
    apply Subtype.ext
    exact hb
  have hplane : horizontalStripRectanglePlaneExtension N n A
      ⟨b.toSym2, b.toSym2_mem_edgeSet⟩ = true := by
    rw [hEdgeEq]
    exact hopen
  have hmem : (⟨b.toSym2, b.toSym2_mem_edgeSet⟩ : squareLattice.edgeSet) ∈
      A.image (horizontalStripRectangleOriginalEdge N n) := of_decide_eq_true (by
    simpa [horizontalStripRectanglePlaneExtension] using hplane)
  rcases Finset.mem_image.mp hmem with ⟨e, heA, heq⟩
  have hpair : b.toSym2 = (horizontalStripRectangleOriginalEdge N n e).val :=
    (congrArg Subtype.val heq).symm
  rw [horizontalStripRectangleOriginalEdge_val] at hpair
  change b.toSym2 = Sym2.map (fun z : RectangleVertex
    (-(N : ℤ), 0) (2 * N) (2 * n) => z.val) e.val at hpair
  have hsMem : b.source ∈ b.toSym2 := (Sym2.mem_iff').2 (Or.inl rfl)
  have htMem : b.target ∈ b.toSym2 := (Sym2.mem_iff').2 (Or.inr rfl)
  rw [hpair, Sym2.mem_map] at hsMem htMem
  rcases hsMem with ⟨x, hx, hxs⟩
  rcases htMem with ⟨y, hy, hyt⟩
  have hxBounds := (mem_latticeRectangle (-(N : ℤ), 0) x.val (2 * N) (2 * n)).mp x.property
  have hyBounds := (mem_latticeRectangle (-(N : ℤ), 0) y.val (2 * N) (2 * n)).mp y.property
  have hbondPair : b.toSym2 = s(u.val, v.val) := hb
  rcases Sym2.eq_iff.mp hbondPair with ⟨hus, hvt⟩ | ⟨hut, hvs⟩
  · have hu := congrArg Prod.fst (hus.symm.trans hxs.symm)
    have hv := congrArg Prod.fst (hvt.symm.trans hyt.symm)
    constructor
    · constructor <;> (rw [hu]; omega)
    · constructor <;> (rw [hv]; omega)
  · have hu := congrArg Prod.fst (hvs.symm.trans hyt.symm)
    have hv := congrArg Prod.fst (hut.symm.trans hxs.symm)
    constructor
    · constructor <;> (rw [hu]; omega)
    · constructor <;> (rw [hv]; omega)

/-- A path in the closed extension that starts inside the rectangle collar
cannot leave it: every edge it uses has both endpoints in the collar. -/
theorem horizontalStripClosedExtension_walk_support_bounds_of_start
    (N n : ℕ) (A : Finset (horizontalStripCutRectangle N n).edgeSet)
    {u v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n
      (horizontalStripRectanglePlaneExtension N n A)).Walk u v)
    (hu : -(N : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ N) :
    ∀ z ∈ p.support, -(N : ℤ) ≤ z.val.1 ∧ z.val.1 ≤ N := by
  induction p with
  | nil =>
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact hu
  | @cons a b c hadj tail ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hu
      · apply ih
        · exact (horizontalStripClosedExtension_openAdj_endpoint_bounds N n A hadj).2
        · exact hz

/-- The reverse formulation obtains the same collar control from the path's
terminal vertex. -/
theorem horizontalStripClosedExtension_walk_support_bounds_of_end
    (N n : ℕ) (A : Finset (horizontalStripCutRectangle N n).edgeSet)
    {u v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n
      (horizontalStripRectanglePlaneExtension N n A)).Walk u v)
    (hv : -(N : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ N) :
    ∀ z ∈ p.support, -(N : ℤ) ≤ z.val.1 ∧ z.val.1 ≤ N := by
  have hr : ∀ z ∈ p.reverse.support, -(N : ℤ) ≤ z.val.1 ∧ z.val.1 ≤ N :=
    horizontalStripClosedExtension_walk_support_bounds_of_start N n A p.reverse hv
  intro z hz
  have hz' : z ∈ p.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr hz
  exact hr z hz'

/-- The rectangle vertex corresponding to a strip vertex known to lie in the
closed-extension collar. -/
def horizontalStripClosedExtension_rectangleVertex (N n : ℕ)
    (v : horizontalStripVertex n)
    (hv : -(N : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ N) :
    RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
  (horizontalStripBlockerCollarEquiv N n).symm ⟨v, hv⟩

@[simp] theorem horizontalStripClosedExtension_rectangleVertex_val
    (N n : ℕ) (v : horizontalStripVertex n)
    (hv : -(N : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ N) :
    (horizontalStripClosedExtension_rectangleVertex N n v hv).val = v.val := rfl

/-- Any closed-extension strip walk with its initial point in the collar lifts
to the actual finite rectangle graph. The support correspondence records every
vertex, including repetitions and the endpoints. -/
theorem horizontalStripClosedExtension_walk_lifts_to_rectangle
    (N n : ℕ) (A : Finset (horizontalStripCutRectangle N n).edgeSet)
    {u v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n
      (horizontalStripRectanglePlaneExtension N n A)).Walk u v)
    (hu : -(N : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ N) :
    ∃ q : (horizontalStripRectangleOpenGraph N n
        (horizontalStripRectanglePlaneExtension N n A)).Walk
          (horizontalStripClosedExtension_rectangleVertex N n u hu)
          (horizontalStripClosedExtension_rectangleVertex N n v
            (horizontalStripClosedExtension_walk_support_bounds_of_start N n A p
              hu v p.end_mem_support)),
      q.support.map (horizontalStripBlockerRectangleToStrip N n) = p.support := by
  classical
  have hsupport : ∀ z ∈ p.support,
      z ∈ {z : horizontalStripVertex n | horizontalStripBlockerCollarBound n N z} := by
    intro z hz
    exact horizontalStripClosedExtension_walk_support_bounds_of_start N n A p hu z hz
  let pC : (horizontalStripBlockerCollarGraphOnStrip N n
      (horizontalStripRectanglePlaneExtension N n A)).Walk
        ⟨u, horizontalStripClosedExtension_walk_support_bounds_of_start
          N n A p hu u p.start_mem_support⟩
        ⟨v, horizontalStripClosedExtension_walk_support_bounds_of_start
          N n A p hu v p.end_mem_support⟩ := by
    change ((horizontalStripOpenGraph n
      (horizontalStripRectanglePlaneExtension N n A)).induce
        {z : horizontalStripVertex n | horizontalStripBlockerCollarBound n N z}).Walk _ _
    exact p.induce _ hsupport
  let I := horizontalStripBlockerCollarGraphIso N n
    (horizontalStripRectanglePlaneExtension N n A)
  let q : (horizontalStripRectangleOpenGraph N n
      (horizontalStripRectanglePlaneExtension N n A)).Walk
        (horizontalStripClosedExtension_rectangleVertex N n u hu)
        (horizontalStripClosedExtension_rectangleVertex N n v
          (horizontalStripClosedExtension_walk_support_bounds_of_start N n A p
            hu v p.end_mem_support)) :=
    pC.map I.symm.toHom
  refine ⟨q, ?_⟩
  have hfun (w : horizontalStripBlockerCollarSet N n) :
      horizontalStripBlockerRectangleToStrip N n (I.symm.toHom w) = w.val := by
    apply Subtype.ext
    rfl
  have hq : q.support.map (horizontalStripBlockerRectangleToStrip N n) =
      pC.support.map Subtype.val := by
    change List.map (horizontalStripBlockerRectangleToStrip N n)
      (SimpleGraph.Walk.map I.symm.toHom pC).support = _
    rw [SimpleGraph.Walk.support_map, List.map_map]
    apply List.map_congr_left
    intro w hw
    exact hfun w
  have hinduce : pC.support.map Subtype.val = p.support := by
    change (p.induce
      {z : horizontalStripVertex n | horizontalStripBlockerCollarBound n N z} hsupport).support.map
        Subtype.val = p.support
    rw [SimpleGraph.Walk.support_induce]
    change List.map Subtype.val
      (List.pmap (fun z hz => (⟨z, hz⟩ : {z : horizontalStripVertex n |
        horizontalStripBlockerCollarBound n N z})) p.support hsupport) = p.support
    rw [List.map_pmap]
    rw [List.pmap_eq_map]
    simp
  exact hq.trans hinduce
end
end PottsContinuity.FKC.Medial
