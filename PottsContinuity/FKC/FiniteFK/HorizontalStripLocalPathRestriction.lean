-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripLocalPathRestriction.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutPathLocalization
public import PottsContinuity.FKC.FiniteFK.HorizontalStripBlockerLocality
public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleClopenEvents

@[expose] public section

namespace PottsContinuity.FKC.Medial

noncomputable section

/-- The literal centered-rectangle vertex with the same lattice coordinate as a
strip vertex whose column lies in `[-M,M]`. -/
def horizontalStripRectangleVertexOfStrip (M n : ℕ)
    (v : horizontalStripVertex n)
    (hv : -(M : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ M) :
    RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n) := by
  refine ⟨v.val, ?_⟩
  rw [mem_latticeRectangle]
  constructor
  · constructor
    · exact hv.1
    · have hwidth : -(M : ℤ) + ((2 * M : ℕ) : ℤ) = (M : ℤ) := by
        push_cast
        ring
      rw [hwidth]
      exact hv.2
  · constructor
    · exact v.property.1
    · simpa using v.property.2

@[simp] theorem horizontalStripRectangleVertexOfStrip_val (M n : ℕ)
    (v : horizontalStripVertex n)
    (hv : -(M : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ M) :
    (horizontalStripRectangleVertexOfStrip M n v hv).val = v.val := rfl

private theorem horizontalStripWalk_lifts_to_rectangleOpenGraph
    (M n : ℕ) (ω : LatticeConfiguration)
    {u v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n ω).Walk u v)
    (hbound : ∀ z ∈ p.support,
      -(M : ℤ) ≤ z.val.1 ∧ z.val.1 ≤ M) :
    ∃ q : (horizontalStripRectangleOpenGraph M n ω).Walk
        (horizontalStripRectangleVertexOfStrip M n u (hbound u p.start_mem_support))
        (horizontalStripRectangleVertexOfStrip M n v (hbound v p.end_mem_support)),
      q.support.map (horizontalStripBlockerRectangleToStrip M n) = p.support := by
  let I := horizontalStripBlockerCollarGraphIso M n ω
  have hsupport : ∀ z ∈ p.support,
      z ∈ {z : horizontalStripVertex n | horizontalStripBlockerCollarBound n M z} := by
    intro z hz
    exact hbound z hz
  let pC : (horizontalStripBlockerCollarGraphOnStrip M n ω).Walk
      ⟨u, hbound u p.start_mem_support⟩ ⟨v, hbound v p.end_mem_support⟩ := by
    change ((horizontalStripOpenGraph n ω).induce
      {z : horizontalStripVertex n | horizontalStripBlockerCollarBound n M z}).Walk _ _
    exact p.induce _ hsupport
  let uR := horizontalStripRectangleVertexOfStrip M n u (hbound u p.start_mem_support)
  let vR := horizontalStripRectangleVertexOfStrip M n v (hbound v p.end_mem_support)
  have hmapU : I.toEquiv uR = ⟨u, hbound u p.start_mem_support⟩ := by
    change horizontalStripBlockerRectangleToCollar M n uR = _
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hmapV : I.toEquiv vR = ⟨v, hbound v p.end_mem_support⟩ := by
    change horizontalStripBlockerRectangleToCollar M n vR = _
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hstart : I.toEquiv.symm ⟨u, hbound u p.start_mem_support⟩ = uR := by
    apply I.toEquiv.injective
    calc
      I.toEquiv (I.toEquiv.symm ⟨u, hbound u p.start_mem_support⟩) =
          ⟨u, hbound u p.start_mem_support⟩ := I.toEquiv.apply_symm_apply _
      _ = I.toEquiv uR := hmapU.symm
  have hend : I.toEquiv.symm ⟨v, hbound v p.end_mem_support⟩ = vR := by
    apply I.toEquiv.injective
    calc
      I.toEquiv (I.toEquiv.symm ⟨v, hbound v p.end_mem_support⟩) =
          ⟨v, hbound v p.end_mem_support⟩ := I.toEquiv.apply_symm_apply _
      _ = I.toEquiv vR := hmapV.symm
  let q0 := pC.map I.symm.toHom
  have hqstart : (I.symm.toHom ⟨u, hbound u p.start_mem_support⟩) = uR := by
    change I.toEquiv.symm ⟨u, hbound u p.start_mem_support⟩ = uR
    exact hstart
  have hqend : (I.symm.toHom ⟨v, hbound v p.end_mem_support⟩) = vR := by
    change I.toEquiv.symm ⟨v, hbound v p.end_mem_support⟩ = vR
    exact hend
  let q : (horizontalStripRectangleOpenGraph M n ω).Walk uR vR :=
    q0.copy hqstart hqend
  refine ⟨q, ?_⟩
  have hfun (z : horizontalStripBlockerCollarSet M n) :
      horizontalStripBlockerRectangleToStrip M n (I.symm.toHom z) = z.val := by
    apply Subtype.ext
    rfl
  have hq0 : q0.support.map (horizontalStripBlockerRectangleToStrip M n) =
      pC.support.map Subtype.val := by
    change List.map (horizontalStripBlockerRectangleToStrip M n)
      (SimpleGraph.Walk.map I.symm.toHom pC).support = _
    rw [SimpleGraph.Walk.support_map, List.map_map]
    apply List.map_congr_left
    intro z hz
    exact hfun z
  have hinduce : pC.support.map Subtype.val = p.support := by
    change (p.induce
      {z : horizontalStripVertex n | horizontalStripBlockerCollarBound n M z} hsupport).support.map
        Subtype.val = p.support
    rw [SimpleGraph.Walk.support_induce]
    change List.map Subtype.val
      (List.pmap (fun z hz => (⟨z, hz⟩ : {z : horizontalStripVertex n |
        horizontalStripBlockerCollarBound n M z})) p.support hsupport) = p.support
    rw [List.map_pmap]
    rw [List.pmap_eq_map]
    simp
  change List.map (horizontalStripBlockerRectangleToStrip M n)
    (q0.copy hqstart hqend).support = p.support
  rw [SimpleGraph.Walk.support_copy]
  exact hq0.trans hinduce

theorem horizontalStripWalk_lifts_to_rectangleRestriction
    (M n : ℕ) (ω : LatticeConfiguration)
    {u v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n ω).Walk u v)
    (hbound : ∀ z ∈ p.support,
      -(M : ℤ) ≤ z.val.1 ∧ z.val.1 ≤ M) :
    ∃ q : (PottsContinuity.FKC.FiniteFK.openGraph (horizontalStripCutRectangle M n)
      (horizontalStripRectangleRestriction M n ω)).Walk
        (horizontalStripRectangleVertexOfStrip M n u (hbound u p.start_mem_support))
        (horizontalStripRectangleVertexOfStrip M n v (hbound v p.end_mem_support)),
      q.support.map (horizontalStripBlockerRectangleToStrip M n) = p.support := by
  rw [← horizontalStripRectangleOpenGraph_eq_openGraph_restriction M n ω]
  exact horizontalStripWalk_lifts_to_rectangleOpenGraph M n ω p hbound

/-- With two closed cuts, a top connection from their intervening columns
lifts to the actual finite rectangle whenever the whole interval is centered
inside that rectangle. -/
theorem horizontalStripTopReachable_lifts_to_rectangleRestriction_of_closed_cuts
    (M n : ℕ) (ω : LatticeConfiguration) (l r : ℤ)
    (hclosedL : ∀ e ∈ horizontalStripCutEdges n l, ω e = false)
    (hclosedR : ∀ e ∈ horizontalStripCutEdges n r, ω e = false)
    (hleft : -(M : ℤ) ≤ l + 1) (hright : r ≤ M)
    (u : horizontalStripVertex n)
    (hu : l < u.val.1 ∧ u.val.1 ≤ r)
    (hreach : horizontalStripTopReachable n ω u) :
    ∃ v : horizontalStripVertex n, v.val.2 = (2 * n : ℤ) ∧
      ∃ hv : -(M : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ M,
      ∃ p : (horizontalStripOpenGraph n ω).Walk u v,
        (∀ z ∈ p.support, -(M : ℤ) ≤ z.val.1 ∧ z.val.1 ≤ M) ∧
        ∃ q : (PottsContinuity.FKC.FiniteFK.openGraph (horizontalStripCutRectangle M n)
          (horizontalStripRectangleRestriction M n ω)).Walk
            (horizontalStripRectangleVertexOfStrip M n u (by omega))
            (horizontalStripRectangleVertexOfStrip M n v hv),
          q.support.map (horizontalStripBlockerRectangleToStrip M n) = p.support := by
  obtain ⟨x, hconn⟩ := hreach
  obtain ⟨p⟩ := hconn
  have hwindow := horizontalStripWalk_support_localized_by_closed_cuts
    n ω l r hclosedL hclosedR p hu
  have hbound : ∀ z ∈ p.support,
      -(M : ℤ) ≤ z.val.1 ∧ z.val.1 ≤ M := by
    intro z hz
    have hz' : z ∈ horizontalStripClosedCutColumnWindow n l r := hwindow z hz
    change l < z.val.1 ∧ z.val.1 ≤ r at hz'
    exact ⟨by omega, by omega⟩
  let v := horizontalStripVertexOfNat n x (2 * n) (le_rfl)
  have hvTop : v.val.2 = (2 * n : ℤ) := rfl
  have hvBound : -(M : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ M := hbound v p.end_mem_support
  have hstartBound : -(M : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ M := hbound u p.start_mem_support
  have hlift := horizontalStripWalk_lifts_to_rectangleRestriction M n ω p hbound
  exact ⟨v, hvTop, hvBound, p, hbound, hlift⟩

end
end PottsContinuity.FKC.Medial
