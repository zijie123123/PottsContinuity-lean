-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripAsymmetricBoundaryLocalization.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreConnectivityLaw
public import PottsContinuity.FKC.FiniteFK.HorizontalStripAsymmetricTopLimit
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightLocalization
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutPathLocalization

@[expose] public section

namespace PottsContinuity.FKC.Medial
open PottsContinuity.FKC PottsContinuity.FKC.FiniteFK

noncomputable section

local instance asymBoundaryCfgFintype (N n : ℕ) :
    Fintype (Configuration (horizontalStripAsymmetricRectangle N n)) := Fintype.ofFinite _
local instance asymBoundaryVertexDecidableEq (N n : ℕ) :
    DecidableEq (RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)) := Classical.decEq _

/-- The full actual left/right/top sides of the asymmetric source rectangle. -/
def horizontalStripAsymmetricFullThreeSides (N n : ℕ) :
    Set (RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)) :=
  {v | v.val.1 = -((N : ℤ) + 1) ∨ v.val.1 = (N : ℤ) ∨ v.val.2 = (2 * n : ℤ)}

/-- A vertex of the asymmetric rectangle, viewed in the actual primal strip. -/
def horizontalStripAsymmetricVertexToStrip (N n : ℕ)
    (v : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)) :
    horizontalStripVertex n := by
  refine ⟨v.val, ?_⟩
  have hv := v.property
  rw [mem_latticeRectangle] at hv
  exact ⟨hv.2.1, by simpa using hv.2.2⟩

@[simp] theorem horizontalStripAsymmetricVertexToStrip_val (N n : ℕ)
    (v : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)) :
    (horizontalStripAsymmetricVertexToStrip N n v).val = v.val := rfl

private theorem horizontalStripAsymmetricRectangleEdge_to_strip_adj
    (N n : ℕ) (A : Configuration (horizontalStripAsymmetricRectangle N n))
    (v : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n))
    {u : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)}
    (hadj : (openGraph (horizontalStripAsymmetricRectangle N n) A).Adj u v) :
    (horizontalStripOpenGraph n (horizontalStripAsymmetricPlaneExtension N n A)).Adj
      (horizontalStripAsymmetricVertexToStrip N n u)
      (horizontalStripAsymmetricVertexToStrip N n v) := by
  classical
  let G := horizontalStripAsymmetricRectangle N n
  let ω := horizontalStripAsymmetricPlaneExtension N n A
  have hGadj : G.Adj u v := openGraph_le G A hadj
  rw [openGraph_adj] at hadj
  rcases hadj with ⟨e, heA, heuv⟩
  have hsq : squareLattice.Adj u.val v.val :=
    (rectangleGraph_adj_iff (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n) u v).mp hGadj
  have hmapval : (rectanglePrimalEdgeToSquareEdge
      (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n) e).val =
        Sym2.map (fun x : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n) => x.val) e.val := rfl
  have hEdgeVal : (rectanglePrimalEdgeToSquareEdge
      (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n) e).val = s(u.val, v.val) := by
    rw [hmapval]
    simpa using congrArg
      (Sym2.map (fun x : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n) => x.val)) heuv
  have hstate : ω (rectanglePrimalEdgeToSquareEdge
      (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n) e) = true := by
    change decide (rectanglePrimalEdgeToSquareEdge
      (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n) e ∈
        A.image (rectanglePrimalEdgeToSquareEdge (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n))) = true
    exact decide_eq_true_iff.mpr (Finset.mem_image.mpr ⟨e, heA, rfl⟩)
  have hwhole : (wholePlaneOpenPrimalGraph ω).Adj u.val v.val := by
    refine ⟨hsq, ?_⟩
    have hcoord : (rectanglePrimalEdgeToSquareEdge
        (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n) e) =
        ⟨s(u.val, v.val), squareLattice.mem_edgeSet.mpr hsq⟩ := by
      apply Subtype.ext
      exact hEdgeVal
    simpa [ω, hcoord] using hstate
  exact hwhole

private theorem horizontalStripAsymmetricWalk_to_strip
    (N n : ℕ) (A : Configuration (horizontalStripAsymmetricRectangle N n))
    {u v : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)}
    (p : (openGraph (horizontalStripAsymmetricRectangle N n) A).Walk u v) :
    Nonempty ((horizontalStripOpenGraph n (horizontalStripAsymmetricPlaneExtension N n A)).Walk
      (horizontalStripAsymmetricVertexToStrip N n u)
      (horizontalStripAsymmetricVertexToStrip N n v)) := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons x y z hadj tail ih =>
      rcases ih with ⟨tailStrip⟩
      exact ⟨SimpleGraph.Walk.cons
        (horizontalStripAsymmetricRectangleEdge_to_strip_adj N n A y hadj) tailStrip⟩

/-- Any actual connection from column zero, height at most `n`, to a full
side of the asymmetric finite rectangle either gives the original strip-height
bound or requires failure of the literal two-closed-cut event. -/
theorem horizontalStripAsymmetric_center_to_boundary_localizes
    (N M n : ℕ) (hMN : M ≤ N)
    (A : Configuration (horizontalStripAsymmetricRectangle N n))
    {u : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)}
    (huX : u.val.1 = 0) (huY : 0 ≤ u.val.2 ∧ u.val.2 ≤ (n : ℤ))
    {z : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)}
    (hz : z ∈ horizontalStripAsymmetricFullThreeSides N n)
    (hconn : ActualConnected (horizontalStripAsymmetricRectangle N n) A u z) :
    horizontalStripHeight n (horizontalStripAsymmetricPlaneExtension N n A) 0 ≤ n ∨
      horizontalStripAsymmetricPlaneExtension N n A ∉ horizontalStripLocalClosedCutSuccess M n := by
  classical
  let ω := horizontalStripAsymmetricPlaneExtension N n A
  by_cases hcuts : ω ∈ horizontalStripLocalClosedCutSuccess M n
  · left
    rcases hcuts with ⟨l, hlower, hleft, r, hright, hupper, hclosedL, hclosedR⟩
    rcases (actualConnected_iff_walk _ _ _ _).mp hconn with ⟨p⟩
    obtain ⟨pStrip⟩ := horizontalStripAsymmetricWalk_to_strip N n A p
    have hstartX : (horizontalStripAsymmetricVertexToStrip N n u).val.1 = 0 := huX
    have hstartY : 0 ≤ (horizontalStripAsymmetricVertexToStrip N n u).val.2 ∧
        (horizontalStripAsymmetricVertexToStrip N n u).val.2 ≤ (n : ℤ) := huY
    rcases hz with hleftSide | hrightSide | htopSide
    · have hzle : (horizontalStripAsymmetricVertexToStrip N n z).val.1 ≤ l := by
        rw [horizontalStripAsymmetricVertexToStrip_val]
        change z.val.1 = -((N : ℤ) + 1) at hleftSide
        rw [hleftSide]
        omega
      have hstartgt : l < (horizontalStripAsymmetricVertexToStrip N n u).val.1 := by
        rw [horizontalStripAsymmetricVertexToStrip_val]
        simpa [huX] using hleft
      have hblocked := horizontalStripClosedCut_not_reachable n ω l
        (horizontalStripAsymmetricVertexToStrip N n z)
        (horizontalStripAsymmetricVertexToStrip N n u) hzle hstartgt hclosedL
      exact False.elim (hblocked pStrip.reachable.symm)
    · have hstartle : (horizontalStripAsymmetricVertexToStrip N n u).val.1 ≤ r := by
        rw [horizontalStripAsymmetricVertexToStrip_val]
        simpa [huX] using hright
      have hzgt : r < (horizontalStripAsymmetricVertexToStrip N n z).val.1 := by
        rw [horizontalStripAsymmetricVertexToStrip_val]
        change z.val.1 = (N : ℤ) at hrightSide
        rw [hrightSide]
        omega
      have hblocked := horizontalStripClosedCut_not_reachable n ω r
        (horizontalStripAsymmetricVertexToStrip N n u)
        (horizontalStripAsymmetricVertexToStrip N n z) hstartle hzgt hclosedR
      exact False.elim (hblocked pStrip.reachable)
    · have htopCoord : (horizontalStripAsymmetricVertexToStrip N n z).val.2 = (2 * n : ℤ) := htopSide
      let y : ℕ := Int.toNat u.val.2
      have hyval : (y : ℤ) = u.val.2 := Int.toNat_of_nonneg huY.1
      have hyn : y ≤ n := by
        have hy : (y : ℤ) ≤ (n : ℤ) := by simpa [hyval] using huY.2
        exact_mod_cast hy
      have hstartEq : horizontalStripAsymmetricVertexToStrip N n u =
          horizontalStripVertexOfNat n 0 y (by omega) := by
        apply Subtype.ext
        apply Prod.ext
        · rw [horizontalStripAsymmetricVertexToStrip_val]
          simp [horizontalStripVertexOfNat, huX]
        · change u.val.2 = (y : ℤ)
          exact hyval.symm
      have hendEq : horizontalStripAsymmetricVertexToStrip N n z =
          horizontalStripVertexOfNat n (z.val.1) (2 * n) le_rfl := by
        apply Subtype.ext
        apply Prod.ext
        · rw [horizontalStripAsymmetricVertexToStrip_val]
          rfl
        · rw [horizontalStripAsymmetricVertexToStrip_val]
          exact htopCoord
      have hreach : horizontalStripTopReachable n ω
          (horizontalStripVertexOfNat n 0 y (by omega)) := by
        refine ⟨z.val.1, ?_⟩
        have hreach' : (horizontalStripOpenGraph n ω).Reachable
            (horizontalStripAsymmetricVertexToStrip N n u)
            (horizontalStripAsymmetricVertexToStrip N n z) := pStrip.reachable
        simpa [horizontalStripTopReachable, hstartEq, hendEq] using hreach'
      by_contra hnot
      have hlt : y < horizontalStripHeight n ω 0 :=
        lt_of_le_of_lt hyn (Nat.lt_of_not_ge hnot)
      exact (horizontalStripHeight_no_lower_top_connection n ω 0 y hlt) hreach
  · exact Or.inr (by simpa [ω] using hcuts)

end
end PottsContinuity.FKC.Medial
