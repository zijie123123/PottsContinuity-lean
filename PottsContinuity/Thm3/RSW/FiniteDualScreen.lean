module

public import PottsContinuity.Thm3.RSW.AnnulusShielding
public import PottsContinuity.PD.Duality.RayIndex

/-!
# Actual finite closed-dual circuit screens

A screen is a simple dual cycle, with every crossed sampled primal bond closed,
whose ray index distinguishes every vertex of U from every vertex outside W.
This is full-source-set separation; a nonzero index at the center alone is
insufficient. There is no circuit selector and no conditional-law premise.
-/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- Closure of the sampled primal bonds crossed by a given actual dual walk.
Only bonds in the ambient finite induced graph are sampled. -/
def finiteDualWalkClosed (V : Finset (ℤ × ℤ))
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    {x : ℤ × ℤ} (p : PD.FK.squareLattice.Walk x x) : Prop :=
  ∀ b : LatticeBond, (dualBondOfPrimal b).toSym2 ∈ p.edges →
    ∀ e : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet,
      Sym2.map Subtype.val e.val = b.toSym2 → e ∉ A

/-- An actual closed-dual simple circuit separating the whole source region
U from all ambient vertices outside W, in the precise ray-index sense. -/
def dualCircuitScreenEvent (V : Finset (ℤ × ℤ))
    (U W : Set (V : Set (ℤ × ℤ))) :
    Set (Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :=
  {A | ∃ x : ℤ × ℤ, ∃ p : PD.FK.squareLattice.Walk x x,
    p.IsCycle ∧ finiteDualWalkClosed V A p ∧
      ∀ v ∈ U, ∀ w, w ∉ W → rayIndex v.val p ≠ rayIndex w.val p}

/-- Actual primal paths cannot cross any bond of the closed dual walk. -/
def finiteDualScreenOpenHom (V : Finset (ℤ × ℤ))
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    {x : ℤ × ℤ} (p : PD.FK.squareLattice.Walk x x) (hclosed : finiteDualWalkClosed V A p) :
    openGraph (squareLattice.induce (V : Set (ℤ × ℤ))) A →g circuitAvoidanceGraph p where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    refine ⟨openGraph_le _ A huv, ?_⟩
    intro b hb hdual
    obtain ⟨e,he,hev⟩ := (openGraph_adj _ A u v).mp huv
    apply hclosed b hdual e ?_ he
    rw [hev]
    change s(u.val,v.val) = b.toSym2
    exact hb.symm

/-- Every cluster meeting the full inner region stays inside the screened
outer region. No finiteness of infinite clusters is assumed. -/
theorem dualCircuitScreen_full_inner_shield (V : Finset (ℤ × ℤ))
    (U W : Set (V : Set (ℤ × ℤ)))
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hA : A ∈ dualCircuitScreenEvent V U W) :
    ∀ v ∈ U, ∀ w, ActualConnected (squareLattice.induce (V : Set (ℤ × ℤ))) A v w → w ∈ W := by
  obtain ⟨x,p,_,hclosed,hsep⟩ := hA
  intro v hv w hconn
  by_contra hw
  have hpath := hconn.map (finiteDualScreenOpenHom V A p hclosed)
  have hidx : rayIndex v.val p = rayIndex w.val p :=
    rayIndex_eq_of_avoidance_reachable p hpath
  exact hsep v hv w hw hidx

/-- A genuine full-inner-box closed-dual screen shields every actual annulus
witness in that box. -/
theorem shieldedAnnulus_of_dualCircuitScreen (V : Finset (ℤ × ℤ))
    (W : Set (V : Set (ℤ × ℤ))) (z : ℤ × ℤ) (n : ℕ)
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hAnn : A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n))
    (hScreen : A ∈ dualCircuitScreenEvent V (vertexBoxRegion V z (2*n)) W) :
    A ∈ shieldedAnnulusEvent V W z n :=
  shieldedAnnulus_of_full_inner_shield V W z n A hAnn
    (dualCircuitScreen_full_inner_shield V _ W A hScreen)

end
end PottsContinuity.RSW
