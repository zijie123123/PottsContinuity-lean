module

public import PottsContinuity.Thm3.Prop4.MarkedHalfTurnRawCovariance
public import PottsContinuity.Thm3.Prop4.MarkedIsoComposition
public import PottsContinuity.Thm3.Prop4.MarkedJointRawReveal
public import PottsContinuity.Thm3.Prop4.RawMarkedStoppedLaw

/-! # The unchanged original box records equal the literal source explorations -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
local instance markedBoxSourceIdentityEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _
local instance markedBoxSourceIdentityFrozenEdgeEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set LatticeVertex)).edgeSet := Classical.decEq _
local instance markedBoxSourceIdentityRectangleEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- The source square's half-turn anchor is its original lower-left corner. -/
theorem markedHalfTurnAnchor_sourceBox (n : ℕ) :
    markedHalfTurnAnchor (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) = (-(n : ℤ),-(n : ℤ)) := by
  apply Prod.ext <;> dsimp [markedHalfTurnAnchor]<;> omega

/-- The original box half-turn, on the coordinate-identical rectangle carrier. -/
def markedBoxRectangleHalfTurnIso (n : ℕ) :
    rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) ≃g
      rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) :=
  (boxTubeRectangleIso n).symm.trans ((boxHalfTurnIso n).trans (boxTubeRectangleIso n))

/-- The conjugated original box map has precisely the same primal coordinates. -/
theorem markedBoxRectangleHalfTurnIso_val (n : ℕ)
    (x : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :
    (markedBoxRectangleHalfTurnIso n x).val = -x.val := by
  change (boxTubeRectangleIso n (boxHalfTurnIso n ((boxTubeRectangleIso n).symm x))).val = -x.val
  rw [boxTubeRectangleIso_val,boxHalfTurnIso_val,boxTubeRectangleIso_symm_val]

/-- Exact configuration commutation, including every original sampled bond. -/
theorem markedBoxRectangleHalfTurn_configuration (n : ℕ)
    (A : Configuration (finiteLatticeGraph (box n))) :
    configurationIso (markedBoxRectangleHalfTurnIso n) (configurationIso (boxTubeRectangleIso n) A) =
      configurationIso (boxTubeRectangleIso n) (configurationIso (boxHalfTurnIso n) A) := by
  let R := boxTubeRectangleIso n
  let H := boxHalfTurnIso n
  calc
    _ = configurationIso (H.trans R) (configurationIso R.symm (configurationIso R A)) :=
      markedConfigurationIso_trans R.symm (H.trans R) (configurationIso R A)
    _ = configurationIso (H.trans R) A :=
      congrArg (configurationIso (H.trans R)) ((configurationIso R).symm_apply_apply A)
    _ = _ := markedConfigurationIso_trans H R A


/-- The literal upper sampled exploration rotates to the literal lower
exploration on the source rectangle's original carrier. -/
theorem sampledUpperRawReveal_sourceBox_halfTurn (n : ℕ) (u v : LatticeVertex)
    (A : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))) :
    configurationIso (markedBoxRectangleHalfTurnIso n)
      (sampledRawDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) A) =
    sampledRawDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (-v) (-u))
      (configurationIso (markedBoxRectangleHalfTurnIso n) A) := by
  have bundle : ∃ i : rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) ≃g
      rectangleGraph (markedHalfTurnAnchor (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) (2*n) (2*n),
      (∀ x, (i x).val = -x.val) ∧
      ∀ (u v : LatticeVertex) (A : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))),
      configurationIso i (sampledRawDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) A) =
      sampledRawDualReveal (markedHalfTurnAnchor (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) (2*n) (2*n)
        (PlanarTopology.rectangleLowerDualArc (markedHalfTurnAnchor (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) (2*n) (2*n) (-v) (-u))
        (configurationIso i A) :=
    ⟨markedRectangleHalfTurnIso _ _ _,markedRectangleHalfTurnIso_val _ _ _,
      fun u v A => sampledUpperRawReveal_markedHalfTurn _ _ _ u v A⟩
  rw [markedHalfTurnAnchor_sourceBox] at bundle
  obtain ⟨i,hi,hcov⟩ := bundle
  have hiEq : i = markedBoxRectangleHalfTurnIso n := by
    apply RelIso.ext
    intro x
    apply Subtype.ext
    exact (hi x).trans (markedBoxRectangleHalfTurnIso_val n x).symm
  subst i
  exact hcov u v A

/-- The UNCHANGED upper box raw record equals the actual upper-seed sampled
exploration after the coordinate-identical original-box/rectangle transport. -/
theorem markedUpperBoxRawReveal_eq_source_upper (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) :
    configurationIso (boxTubeRectangleIso n) (markedUpperBoxRawReveal n u v A) =
      sampledRawDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val)
        (configurationIso (boxTubeRectangleIso n) A) := by
  have hcov := sampledUpperRawReveal_sourceBox_halfTurn n u.val v.val (configurationIso (boxTubeRectangleIso n) A)
  have comm := markedBoxRectangleHalfTurn_configuration n A
  have hcov' := hcov.trans (congrArg
    (sampledRawDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (-v.val) (-u.val))) comm)
  have hUpper : configurationIso (boxHalfTurnIso n) (markedUpperBoxRawReveal n u v A) =
      markedLowerBoxRawReveal n (boxHalfTurnIso n v) (boxHalfTurnIso n u)
        (configurationIso (boxHalfTurnIso n) A) :=
    (configurationIso (boxHalfTurnIso n)).apply_symm_apply _
  have hLower : configurationIso (boxTubeRectangleIso n)
      (markedLowerBoxRawReveal n (boxHalfTurnIso n v) (boxHalfTurnIso n u) (configurationIso (boxHalfTurnIso n) A)) =
      markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (boxHalfTurnIso n v).val (boxHalfTurnIso n u).val
        (configurationIso (boxTubeRectangleIso n) (configurationIso (boxHalfTurnIso n) A)) :=
    (configurationIso (boxTubeRectangleIso n)).apply_symm_apply _
  have hLower' : configurationIso (boxTubeRectangleIso n)
      (markedLowerBoxRawReveal n (boxHalfTurnIso n v) (boxHalfTurnIso n u) (configurationIso (boxHalfTurnIso n) A)) =
      sampledRawDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (-v.val) (-u.val))
        (configurationIso (boxTubeRectangleIso n) (configurationIso (boxHalfTurnIso n) A)) := by
    simpa only [boxHalfTurnIso_val,sampledRawDualReveal_lower_arc_eq] using hLower
  apply (configurationIso (markedBoxRectangleHalfTurnIso n)).injective
  exact ((markedBoxRectangleHalfTurn_configuration n (markedUpperBoxRawReveal n u v A)).trans
    ((congrArg (configurationIso (boxTubeRectangleIso n)) hUpper).trans hLower')).trans hcov'.symm


/-- The UNCHANGED joint box record is exactly the edge-defined raw source
record used by the proved stopped wired law, with neither completion. -/
theorem markedJointBoxRawReveal_eq_source_raw (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) :
    configurationIso (boxTubeRectangleIso n) (markedJointBoxRawReveal n u v A) =
      sourceMarkedRawReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (boxTubeRectangleIso n u) (boxTubeRectangleIso n v)
        (configurationIso (boxTubeRectangleIso n) A) := by
  classical
  unfold markedJointBoxRawReveal
  have hL : configurationIso (boxTubeRectangleIso n) (markedLowerBoxRawReveal n u v A) =
      sampledRawDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val)
        (configurationIso (boxTubeRectangleIso n) A) := by
    rw [sampledRawDualReveal_lower_arc_eq]
    exact (configurationIso (boxTubeRectangleIso n)).apply_symm_apply _
  have hU := markedUpperBoxRawReveal_eq_source_upper n u v A
  have hUnion : configurationIso (boxTubeRectangleIso n)
      (markedLowerBoxRawReveal n u v A ∪ markedUpperBoxRawReveal n u v A) =
      configurationIso (boxTubeRectangleIso n) (markedLowerBoxRawReveal n u v A) ∪
        configurationIso (boxTubeRectangleIso n) (markedUpperBoxRawReveal n u v A) := by
    exact Finset.map_union _ _
  have hSource := sourceMarkedRawReveal_eq_union (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    (boxTubeRectangleIso n u) (boxTubeRectangleIso n v) (configurationIso (boxTubeRectangleIso n) A)
  have hBoth := congrArg₂ (fun (B C : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))) => B ∪ C) hL hU
  exact hUnion.trans (hBoth.trans hSource.symm)


end
end PottsContinuity.Thm3.Prop4
