module

public import PottsContinuity.PlanarMixed.Square.WiredArcSquare
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.CompletePartialOrder

/-!
# Translated, rotated and odd-side dual-label square wired-arc estimates

All squares here are genuine induced nearest-neighbour graphs. Dual vertices
are labelled by integers and physically embedded at label+(1/2,1/2), so the
Lemma 4 square R* has lower-left label (-3n,-3n) and side length 6n-1.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.Duality BD12
noncomputable section

/-- Isomorphism transport preserves ACTUAL sampled arc connectivity. -/
theorem arcsConnectionEvent_iso_preimage {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (A B : Set V) :
    (configurationIso e) ⁻¹' arcsConnectionEvent H (e '' A) (e '' B) =
      arcsConnectionEvent G A B := by
  ext C
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, hc⟩
    exact ⟨u, hu, v, hv, (actualConnected_configurationIso e C u v).mp hc⟩
  · rintro ⟨u, hu, v, hv, hc⟩
    exact ⟨e u, ⟨u, hu, rfl⟩, e v, ⟨v, hv, rfl⟩,
      (actualConnected_configurationIso e C u v).mpr hc⟩

/-- Literal integer translation from the origin square, retaining all vertices. -/
def squareTranslationIso (a : LatticeVertex) (N : ℕ) :
    rectangleGraph (0,0) N N ≃g rectangleGraph a N N where
  toEquiv := {
    toFun := fun v => ⟨latticeTranslate a v.val, by
      have hv := (mem_latticeRectangle (0,0) v.val N N).mp v.property
      rw [mem_latticeRectangle]
      dsimp [latticeTranslate]
      constructor <;> constructor <;> omega⟩
    invFun := fun v => ⟨latticeTranslate (-a) v.val, by
      have hv := (mem_latticeRectangle a v.val N N).mp v.property
      rw [mem_latticeRectangle]
      dsimp [latticeTranslate]
      constructor <;> constructor <;> omega⟩
    left_inv := fun v => Subtype.ext (latticeTranslate_neg_cancel a v.val)
    right_inv := by
      intro v
      apply Subtype.ext
      ext <;> dsimp [latticeTranslate] <;> omega }
  map_rel_iff' := by
    intro u v
    exact squareLattice_adj_translate_iff a u.val v.val

theorem squareTranslation_image_bottom (a : LatticeVertex) (N : ℕ) :
    squareTranslationIso a N '' rectangleDoubleCollarInnerBottom (0,0) N N =
      rectangleDoubleCollarInnerBottom a N N := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    change u.val.2 = 0 at hu
    change u.val.2 + a.2 = a.2
    omega
  · intro hv
    let e := squareTranslationIso a N
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    change v.val.2 = a.2 at hv
    change v.val.2 + -a.2 = 0
    omega

theorem squareTranslation_image_top (a : LatticeVertex) (N : ℕ) :
    squareTranslationIso a N '' rectangleDoubleCollarInnerTop (0,0) N N =
      rectangleDoubleCollarInnerTop a N N := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    change u.val.2 = 0+(N:ℤ) at hu
    change u.val.2 + a.2 = a.2+(N:ℤ)
    omega
  · intro hv
    let e := squareTranslationIso a N
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    change v.val.2 = a.2+(N:ℤ) at hv
    change v.val.2 + -a.2 = 0+(N:ℤ)
    omega

/-- Equality of the sets transports a two-block boundary, independently of
which proof of their disjointness is supplied. -/
theorem twoBlockBoundary_set_congr {V : Type*} [Finite V]
    {A A' B B' : Set V} (hA : A = A') (hB : B = B')
    (hAB : Disjoint A B) (hA'B' : Disjoint A' B') :
    twoBlockBoundary A B hAB = twoBlockBoundary A' B' hA'B' := by
  subst A'
  subst B'
  rfl

/-- The actual separately wired bottom/top connection bound on EVERY integer
translate of a square, for EVERY real q>=1 at the explicit self-dual point. -/
theorem square_wiredBottomTop_lower_bound
    (q : Set.Ici (1 : ℝ)) (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N) :
    1/(1+(q:ℝ)^2) ≤
    (measure (rectangleGraph a N N) (criticalParameters q)
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom a N N)
        (rectangleDoubleCollarInnerTop a N N)
        (rectangleDoubleCollarInnerBottom_disjoint_top a N N hN))
      (arcsConnectionEvent (rectangleGraph a N N)
        (rectangleDoubleCollarInnerBottom a N N) (rectangleDoubleCollarInnerTop a N N))).toReal := by
  let e := squareTranslationIso a N
  have ht := measure_event_configurationIso (criticalParameters q) e
    (twoBlockBoundary (rectangleDoubleCollarInnerBottom (0,0) N N)
      (rectangleDoubleCollarInnerTop (0,0) N N)
      (rectangleDoubleCollarInnerBottom_disjoint_top (0,0) N N hN))
    _ _ (arcsConnectionEvent_iso_preimage e
      (rectangleDoubleCollarInnerBottom (0,0) N N) (rectangleDoubleCollarInnerTop (0,0) N N))
  have hbd : boundaryConditionIso e
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom (0,0) N N)
        (rectangleDoubleCollarInnerTop (0,0) N N)
        (rectangleDoubleCollarInnerBottom_disjoint_top (0,0) N N hN)) =
      twoBlockBoundary (rectangleDoubleCollarInnerBottom a N N)
        (rectangleDoubleCollarInnerTop a N N)
        (rectangleDoubleCollarInnerBottom_disjoint_top a N N hN) := by
    rw [boundaryConditionIso_twoBlock_image]
    exact twoBlockBoundary_set_congr (squareTranslation_image_bottom a N)
      (squareTranslation_image_top a N) _ _
  have hEvent : arcsConnectionEvent (rectangleGraph a N N)
      (e '' rectangleDoubleCollarInnerBottom (0,0) N N)
      (e '' rectangleDoubleCollarInnerTop (0,0) N N) =
      arcsConnectionEvent (rectangleGraph a N N)
        (rectangleDoubleCollarInnerBottom a N N) (rectangleDoubleCollarInnerTop a N N) := by
    dsimp only [e]
    rw [squareTranslation_image_bottom, squareTranslation_image_top]
  rw [hbd, hEvent] at ht
  rw [← ht]
  exact square_separate_wiredBottomTop_connection_lower q 0 N hN

/-- The full left side of an induced square, corners included. -/
def squareLeftArc (a : LatticeVertex) (N : ℕ) : Set (RectangleVertex a N N) :=
  {v | v.val.1 = a.1}

/-- The full right side of an induced square, corners included. -/
def squareRightArc (a : LatticeVertex) (N : ℕ) : Set (RectangleVertex a N N) :=
  {v | v.val.1 = a.1+(N:ℤ)}

theorem squareLeftArc_disjoint_right (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N) :
    Disjoint (squareLeftArc a N) (squareRightArc a N) := by
  apply Set.disjoint_left.mpr
  intro v hvL hvR
  change v.val.1 = a.1 at hvL
  change v.val.1 = a.1+(N:ℤ) at hvR
  omega

theorem squareSwap_image_left (a : LatticeVertex) (N : ℕ) :
    rectangleGraphCoordinateSwapIso a N N '' squareLeftArc a N =
      rectangleDoubleCollarInnerBottom (latticeCoordinateSwap a) N N := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hv
    let e := rectangleGraphCoordinateSwapIso a N N
    exact ⟨e.symm v, hv, e.apply_symm_apply v⟩

theorem squareSwap_image_right (a : LatticeVertex) (N : ℕ) :
    rectangleGraphCoordinateSwapIso a N N '' squareRightArc a N =
      rectangleDoubleCollarInnerTop (latticeCoordinateSwap a) N N := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hv
    let e := rectangleGraphCoordinateSwapIso a N N
    exact ⟨e.symm v, hv, e.apply_symm_apply v⟩

/-- The rotated WIRED-ARC square bound: the separate left and right classes
are joined by an actual sampled open path with probability at least 1/(1+q²). -/
theorem square_wiredLeftRight_lower_bound
    (q : Set.Ici (1 : ℝ)) (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N) :
    1/(1+(q:ℝ)^2) ≤
    (measure (rectangleGraph a N N) (criticalParameters q)
      (twoBlockBoundary (squareLeftArc a N) (squareRightArc a N)
        (squareLeftArc_disjoint_right a N hN))
      (arcsConnectionEvent (rectangleGraph a N N) (squareLeftArc a N) (squareRightArc a N))).toReal := by
  let e := rectangleGraphCoordinateSwapIso a N N
  have ht := measure_event_configurationIso (criticalParameters q) e
    (twoBlockBoundary (squareLeftArc a N) (squareRightArc a N)
      (squareLeftArc_disjoint_right a N hN))
    _ _ (arcsConnectionEvent_iso_preimage e (squareLeftArc a N) (squareRightArc a N))
  have hbd : boundaryConditionIso e
      (twoBlockBoundary (squareLeftArc a N) (squareRightArc a N)
        (squareLeftArc_disjoint_right a N hN)) =
      twoBlockBoundary (rectangleDoubleCollarInnerBottom (latticeCoordinateSwap a) N N)
        (rectangleDoubleCollarInnerTop (latticeCoordinateSwap a) N N)
        (rectangleDoubleCollarInnerBottom_disjoint_top (latticeCoordinateSwap a) N N hN) := by
    rw [boundaryConditionIso_twoBlock_image]
    exact twoBlockBoundary_set_congr (squareSwap_image_left a N) (squareSwap_image_right a N) _ _
  have hEvent : arcsConnectionEvent (rectangleGraph (latticeCoordinateSwap a) N N)
      (e '' squareLeftArc a N) (e '' squareRightArc a N) =
      arcsConnectionEvent (rectangleGraph (latticeCoordinateSwap a) N N)
        (rectangleDoubleCollarInnerBottom (latticeCoordinateSwap a) N N)
        (rectangleDoubleCollarInnerTop (latticeCoordinateSwap a) N N) := by
    dsimp only [e]
    rw [squareSwap_image_left, squareSwap_image_right]
  rw [hbd, hEvent] at ht
  rw [ht]
  exact square_wiredBottomTop_lower_bound q (latticeCoordinateSwap a) N hN

end
end PottsContinuity.PlanarMixed.Square
