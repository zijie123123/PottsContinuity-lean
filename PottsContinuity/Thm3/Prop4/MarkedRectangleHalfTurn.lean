module

public import PottsContinuity.Thm3.Prop4.RawLowerFrontierFit

/-! # Coordinate-faithful half-turn of rectangles and their sampled faces -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- The actual lower-left corner after rotating an original rectangle by pi. -/
def markedHalfTurnAnchor (a : LatticeVertex) (w h : ℕ) : LatticeVertex :=
  (-a.1-(w : ℤ),-a.2-(h : ℤ))

/-- Actual primal vertices rotate by negation, with no translation error. -/
def markedRectangleHalfTurnIso (a : LatticeVertex) (w h : ℕ) :
    rectangleGraph a w h ≃g rectangleGraph (markedHalfTurnAnchor a w h) w h where
  toEquiv := {
    toFun x := ⟨-x.val,by
      have hx := (PD.FK.mem_latticeRectangle a x.val w h).mp x.property
      rw [PD.FK.mem_latticeRectangle]
      dsimp [markedHalfTurnAnchor]
      exact ⟨⟨by omega,by omega⟩,by omega,by omega⟩⟩
    invFun x := ⟨-x.val,by
      have hx := (PD.FK.mem_latticeRectangle (markedHalfTurnAnchor a w h) x.val w h).mp x.property
      dsimp [markedHalfTurnAnchor] at hx
      rw [PD.FK.mem_latticeRectangle]
      dsimp
      exact ⟨⟨by omega,by omega⟩,by omega,by omega⟩⟩
    left_inv x := by apply Subtype.ext; exact neg_neg x.val
    right_inv x := by apply Subtype.ext; exact neg_neg x.val }
  map_rel_iff' := by
    intro x y
    rw [rectangleGraph_adj_iff,rectangleGraph_adj_iff,squareLattice_adj_iff,squareLattice_adj_iff]
    dsimp
    omega

/-- A dual face base rotates about its face center, not its lower-left corner. -/
def markedFaceHalfTurn (f : LatticeVertex) : LatticeVertex := (-f.1-1,-f.2-1)

/-- The dual face transformation is an actual involution. -/
theorem markedFaceHalfTurn_involutive : Function.Involutive markedFaceHalfTurn := by
  intro f
  apply Prod.ext <;> dsimp [markedFaceHalfTurn] <;> omega

/-- A primal sampled bond rotates with its literal lower-left endpoint convention. -/
def markedBondHalfTurn (b : LatticeBond) : LatticeBond :=
  match b.axis with
  | .horizontal => ⟨(-b.base.1-1,-b.base.2),.horizontal⟩
  | .vertical => ⟨(-b.base.1,-b.base.2-1),.vertical⟩

/-- The original unordered edge under the half-turn is the exact rotated bond. -/
theorem markedBondHalfTurn_toSym2 (b : LatticeBond) :
    (markedBondHalfTurn b).toSym2 = b.toSym2.map (fun x => -x) := by
  cases b with
  | mk base axis =>
    cases base with
    | mk x y =>
      cases axis <;>
        simp only [markedBondHalfTurn,LatticeBond.toSym2,LatticeBond.source,LatticeBond.target,Sym2.map_mk]
      all_goals apply Sym2.eq_iff.mpr; right; constructor <;> apply Prod.ext <;> dsimp <;> omega

/-- The two incident face labels swap sides under the original bond half-turn. -/
theorem markedBondHalfTurn_faceBase (b : LatticeBond) (side : Bool) :
    (markedBondHalfTurn b).faceBase (!side) = markedFaceHalfTurn (b.faceBase side) := by
  cases b with
  | mk base axis =>
    cases base with
    | mk x y =>
      cases axis <;> cases side <;> simp only [Bool.not_false,Bool.not_true] <;> apply Prod.ext <;>
        dsimp [markedBondHalfTurn,LatticeBond.faceBase,markedFaceHalfTurn] <;> omega

/-- Original primal vertex coordinates are exactly negated. -/
theorem markedRectangleHalfTurnIso_val (a : LatticeVertex) (w h : ℕ)
    (x : RectangleVertex a w h) : (markedRectangleHalfTurnIso a w h x).val = -x.val := rfl

/-- The lower exterior arc at the rotated exchanged marks is exactly the
half-turn of the original upper exterior arc, including corner endpoints. -/
theorem markedFaceHalfTurn_lower_arc_iff (a : LatticeVertex) (w h : ℕ)
    (u v f : LatticeVertex) :
    markedFaceHalfTurn f ∈ PlanarTopology.rectangleLowerDualArc (markedHalfTurnAnchor a w h) w h (-v) (-u) ↔
      f ∈ PlanarTopology.rectangleUpperDualArc a w h u v := by
  dsimp [markedFaceHalfTurn,markedHalfTurnAnchor,PlanarTopology.rectangleLowerDualArc,
    PlanarTopology.rectangleUpperDualArc]
  omega

end
end PottsContinuity.Thm3.Prop4

