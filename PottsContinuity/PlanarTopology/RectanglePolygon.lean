module

public import PottsContinuity.FKC.Domains.LatticePolygon
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- Every boundary vertex of the integer rectangle, in cyclic unit-step order.
The four half-open pieces are bottom, right, top, and left. -/
def rectanglePolygonVertex (a : FKC.LatticeVertex) (w h : ℕ)
    (_hw : 1 ≤ w) (_hh : 1 ≤ h)
    (i : ZMod ((2*w+2*h-3)+3)) : FKC.LatticeVertex :=
  let j := i.val
  if j < w then (a.1 + (j : ℤ), a.2)
  else if j < w+h then (a.1+(w : ℤ), a.2+((j-w : ℕ) : ℤ))
  else if j < 2*w+h then (a.1+((2*w+h-j : ℕ) : ℤ), a.2+(h : ℤ))
  else (a.1, a.2+((2*w+2*h-j : ℕ) : ℤ))

/-- Nondegenerate integer rectangles give actual unit-edge lattice polygons,
retaining all collinear intermediate boundary vertices. -/
def rectangleLatticePolygon (a : FKC.LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) : FKC.LatticePolygon (2*w+2*h-3) where
  vertex := rectanglePolygonVertex a w h hw hh
  vertex_injective := by
    let : NeZero ((2*w+2*h-3)+3) := ⟨by omega⟩
    intro i j hij
    have hi := ZMod.val_lt i
    have hj := ZMod.val_lt j
    apply ZMod.val_injective
    simp only [rectanglePolygonVertex] at hij
    split_ifs at hij <;> simp only [Prod.mk.injEq] at hij <;> omega
  adjacent := by
    let : NeZero ((2*w+2*h-3)+3) := ⟨by omega⟩
    intro i
    have hi := ZMod.val_lt i
    have hn : (2*w+2*h-3)+3 = 2*w+2*h := by omega
    have hnext : (i+1).val = if i.val+1 < 2*w+2*h then i.val+1 else 0 := by
      rw [ZMod.val_add]
      have hone : (1 : ZMod ((2*w+2*h-3)+3)).val = 1 := by
        have : Fact (1 < (2*w+2*h-3)+3) := ⟨by omega⟩
        exact ZMod.val_one _
      rw [hone]
      conv_lhs => arg 2; rw [hn]
      split_ifs with hlt
      · exact Nat.mod_eq_of_lt hlt
      · have he : i.val+1 = 2*w+2*h := by omega
        rw [he,Nat.mod_self]
    rw [FKC.squareLattice_adj_iff]
    simp only [rectanglePolygonVertex,hnext]
    split_ifs <;> dsimp only [Prod.fst,Prod.snd] <;> omega

/-- The unit-step cyclic list exhausts exactly the literal rectangle's lattice boundary. -/
theorem mem_rectanglePolygon_vertices_iff (a : FKC.LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (z : FKC.LatticeVertex) :
    (∃ i, (rectangleLatticePolygon a w h hw hh).vertex i = z) ↔
      a.1 ≤ z.1 ∧ z.1 ≤ a.1+(w : ℤ) ∧ a.2 ≤ z.2 ∧ z.2 ≤ a.2+(h : ℤ) ∧
      (z.1 = a.1 ∨ z.1 = a.1+(w : ℤ) ∨ z.2 = a.2 ∨ z.2 = a.2+(h : ℤ)) := by
  let : NeZero ((2*w+2*h-3)+3) := ⟨by omega⟩
  change (∃ i, rectanglePolygonVertex a w h hw hh i = z) ↔ _
  constructor
  · rintro ⟨i,hi⟩
    have hib := ZMod.val_lt i
    simp only [rectanglePolygonVertex] at hi
    split_ifs at hi <;>
      have hx := congrArg Prod.fst hi <;>
      have hy := congrArg Prod.snd hi <;>
      dsimp only [Prod.fst, Prod.snd] at hx hy <;> omega
  · intro hz
    by_cases hy0 : z.2 = a.2
    · let j := (z.1-a.1).toNat
      have hj : j < (2*w+2*h-3)+3 := by dsimp [j]; omega
      refine ⟨(j : ZMod ((2*w+2*h-3)+3)), ?_⟩
      have hjval : (j : ZMod ((2*w+2*h-3)+3)).val = j := ZMod.val_natCast_of_lt hj
      simp only [rectanglePolygonVertex,hjval]
      split_ifs <;> apply Prod.ext <;> dsimp [j] at * <;> omega
    · by_cases hx1 : z.1 = a.1+(w : ℤ)
      · let j := w+(z.2-a.2).toNat
        have hj : j < (2*w+2*h-3)+3 := by dsimp [j]; omega
        refine ⟨(j : ZMod ((2*w+2*h-3)+3)), ?_⟩
        have hjval : (j : ZMod ((2*w+2*h-3)+3)).val = j := ZMod.val_natCast_of_lt hj
        simp only [rectanglePolygonVertex,hjval]
        split_ifs <;> apply Prod.ext <;> dsimp [j] at * <;> omega
      · by_cases hy1 : z.2 = a.2+(h : ℤ)
        · let j := w+h+(a.1+(w : ℤ)-z.1).toNat
          have hj : j < (2*w+2*h-3)+3 := by dsimp [j]; omega
          refine ⟨(j : ZMod ((2*w+2*h-3)+3)), ?_⟩
          have hjval : (j : ZMod ((2*w+2*h-3)+3)).val = j := ZMod.val_natCast_of_lt hj
          simp only [rectanglePolygonVertex,hjval]
          split_ifs <;> apply Prod.ext <;> dsimp [j] at * <;> omega
        · have hx0 : z.1 = a.1 := by omega
          let j := 2*w+h+(a.2+(h : ℤ)-z.2).toNat
          have hj : j < (2*w+2*h-3)+3 := by dsimp [j]; omega
          refine ⟨(j : ZMod ((2*w+2*h-3)+3)), ?_⟩
          have hjval : (j : ZMod ((2*w+2*h-3)+3)).val = j := ZMod.val_natCast_of_lt hj
          simp only [rectanglePolygonVertex,hjval]
          split_ifs <;> apply Prod.ext <;> dsimp [j] at * <;> omega

end PottsContinuity.PlanarTopology
