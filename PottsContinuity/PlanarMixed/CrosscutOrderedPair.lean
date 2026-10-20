module

public import PottsContinuity.PlanarMixed.CrosscutSeparation
public import PottsContinuity.PlanarMixed.OrderedCutBands
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! Construct the ordered-cut interface from actual square-crossing walks.
Both cut traces are the given supports, including every repeated boundary
contact. The bottom starting-point order and disjointness are the only
relative-position premises; no separation hypothesis is supplied.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PlanarTopology
noncomputable section

/-- The actual coordinate inclusion of the source square graph. -/
def originSquareToLattice (N : ℕ) : rectangleGraph (0,0) N N →g squareLattice where
  toFun := Subtype.val
  map_rel' := fun h => (rectangleGraph_adj_iff (0,0) N N _ _).mp h

@[simp] theorem originSquareToLattice_coe (N : ℕ) :
    (⇑(originSquareToLattice N) : RectangleVertex (0,0) N N → LatticeVertex) = Subtype.val := rfl

/-- Every original square walk maps inside the same closed coordinate square. -/
theorem originSquare_walk_bounds (N : ℕ) {u v : RectangleVertex (0,0) N N}
    (p : (rectangleGraph (0,0) N N).Walk u v) :
    ∀ z ∈ (p.map (originSquareToLattice N)).support,
      0 ≤ z.1 ∧ z.1 ≤ (N : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (N : ℤ) := by
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
  have h := (mem_latticeRectangle (0,0) w.val N N).mp w.property
  change 0 ≤ w.val.1 ∧ w.val.1 ≤ (N : ℤ) ∧ 0 ≤ w.val.2 ∧ w.val.2 ≤ (N : ℤ)
  dsimp at h
  omega

private theorem common_from_coordinate_supports (N : ℕ)
    {u v x y : RectangleVertex (0,0) N N}
    (p : (rectangleGraph (0,0) N N).Walk u v)
    (q : (rectangleGraph (0,0) N N).Walk x y)
    (h : ∃ z : LatticeVertex,
      z ∈ p.support.map Subtype.val ∧ z ∈ q.support.map Subtype.val) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  obtain ⟨z, hzP, hzQ⟩ := h
  obtain ⟨a, ha, haz⟩ := List.mem_map.mp hzP
  obtain ⟨b, hb, hbz⟩ := List.mem_map.mp hzQ
  have hab : a = b := Subtype.ext (haz.trans hbz.symm)
  exact ⟨a, ha, hab.symm ▸ hb⟩

/-- Disjoint bottom-to-top crossings with ordered bottom starts satisfy all
three walk-separation fields of OrderedCutPair on the ORIGINAL square graph. -/
theorem orderedCutPair_of_square_crosscuts (N : ℕ)
    {a b t u : RectangleVertex (0,0) N N}
    (p : (rectangleGraph (0,0) N N).Walk a t)
    (q : (rectangleGraph (0,0) N N).Walk b u)
    (ha : a.val.2 = 0) (hb : b.val.2 = 0)
    (ht : t.val.2 = (N : ℤ)) (hu : u.val.2 = (N : ℤ))
    (hab : a.val.1 < b.val.1)
    (hdis : ∀ z ∈ p.support, z ∉ q.support) :
    OrderedCutPair (rectangleGraph (0,0) N N)
      (Square.squareLeftArc (0,0) N) (Square.squareRightArc (0,0) N)
      {z | z ∈ p.support} {z | z ∈ q.support} := by
  classical
  let f := originSquareToLattice N
  let P : squareLattice.Walk (a.val.1,0) t.val :=
    (p.map f).copy (show f a = (a.val.1,0) from Prod.ext rfl ha) rfl
  let Q : squareLattice.Walk (b.val.1,0) u.val :=
    (q.map f).copy (show f b = (b.val.1,0) from Prod.ext rfl hb) rfl
  have hf : (⇑f : RectangleVertex (0,0) N N → LatticeVertex) = Subtype.val := rfl
  have hsP : P.support = p.support.map Subtype.val := by
    calc
      P.support = (p.map f).support := SimpleGraph.Walk.support_copy _ _ _
      _ = p.support.map Subtype.val := SimpleGraph.Walk.support_map _ _
  have hsQ : Q.support = q.support.map Subtype.val := by
    calc
      Q.support = (q.map f).support := SimpleGraph.Walk.support_copy _ _ _
      _ = q.support.map Subtype.val := SimpleGraph.Walk.support_map _ _
  have hP : ∀ z ∈ P.support,
      0 ≤ z.1 ∧ z.1 ≤ (N : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (N : ℤ) := by
    intro z hz
    have hm : (p.map (originSquareToLattice N)).support =
        p.support.map Subtype.val := SimpleGraph.Walk.support_map _ _
    exact originSquare_walk_bounds N p z (hm.symm ▸ (hsP ▸ hz))
  have hQ : ∀ z ∈ Q.support,
      0 ≤ z.1 ∧ z.1 ≤ (N : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (N : ℤ) := by
    intro z hz
    have hm : (q.map (originSquareToLattice N)).support =
        q.support.map Subtype.val := SimpleGraph.Walk.support_map _ _
    exact originSquare_walk_bounds N q z (hm.symm ▸ (hsQ ▸ hz))
  have hPQ : ∀ z ∈ P.support, z ∉ Q.support := by
    intro z hzP hzQ
    obtain ⟨w, hwp, hwq⟩ := common_from_coordinate_supports N p q
      ⟨z, hsP ▸ hzP, hsQ ▸ hzQ⟩
    exact hdis w hwp hwq
  refine ⟨Set.disjoint_left.mpr hdis, ?_, ?_, ?_⟩
  · intro l hl r hr R
    have hl' : l.val.1 = 0 := hl
    have hr' : r.val.1 = (N : ℤ) := by
      simpa only [Square.squareRightArc, Set.mem_ofPred_eq, Prod.fst, zero_add] using hr
    have hc := rectangle_walks_common_vertex (R.map f) P
      (by omega : (0 : ℤ) ≤ N) (by omega : (0 : ℤ) ≤ N)
      (originSquare_walk_bounds N R) hP hl' hr' rfl ht
    apply common_from_coordinate_supports N R p
    simpa only [hsP, SimpleGraph.Walk.support_map, originSquareToLattice_coe, hf] using hc
  · intro l hl c hc R
    have hcin : c.val ∈ Q.support := by
      rw [hsQ]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    have h := crosscuts_left_to_second_hits_first (N : ℤ) (by omega)
      a.val.1 b.val.1 P Q hab hP hQ ht hu hPQ (R.map f) hl hcin
      (originSquare_walk_bounds N R)
    apply common_from_coordinate_supports N R p
    simpa only [hsP, SimpleGraph.Walk.support_map, originSquareToLattice_coe, hf] using h
  · intro c hc r hr R
    have hcin : c.val ∈ P.support := by
      rw [hsP]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    have hr' : r.val.1 = (N : ℤ) := by
      simpa only [Square.squareRightArc, Set.mem_ofPred_eq, Prod.fst, zero_add] using hr
    have h := crosscuts_first_to_right_hits_second (N : ℤ) (by omega)
      a.val.1 b.val.1 P Q hab hP hQ ht hu hPQ (R.map f) hcin hr'
      (originSquare_walk_bounds N R)
    apply common_from_coordinate_supports N R q
    simpa only [hsQ, SimpleGraph.Walk.support_map, originSquareToLattice_coe, hf] using h

end
end PottsContinuity.PlanarMixed
