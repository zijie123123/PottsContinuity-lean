module

public import PottsContinuity.Thm3.RSW.SquareSymmetry

/-!
# The actual reflected-pair step of Proposition 3

DCST TeX line 1533. Reflection, free-domain comparison and FKG give the
square of an opposite-square-side pair probability below the probability
of the corresponding symmetric pair in the doubled rectangle. This works
at every interior parameter and every real q≥1.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- Reflect the standard square through its left side. -/
def pairReflectionIso (m : ℕ) :
    (squareLattice.induce (latticeRectangle 0 m 0 m : Set (ℤ × ℤ))) ≃g
      squareLattice.induce (latticeRectangle (-(m:ℤ)) 0 0 m : Set (ℤ × ℤ)) where
  toEquiv :=
    { toFun := fun v => ⟨(-v.val.1,v.val.2), by
        have hv := v.property
        simp only [latticeRectangle, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc] at hv ⊢
        omega⟩
      invFun := fun v => ⟨(-v.val.1,v.val.2), by
        have hv := v.property
        simp only [latticeRectangle, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc] at hv ⊢
        omega⟩
      left_inv := by intro v; apply Subtype.ext; simp
      right_inv := by intro v; apply Subtype.ext; simp }
  map_rel_iff' := by
    intro u v
    change |-u.val.1 - -v.val.1| + |u.val.2-v.val.2| = 1 ↔
      |u.val.1-v.val.1| + |u.val.2-v.val.2| = 1
    rw [neg_sub_neg, abs_sub_comm v.val.1 u.val.1]

/-- Free actual finite connection probability increases with the domain. -/
theorem finite_free_connection_probability_mono (θ : Parameters)
    (V W : Finset (ℤ × ℤ)) (hVW : V ⊆ W) (x y : ℤ × ℤ)
    (hx : x ∈ V) (hy : y ∈ V) :
    finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
      (fun ω => ω ∈ finiteConnectionEvent V x y) ≤
    finiteBoundaryEventProbability W θ (frozenBoundaryCondition W 0)
      (fun ω => ω ∈ finiteConnectionEvent W x y) := by
  rw [finite_free_connection_probability_eq θ V x y hx hy,
    finite_free_connection_probability_eq θ W x y (hVW hx) (hVW hy)]
  let f : (V:Set (ℤ × ℤ)) ↪ (W:Set (ℤ × ℤ)) :=
    ⟨fun v => ⟨v.val,hVW v.property⟩, fun a b h => Subtype.ext (congrArg (fun z : (W:Set (ℤ × ℤ)) => z.val) h)⟩
  have hmap : (squareLattice.induce (V:Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (W:Set (ℤ × ℤ)) := by
    intro a b hab
    obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj f _ a b).mp hab
    exact huv
  exact embedded_free_connection_probability_le_allq f hmap θ ⟨x,hx⟩ ⟨y,hy⟩

/-- The first reflected-FKG inequality of Proposition 3, in an equivalent
squared form. Boundary wiring creates no virtual connection in any event. -/
theorem squarePair_probability_sq_le_reflected_connection (θ : Parameters)
    (m : ℕ) (i j : Fin (m+1)) :
    (squarePairProbability θ m i j)^2 ≤
      finiteBoundaryEventProbability (latticeRectangle (-(m:ℤ)) m 0 m) θ
        (frozenBoundaryCondition (latticeRectangle (-(m:ℤ)) m 0 m) 0)
        (fun ω => ω ∈ finiteConnectionEvent (latticeRectangle (-(m:ℤ)) m 0 m)
          (-(m:ℤ),(j.val:ℤ)) ((m:ℤ),(j.val:ℤ))) := by
  let V := latticeRectangle 0 m 0 m
  let L := latticeRectangle (-(m:ℤ)) 0 0 m
  let W := latticeRectangle (-(m:ℤ)) m 0 m
  let x : ℤ × ℤ := (0,(i.val:ℤ))
  let y : ℤ × ℤ := ((m:ℤ),(j.val:ℤ))
  let z : ℤ × ℤ := (-(m:ℤ),(j.val:ℤ))
  have hxV : x ∈ V := by
    simp only [V,x,latticeRectangle,Finset.mem_product,Finset.mem_Icc]; omega
  have hyV : y ∈ V := by
    simp only [V,y,latticeRectangle,Finset.mem_product,Finset.mem_Icc]; omega
  have hxL : x ∈ L := by
    simp only [L,x,latticeRectangle,Finset.mem_product,Finset.mem_Icc]; omega
  have hzL : z ∈ L := by
    simp only [L,z,latticeRectangle,Finset.mem_product,Finset.mem_Icc]; omega
  have hVW : V ⊆ W := by
    intro v hv
    simp only [V,W,latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hv ⊢
    omega
  have hLW : L ⊆ W := by
    intro v hv
    simp only [L,W,latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hv ⊢
    omega
  let G := squareLattice.induce (W:Set (ℤ × ℤ))
  let xW : (W:Set (ℤ × ℤ)) := ⟨x,hVW hxV⟩
  let yW : (W:Set (ℤ × ℤ)) := ⟨y,hVW hyV⟩
  let zW : (W:Set (ℤ × ℤ)) := ⟨z,hLW hzL⟩
  let ρ := measure G θ (BoundaryCondition.free ∅)
  let E : Set (Configuration G) := {A | ActualConnected G A xW zW}
  let F : Set (Configuration G) := {A | ActualConnected G A xW yW}
  have hreflect : squarePairProbability θ m i j =
      finiteBoundaryEventProbability L θ (frozenBoundaryCondition L 0)
        (fun ω => ω ∈ finiteConnectionEvent L x z) := by
    rw [squarePairProbability, finite_free_connection_probability_eq θ V x y hxV hyV,
      finite_free_connection_probability_eq θ L x z hxL hzL]
    exact free_connection_probability_eq_of_iso θ (pairReflectionIso m) ⟨x,hxV⟩ ⟨y,hyV⟩
  have hE : squarePairProbability θ m i j ≤ (ρ E).toReal := by
    rw [hreflect]
    have h := finite_free_connection_probability_mono θ L W hLW x z hxL hzL
    rw [finite_free_connection_probability_eq θ W x z (hLW hxL) (hLW hzL)] at h
    exact h
  have hF : squarePairProbability θ m i j ≤ (ρ F).toReal := by
    have h := finite_free_connection_probability_mono θ V W hVW x y hxV hyV
    rw [finite_free_connection_probability_eq θ W x y (hVW hxV) (hVW hyV)] at h
    exact h
  rw [finite_free_connection_probability_eq θ W z y (hLW hzL) (hVW hyV)]
  calc
    (squarePairProbability θ m i j)^2 ≤ (ρ E).toReal*(ρ F).toReal := by
      rw [pow_two]
      exact mul_le_mul hE hF (squarePairProbability_nonneg θ m i j) ENNReal.toReal_nonneg
    _ ≤ (ρ (E ∩ F)).toReal := measure_positive_association θ _ E F
      (fun _ _ h hA => actualConnected_mono h hA)
      (fun _ _ h hA => actualConnected_mono h hA)
    _ ≤ _ := measureReal_mono (fun _ h => h.1.symm.trans h.2)

end
end PottsContinuity.RSW
