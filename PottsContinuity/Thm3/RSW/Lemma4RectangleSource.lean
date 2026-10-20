module

public import PottsContinuity.Thm3.RSW.Lemma4DualBands
public import PottsContinuity.Thm3.RSW.FiniteIso
public import PottsContinuity.Foundations.BoxBoundary

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section

/-- The source ambient box is the literal canonical rectangle with these
corners, at every scale including zero. -/
theorem lemma4AmbientRectangle_set_eq (n : ℕ) :
    box (56*n) = PD.FK.latticeRectangle (-56*(n:ℤ),-56*(n:ℤ)) (112*n) (112*n) := by
  ext v
  rw [Foundations.mem_box_iff_interval,mem_latticeRectangle]
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  omega

/-- Coordinate-preserving isomorphism from the exact source box carrier to
the canonical rectangle used by conditioned finite duality. -/
def lemma4AmbientRectangleIso (n : ℕ) :
    lemma4AmbientGraph n ≃g rectangleGraph (-56*(n:ℤ),-56*(n:ℤ)) (112*n) (112*n) where
  toEquiv :=
    { toFun := fun v => ⟨v.val,by rw [← lemma4AmbientRectangle_set_eq]; exact v.property⟩
      invFun := fun v => ⟨v.val,by rw [lemma4AmbientRectangle_set_eq]; exact v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

/-- The actual source B-n event on canonical rectangle samples, decoded by
the unique coordinate-preserving original-bond relabeling. -/
def lemma4RectangleBandEvent (n : ℕ) :
    Set (Configuration (rectangleGraph (-56*(n:ℤ),-56*(n:ℤ)) (112*n) (112*n))) :=
  (configurationIso (lemma4AmbientRectangleIso n)).symm ⁻¹' lemma4BandConstructionEvent n

end
end PottsContinuity.RSW
