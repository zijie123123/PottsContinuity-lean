-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/WindingReparam.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.Winding
public import PottsContinuity.FKC.Curves.Ordered

/-!
# Winding number is independent of the speed of traversal

The winding number of an arbitrary continuous closed plane path is unchanged
by every continuous endpoint-preserving reparameterization of the unit interval.
In particular, it is invariant under the increasing homeomorphisms of the unit
interval (`IncreasingReparametrization` in `FKC.Curves.Ordered`). No smoothness or
finite-length premise is needed. That a Jordan loop has winding number plus or
minus one throughout its interior is proved in `FKC.Domains.JordanWinding`
(`windingNumber_jordan_interior_sign`).
-/

@[expose] public section

namespace PottsContinuity.FKC

open scoped unitInterval

/-- Normalizing radially commutes with a continuous change of the path parameter. -/
theorem normalizedLoop_reparam {a : ℂ} (γ : Path a a) (z : ℂ)
    (hz : z ∉ Set.range γ) (f : I → I) (hf : Continuous f)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) :
    normalizedLoop (γ.reparam f hf hf0 hf1) z
        (by simpa only [Path.range_reparam] using hz) =
      (normalizedLoop γ z hz).reparam f hf hf0 hf1 := by
  ext t
  rfl

/-- A continuous endpoint-preserving reparameterization has the same winding number. -/
theorem windingNumber_reparam {a : ℂ} (γ : Path a a) (z : ℂ)
    (hz : z ∉ Set.range γ) (f : I → I) (hf : Continuous f)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) :
    windingNumber (γ.reparam f hf hf0 hf1) z
        (by simpa only [Path.range_reparam] using hz) = windingNumber γ z hz := by
  unfold windingNumber
  rw [normalizedLoop_reparam]
  exact (Circle.degree_eq_of_homotopic
    ⟨Path.Homotopy.reparam (normalizedLoop γ z hz) f hf hf0 hf1⟩).symm

end PottsContinuity.FKC
