module

public import PottsContinuity.Thm4Plane.ScreenTargetCap

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC.FiniteFK

theorem screenTargetCap_bottomCenter_mem (m : ℕ) :
    slitBoxBottomCenterVertex (16 * m) ∈ screenTargetCap m := by
  simp [screenTargetCap, slitBoxBottomCenterVertex]
  omega

/-- The truncated `E` witness remains a path in the open graph induced on any
vertex set containing the clipped target cap. This separates path containment
from the still-needed proof that the screen arch selects such an interior. -/
theorem generalEScreenEvent_has_path_in_any_induced_cap_domain
    (m : ℕ) (A : Configuration (slitBoxGraph (16 * m)))
    (hE : A ∈ generalEScreenEvent (16 * m))
    (D : Set (SlitBoxVertex (16 * m)))
    (hcap : screenTargetCap m ⊆ D) :
    ∃ v : D, v.val ∈ screenTargetCap m ∧
      (|v.val.val.1| = (m : ℤ) ∨
        v.val.val.2 = -(15 * (m : ℤ))) ∧
      Nonempty (((openGraph (slitBoxGraph (16 * m)) A).induce D).Walk
        ⟨slitBoxBottomCenterVertex (16 * m),
          hcap (screenTargetCap_bottomCenter_mem m)⟩ v) := by
  obtain ⟨v, hvCap, hvExit, p, hsupport⟩ :=
    generalEScreenEvent_has_path_in_screenTargetCap m A hE
  refine ⟨⟨v, hcap hvCap⟩, hvCap, hvExit, ⟨?_⟩⟩
  exact p.induce D (fun z hz => hcap (hsupport z hz))

end PottsContinuity.Thm4Plane
