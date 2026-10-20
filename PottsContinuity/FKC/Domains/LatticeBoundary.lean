-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeBoundary.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticePolygon
public import PottsContinuity.FKC.Domains.MarkedPolygonBoundary

/-!
# Marked lattice boundary parametrizations in the complex plane

The actual embedded lattice polygon has a continuous simple closed boundary
parametrization placing two prescribed cyclic vertices at zero and one-half.
Its two closed half-intervals have exactly the complementary forward arcs as
their images. Forward refers to the supplied cyclic vertex order. A
counterclockwise marked parametrization, whose half-arcs are these arcs or the
two arcs exchanged, is constructed in `FKC.Domains.MarkedPolygonOrientation`
(`LatticePolygon.exists_markedBoundaryParametrization_arc_pair`). No particular
parametrization is selected and no constant-speed condition is imposed.
-/

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open Set OAI.SLEExactGauge

/-- A genuine complex-valued boundary loop with two marked vertices and exact
half-arc images. The only assumptions are the polygon and a valid cyclic split. -/
theorem exists_marked_boundary_loop {m k : ℕ} (P : LatticePolygon m)
    (δ : PositiveMesh) (a : ZMod (m + 3)) (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    ∃ β : ℝ → ℂ,
      ContinuousOn β (Icc 0 1) ∧ InjOn β (Ico 0 1) ∧
      β 0 = latticeEmbed δ (P.vertex a) ∧
      β (1 / 2) = latticeEmbed δ (P.vertex (a + k)) ∧ β 1 = β 0 ∧
      β '' Icc 0 1 = P.carrier δ ∧
      complexPlaneCoordinates '' (β '' Icc 0 (1 / 2)) = (P.toPrePolygon δ).arc a k ∧
      complexPlaneCoordinates '' (β '' Icc (1 / 2) 1) =
        (P.toPrePolygon δ).arc (a + k) (m + 3 - k) := by
  obtain ⟨γ, hγ, hzero, hhalf, -, hfull, hfirst, hsecond⟩ :=
    exists_marked_prePolygon_loop (P.toPrePolygon δ) a hk1 hk2
  let β : ℝ → ℂ := complexPlaneCoordinates.symm ∘ γ
  have himage (S : Set ℝ) : complexPlaneCoordinates '' (β '' S) = γ '' S := by
    simp only [β, image_image, Function.comp_def, Homeomorph.apply_symm_apply]
  refine ⟨β, complexPlaneCoordinates.symm.continuous.comp_continuousOn hγ.continuousOn,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht h
    exact hγ.injOn hs ht (complexPlaneCoordinates.symm.injective h)
  · simp only [β, Function.comp_apply, hzero, toPrePolygon,
      Homeomorph.symm_apply_apply]
  · simp only [β, Function.comp_apply, hhalf, toPrePolygon,
      Homeomorph.symm_apply_apply]
  · exact congrArg complexPlaneCoordinates.symm hγ.closes.symm
  · apply complexPlaneCoordinates.injective.image_injective
    rw [himage, P.image_carrier]
    exact hfull
  · exact (himage _).trans hfirst
  · exact (himage _).trans hsecond

end PottsContinuity.FKC.LatticePolygon
