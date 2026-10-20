-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/MarkedPolygonOrientation.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.MarkedApproximation
public import PottsContinuity.FKC.Domains.LatticeBoundary

/-!
# Positive marked parametrizations of actual lattice polygons

For any two distinct cyclic vertices, the existing geometric boundary loop
is restricted to a closed path and oriented using its proved interior winding
sign. The resulting counterclockwise parametrization has the prescribed marks.
Its two parameter half-arcs are the original complementary polygon arcs, or
those arcs exchanged by reversal. This assertion concerns the constructed
original-or-reversed path; every other admissible counterclockwise
parametrization has the same two directed half-arcs by
`MarkedBoundaryParametrization.half_arcs_eq` in `FKC.Domains.MarkedHalfArcs`.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set OAI.SLEExactGauge
open scoped unitInterval

/-- Reversal exchanges the lower and upper halves of the actual path image. -/
theorem path_symm_extend_image_lowerHalf {a b : ℂ} (γ : Path a b) :
    γ.symm.extend '' Icc (0 : ℝ) (1 / 2) = γ.extend '' Icc (1 / 2 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith only [ht.2], by linarith only [ht.1]⟩, ?_⟩
    exact (γ.extend_symm_apply t).symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith only [ht.2], by linarith only [ht.1]⟩, ?_⟩
    rw [γ.extend_symm_apply]
    congr 1
    ring

/-- Reversal exchanges the upper and lower halves of the actual path image. -/
theorem path_symm_extend_image_upperHalf {a b : ℂ} (γ : Path a b) :
    γ.symm.extend '' Icc (1 / 2 : ℝ) 1 = γ.extend '' Icc (0 : ℝ) (1 / 2) := by
  simpa only [Path.symm_symm] using (path_symm_extend_image_lowerHalf γ.symm).symm

namespace LatticePolygon

variable {m : ℕ} (P : LatticePolygon m)

/-- Distinct cyclic marks determine a proper nonempty forward arc, with its exact length. -/
theorem markedArcLength_bounds (i j : ZMod (m + 3)) (hij : i ≠ j) :
    1 ≤ (j - i).val ∧ (j - i).val ≤ m + 2 ∧ i + ((j - i).val : ZMod (m + 3)) = j := by
  have hpos : 0 < (j - i).val := ZMod.val_pos.mpr (sub_ne_zero.mpr hij.symm)
  have hlt := (j - i).val_lt
  refine ⟨hpos, by omega, ?_⟩
  rw [ZMod.natCast_zmod_val]
  abel

/-- The actual boundary path in the supplied cyclic order has the two prescribed
marks and exact complementary half-arc images. No orientation is assumed. -/
theorem exists_marked_boundary_path_arcs (δ : PositiveMesh)
    (i j : ZMod (m + 3)) (hij : i ≠ j) :
    ∃ γ : Path (P.markedDomain δ i j hij).a (P.markedDomain δ i j hij).a,
      InjOn γ (Ico (0 : I) 1) ∧ γ midpointUnitInterval = (P.markedDomain δ i j hij).b ∧
      range γ = frontier (P.markedDomain δ i j hij).domain ∧
      complexPlaneCoordinates '' (γ.extend '' Icc (0 : ℝ) (1 / 2)) =
        (P.toPrePolygon δ).arc i (j - i).val ∧
      complexPlaneCoordinates '' (γ.extend '' Icc (1 / 2 : ℝ) 1) =
        (P.toPrePolygon δ).arc j (m + 3 - (j - i).val) := by
  obtain ⟨hk1, hk2, hadd⟩ := markedArcLength_bounds i j hij
  obtain ⟨f, hcont, hinj, hzero, hhalf, hclose, hfull, hfirst, hsecond⟩ :=
    P.exists_marked_boundary_loop δ i hk1 hk2
  let γ : Path (P.markedDomain δ i j hij).a (P.markedDomain δ i j hij).a := {
    toFun t := f t
    continuous_toFun := hcont.domRestrict
    source' := hzero
    target' := hclose.trans hzero }
  have hext (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ.extend t = f t := by
    rw [γ.extend_apply ht]
    rfl
  have himage (S : Set ℝ) (hS : S ⊆ Icc (0 : ℝ) 1) : γ.extend '' S = f '' S :=
    (show EqOn γ.extend f S from fun t ht => hext t (hS ht)).image_eq
  have hlow : γ.extend '' Icc (0 : ℝ) (1 / 2) = f '' Icc (0 : ℝ) (1 / 2) :=
    himage _ (fun t ht => ⟨ht.1, ht.2.trans (by norm_num)⟩)
  have hupp : γ.extend '' Icc (1 / 2 : ℝ) 1 = f '' Icc (1 / 2 : ℝ) 1 :=
    himage _ (fun t ht => ⟨(by norm_num : (0 : ℝ) ≤ 1 / 2).trans ht.1, ht.2⟩)
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht h
    exact Subtype.ext (hinj ⟨s.property.1, hs.2⟩ ⟨t.property.1, ht.2⟩ h)
  · change f (1 / 2) = latticeEmbed δ (P.vertex j)
    simpa only [hadd] using hhalf
  · rw [markedDomain_domain, P.frontier_domain,
      ← γ.image_extend_of_subset (Subset.rfl)]
    exact (himage _ Subset.rfl).trans hfull
  · rw [hlow]
    exact hfirst
  · rw [hupp]
    simpa only [hadd] using hsecond

/-- There is a counterclockwise marked parametrization whose half-arcs are the
supplied cyclic arcs, or exactly those two arcs exchanged by reversing the
constructed loop. This is an existence statement, not half-arc uniqueness for
an arbitrary counterclockwise parametrization. -/
theorem exists_markedBoundaryParametrization_arc_pair (δ : PositiveMesh)
    (i j : ZMod (m + 3)) (hij : i ≠ j) :
    ∃ β : MarkedBoundaryParametrization (P.markedDomain δ i j hij),
      (complexPlaneCoordinates '' (β.path.extend '' Icc (0 : ℝ) (1 / 2)) =
          (P.toPrePolygon δ).arc i (j - i).val ∧
        complexPlaneCoordinates '' (β.path.extend '' Icc (1 / 2 : ℝ) 1) =
          (P.toPrePolygon δ).arc j (m + 3 - (j - i).val)) ∨
      (complexPlaneCoordinates '' (β.path.extend '' Icc (0 : ℝ) (1 / 2)) =
          (P.toPrePolygon δ).arc j (m + 3 - (j - i).val) ∧
        complexPlaneCoordinates '' (β.path.extend '' Icc (1 / 2 : ℝ) 1) =
          (P.toPrePolygon δ).arc i (j - i).val) := by
  obtain ⟨γ, hsimple, hmid, hrange, hfirst, hsecond⟩ :=
    P.exists_marked_boundary_path_arcs δ i j hij
  obtain ⟨β, hβ⟩ := exists_markedBoundaryParametrization_of_path
    (P.markedDomain δ i j hij) γ hsimple hmid hrange
  refine ⟨β, ?_⟩
  rcases hβ with hβ | hβ
  · exact Or.inl ⟨by simpa only [hβ] using hfirst, by simpa only [hβ] using hsecond⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rw [hβ, path_symm_extend_image_lowerHalf]
      exact hsecond
    · rw [hβ, path_symm_extend_image_upperHalf]
      exact hfirst

/-- Package any admissible parametrization while retaining the prescribed mesh,
polygon and marked indices unchanged. No parametrization is selected here. -/
def markedLatticeBoundaryOfParametrization (δ : PositiveMesh)
    (i j : ZMod (m + 3)) (hij : i ≠ j)
    (β : MarkedBoundaryParametrization (P.markedDomain δ i j hij)) : MarkedLatticeBoundary where
  mesh := δ
  size := m
  polygon := P
  first := i
  second := j
  marks_ne := hij
  boundary := β

@[simp] theorem markedLatticeBoundaryOfParametrization_mesh (δ : PositiveMesh)
    (i j : ZMod (m + 3)) (hij : i ≠ j)
    (β : MarkedBoundaryParametrization (P.markedDomain δ i j hij)) :
    (P.markedLatticeBoundaryOfParametrization δ i j hij β).mesh = δ := rfl

@[simp] theorem markedLatticeBoundaryOfParametrization_size (δ : PositiveMesh)
    (i j : ZMod (m + 3)) (hij : i ≠ j)
    (β : MarkedBoundaryParametrization (P.markedDomain δ i j hij)) :
    (P.markedLatticeBoundaryOfParametrization δ i j hij β).size = m := rfl

@[simp] theorem markedLatticeBoundaryOfParametrization_polygon (δ : PositiveMesh)
    (i j : ZMod (m + 3)) (hij : i ≠ j)
    (β : MarkedBoundaryParametrization (P.markedDomain δ i j hij)) :
    (P.markedLatticeBoundaryOfParametrization δ i j hij β).polygon = P := rfl

@[simp] theorem markedLatticeBoundaryOfParametrization_first (δ : PositiveMesh)
    (i j : ZMod (m + 3)) (hij : i ≠ j)
    (β : MarkedBoundaryParametrization (P.markedDomain δ i j hij)) :
    (P.markedLatticeBoundaryOfParametrization δ i j hij β).first = i := rfl

@[simp] theorem markedLatticeBoundaryOfParametrization_second (δ : PositiveMesh)
    (i j : ZMod (m + 3)) (hij : i ≠ j)
    (β : MarkedBoundaryParametrization (P.markedDomain δ i j hij)) :
    (P.markedLatticeBoundaryOfParametrization δ i j hij β).second = j := rfl

end LatticePolygon

end PottsContinuity.FKC
