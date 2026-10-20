-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/Ordered.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-!
# Ordered curves and the reparametrization distance

Representatives are genuine continuous maps from `[0,1]` to the complex plane.
Reparametrizations are increasing homeomorphisms, represented by order
automorphisms of the unit interval. The pseudodistance is the infimum of the
uniform distances after reparametrization; the metric space identifies exactly
zero-distance representatives, not only pairs in the same homeomorphism orbit.

The usual uniform metric on `C(unitInterval, ℂ)` is not changed. A separate
representative type carries the new pseudometric. Completeness, separability,
and convergence of FK interfaces in this metric are not formalized here; the
main theorems do not use them.
-/

@[expose] public section

namespace PottsContinuity.FKC

noncomputable section

open Set

/-- The increasing homeomorphisms of the unit interval, used as reparametrizations. -/
abbrev IncreasingReparametrization := unitInterval ≃o unitInterval

namespace IncreasingReparametrization

/-- Every increasing homeomorphism gives an order automorphism, so no increasing
homeomorphism of the unit interval is excluded as a reparametrization. -/
def ofHomeomorph (e : unitInterval ≃ₜ unitInterval) (he : StrictMono e) :
    IncreasingReparametrization where
  toEquiv := e.toEquiv
  map_rel_iff' := he.le_iff_le

@[simp] lemma ofHomeomorph_apply (e : unitInterval ≃ₜ unitInterval)
    (he : StrictMono e) (t : unitInterval) : ofHomeomorph e he t = e t := rfl

@[simp] lemma map_zero (e : IncreasingReparametrization) : e 0 = 0 := e.map_bot

@[simp] lemma map_one (e : IncreasingReparametrization) : e 1 = 1 := e.map_top

end IncreasingReparametrization

namespace OrderedCurveDistance

/-- Precomposition preserves the orientation and traversal order. -/
def reparametrize (γ : C(unitInterval, ℂ)) (e : IncreasingReparametrization) :
    C(unitInterval, ℂ) := ⟨fun t => γ (e t), γ.continuous.comp e.continuous⟩

@[simp] lemma reparametrize_apply (γ : C(unitInterval, ℂ))
    (e : IncreasingReparametrization) (t : unitInterval) :
    reparametrize γ e t = γ (e t) := rfl

@[simp] lemma reparametrize_refl (γ : C(unitInterval, ℂ)) :
    reparametrize γ (OrderIso.refl _) = γ := by ext; rfl

lemma reparametrize_trans (γ : C(unitInterval, ℂ))
    (e f : IncreasingReparametrization) :
    reparametrize (reparametrize γ e) f = reparametrize γ (f.trans e) := by ext; rfl

@[simp] lemma reparametrize_symm (γ : C(unitInterval, ℂ))
    (e : IncreasingReparametrization) :
    reparametrize (reparametrize γ e) e.symm = γ := by ext; simp

/-- Simultaneous reparametrization is an isometry for the uniform distance. -/
lemma uniform_dist_reparametrize (γ η : C(unitInterval, ℂ))
    (e : IncreasingReparametrization) :
    dist (reparametrize γ e) (reparametrize η e) = dist γ η := by
  apply le_antisymm
  · apply ContinuousMap.dist_le_iff_of_nonempty.mpr
    intro t
    exact ContinuousMap.dist_apply_le_dist (f := γ) (g := η) (e t)
  · apply ContinuousMap.dist_le_iff_of_nonempty.mpr
    intro t
    obtain ⟨s, rfl⟩ := e.surjective t
    exact ContinuousMap.dist_apply_le_dist (f := reparametrize γ e)
      (g := reparametrize η e) s

lemma uniform_dist_reparametrize_left (γ η : C(unitInterval, ℂ))
    (e : IncreasingReparametrization) :
    dist (reparametrize γ e) η = dist γ (reparametrize η e.symm) := by
  have h := uniform_dist_reparametrize (reparametrize γ e) η e.symm
  simpa using h.symm

/-- Lower boundedness is explicit; the real infimum is never a fallback value. -/
lemma reparametrized_dist_bddBelow (γ η : C(unitInterval, ℂ)) :
    BddBelow (Set.range (fun e : IncreasingReparametrization =>
      dist γ (reparametrize η e))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨e, rfl⟩
  exact dist_nonneg

/-- The curve distance: the infimum, over increasing reparametrizations `e`, of the
uniform distance from `γ` to `η ∘ e`. Only the second curve is reparametrized. -/
def distance (γ η : C(unitInterval, ℂ)) : ℝ :=
  ⨅ e : IncreasingReparametrization, dist γ (reparametrize η e)

lemma distance_nonneg (γ η : C(unitInterval, ℂ)) : 0 ≤ distance γ η :=
  le_ciInf (fun _ => dist_nonneg)

lemma distance_le_reparametrize (γ η : C(unitInterval, ℂ))
    (e : IncreasingReparametrization) : distance γ η ≤ dist γ (reparametrize η e) :=
  ciInf_le (reparametrized_dist_bddBelow γ η) e

lemma distance_le_uniform (γ η : C(unitInterval, ℂ)) : distance γ η ≤ dist γ η := by
  simpa using distance_le_reparametrize γ η (OrderIso.refl _)

lemma exists_reparametrize_lt (γ η : C(unitInterval, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : IncreasingReparametrization, dist γ (reparametrize η e) < distance γ η + ε :=
  exists_lt_of_ciInf_lt (lt_add_of_pos_right (distance γ η) hε)

@[simp] lemma distance_self (γ : C(unitInterval, ℂ)) : distance γ γ = 0 := by
  apply le_antisymm
  · simpa using distance_le_uniform γ γ
  · exact distance_nonneg γ γ

lemma distance_comm (γ η : C(unitInterval, ℂ)) : distance γ η = distance η γ := by
  suffices h : ∀ γ η : C(unitInterval, ℂ), distance γ η ≤ distance η γ from
    le_antisymm (h γ η) (h η γ)
  intro f g
  apply le_ciInf
  intro e
  calc
    distance f g ≤ dist f (reparametrize g e.symm) := distance_le_reparametrize f g e.symm
    _ = dist (reparametrize f e) g := (uniform_dist_reparametrize_left f g e).symm
    _ = dist g (reparametrize f e) := dist_comm _ _

lemma distance_triangle (γ η ζ : C(unitInterval, ℂ)) :
    distance γ ζ ≤ distance γ η + distance η ζ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨e, he⟩ := exists_reparametrize_lt γ η (half_pos hε)
  obtain ⟨f, hf⟩ := exists_reparametrize_lt η ζ (half_pos hε)
  have hcalc := calc
    distance γ ζ ≤ dist γ (reparametrize ζ (e.trans f)) :=
      distance_le_reparametrize γ ζ (e.trans f)
    _ ≤ dist γ (reparametrize η e) +
        dist (reparametrize η e) (reparametrize ζ (e.trans f)) := dist_triangle _ _ _
    _ = dist γ (reparametrize η e) + dist η (reparametrize ζ f) := by
      rw [← reparametrize_trans, uniform_dist_reparametrize]
  linarith

lemma start_dist_le (γ η : C(unitInterval, ℂ)) : dist (γ 0) (η 0) ≤ distance γ η := by
  apply le_ciInf
  intro e
  simpa using ContinuousMap.dist_apply_le_dist (f := γ) (g := reparametrize η e) 0

lemma end_dist_le (γ η : C(unitInterval, ℂ)) : dist (γ 1) (η 1) ≤ distance γ η := by
  apply le_ciInf
  intro e
  simpa using ContinuousMap.dist_apply_le_dist (f := γ) (g := reparametrize η e) 1

end OrderedCurveDistance

/-- Separate representatives so the uniform metric on `C([0,1], ℂ)` remains intact. -/
structure OrderedCurveRepresentative where
  path : C(unitInterval, ℂ)

namespace OrderedCurveRepresentative

instance : PseudoMetricSpace OrderedCurveRepresentative where
  dist γ η := OrderedCurveDistance.distance γ.path η.path
  dist_self γ := OrderedCurveDistance.distance_self γ.path
  dist_comm γ η := OrderedCurveDistance.distance_comm γ.path η.path
  dist_triangle γ η ζ := OrderedCurveDistance.distance_triangle γ.path η.path ζ.path

@[simp] lemma dist_eq (γ η : OrderedCurveRepresentative) :
    dist γ η = OrderedCurveDistance.distance γ.path η.path := rfl

end OrderedCurveRepresentative

/-- Ordered continuous curves modulo the zero-distance relation of the curve distance. -/
abbrev OrderedCurve := SeparationQuotient OrderedCurveRepresentative

namespace OrderedCurve

/-- Pass from an actual parametrized continuous curve to its metric class. -/
def ofPath (γ : C(unitInterval, ℂ)) : OrderedCurve :=
  SeparationQuotient.mk ⟨γ⟩

@[simp] lemma dist_ofPath (γ η : C(unitInterval, ℂ)) :
    dist (ofPath γ) (ofPath η) = OrderedCurveDistance.distance γ η := rfl

lemma ofPath_eq_iff (γ η : C(unitInterval, ℂ)) :
    ofPath γ = ofPath η ↔ OrderedCurveDistance.distance γ η = 0 := by
  rw [← dist_eq_zero, dist_ofPath]

/-- The metric quotient map is nonexpanding from the usual uniform path space. -/
lemma lipschitz_ofPath : LipschitzWith 1 ofPath := by
  apply LipschitzWith.of_dist_le_mul
  intro γ η
  simpa using OrderedCurveDistance.distance_le_uniform γ η

lemma continuous_ofPath : Continuous ofPath := lipschitz_ofPath.continuous

lemma ofPath_surjective : Function.Surjective ofPath := by
  intro c
  obtain ⟨γ, rfl⟩ := SeparationQuotient.surjective_mk c
  exact ⟨γ.path, rfl⟩

@[simp] lemma ofPath_reparametrize (γ : C(unitInterval, ℂ))
    (e : IncreasingReparametrization) :
    ofPath (OrderedCurveDistance.reparametrize γ e) = ofPath γ := by
  apply (ofPath_eq_iff _ _).mpr
  apply le_antisymm
  · have h := OrderedCurveDistance.distance_le_reparametrize
      (OrderedCurveDistance.reparametrize γ e) γ e
    simpa using h
  · exact OrderedCurveDistance.distance_nonneg _ _

/-- The starting point survives zero-distance identification. -/
def start : OrderedCurve → ℂ :=
  SeparationQuotient.lift (fun γ : OrderedCurveRepresentative => γ.path 0) (by
    intro γ η h
    apply dist_eq_zero.mp
    apply le_antisymm
    · exact (OrderedCurveDistance.start_dist_le γ.path η.path).trans_eq h.dist_eq_zero
    · exact dist_nonneg)

/-- The terminal point survives zero-distance identification. -/
def finish : OrderedCurve → ℂ :=
  SeparationQuotient.lift (fun γ : OrderedCurveRepresentative => γ.path 1) (by
    intro γ η h
    apply dist_eq_zero.mp
    apply le_antisymm
    · exact (OrderedCurveDistance.end_dist_le γ.path η.path).trans_eq h.dist_eq_zero
    · exact dist_nonneg)

@[simp] lemma start_ofPath (γ : C(unitInterval, ℂ)) : start (ofPath γ) = γ 0 := rfl

@[simp] lemma finish_ofPath (γ : C(unitInterval, ℂ)) : finish (ofPath γ) = γ 1 := rfl

lemma lipschitz_start : LipschitzWith 1 start := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  obtain ⟨γ, rfl⟩ := ofPath_surjective c
  obtain ⟨η, rfl⟩ := ofPath_surjective d
  simpa using OrderedCurveDistance.start_dist_le γ η

lemma lipschitz_finish : LipschitzWith 1 finish := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  obtain ⟨γ, rfl⟩ := ofPath_surjective c
  obtain ⟨η, rfl⟩ := ofPath_surjective d
  simpa using OrderedCurveDistance.end_dist_le γ η

lemma continuous_start : Continuous start := lipschitz_start.continuous

lemma continuous_finish : Continuous finish := lipschitz_finish.continuous

end OrderedCurve

end

end PottsContinuity.FKC
