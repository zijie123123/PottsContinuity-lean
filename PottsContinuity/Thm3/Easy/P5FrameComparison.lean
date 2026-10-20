module

public import Mathlib
public import PottsContinuity.PD.Duality.BoxDihedral
public import PottsContinuity.Foundations.HorizontalCrossingBridge
public import PottsContinuity.PD.FK.Isomorphism
public import PottsContinuity.Thm3.Easy.P5FourFrameConditional
public import PottsContinuity.Thm3.RSW.EmbeddedPath
public import PottsContinuity.Thm3.RSW.FiniteIso

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.RSW

private theorem p5SquareLattice_adj_iff (u v : ℤ × ℤ) :
    PottsContinuity.squareLattice.Adj u v ↔
      ((u.1 + 1 = v.1 ∨ v.1 + 1 = u.1) ∧ u.2 = v.2) ∨
      (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) := by
  change |u.1 - v.1| + |u.2 - v.2| = 1 ↔ _
  simp only [abs_eq_max_neg]
  omega

def p5Translate (a v : ℤ × ℤ) : ℤ × ℤ := (v.1 + a.1, v.2 + a.2)
def p5QuarterTurn (v : ℤ × ℤ) : ℤ × ℤ := (-v.2, v.1)
def p5ReflectX (v : ℤ × ℤ) : ℤ × ℤ := (-v.1, v.2)

def p5TranslationIso (a : ℤ × ℤ) :
    PottsContinuity.squareLattice ≃g PottsContinuity.squareLattice where
  toFun := p5Translate a
  invFun := p5Translate (-a)
  left_inv := by intro v; ext <;> dsimp [p5Translate] <;> omega
  right_inv := by intro v; ext <;> dsimp [p5Translate] <;> omega
  map_rel_iff' := by
    intro u v
    rw [p5SquareLattice_adj_iff, p5SquareLattice_adj_iff]
    dsimp [p5Translate]
    omega

def p5QuarterTurnIso :
    PottsContinuity.squareLattice ≃g PottsContinuity.squareLattice where
  toFun := p5QuarterTurn
  invFun := fun v => (v.2, -v.1)
  left_inv := by intro v; ext <;> dsimp [p5QuarterTurn]; omega
  right_inv := by intro v; ext <;> dsimp [p5QuarterTurn]; omega
  map_rel_iff' := by
    intro u v
    rw [p5SquareLattice_adj_iff, p5SquareLattice_adj_iff]
    dsimp [p5QuarterTurn]
    omega

def p5ReflectXIso :
    PottsContinuity.squareLattice ≃g PottsContinuity.squareLattice where
  toFun := p5ReflectX
  invFun := p5ReflectX
  left_inv := by intro v; ext <;> dsimp [p5ReflectX]; omega
  right_inv := by intro v; ext <;> dsimp [p5ReflectX]; omega
  map_rel_iff' := by
    intro u v
    rw [p5SquareLattice_adj_iff, p5SquareLattice_adj_iff]
    dsimp [p5ReflectX]
    omega

/-- The buffered `α = 16` rectangle in P5, at scale `m`. -/
def p5BaseDomain (m : ℕ) : Finset (ℤ × ℤ) :=
  latticeRectangle (-(m : ℤ)) (17 * (m : ℤ)) (-(m : ℤ)) (2 * (m : ℤ))

/-- The P5 crossing inside its one-scale-buffered rectangle. -/
def p5BaseCrossing (m : ℕ)
    (ω : (squareLattice.induce (p5BaseDomain m : Set (ℤ × ℤ))).edgeSet → Bool) : Prop :=
  horizontalCrossing (p5BaseDomain m) 0 (16 * (m : ℤ)) 0 (m : ℤ) ω

/-- The four translated or quarter-turned buffered P5 rectangles. -/
def p5FrameDomain (n m : ℕ) (i : Fin 4) : Finset (ℤ × ℤ) :=
  match i.val with
  | 0 => latticeRectangle (-(9 * (m : ℤ))) (9 * (m : ℤ))
      ((n : ℤ) + 2) ((n : ℤ) + 2 + 3 * (m : ℤ))
  | 1 => latticeRectangle (-(9 * (m : ℤ))) (9 * (m : ℤ))
      (-(n : ℤ) - 2 - 3 * (m : ℤ)) (-(n : ℤ) - 2)
  | 2 => latticeRectangle ((n : ℤ) + 2) ((n : ℤ) + 2 + 3 * (m : ℤ))
      (-(9 * (m : ℤ))) (9 * (m : ℤ))
  | _ => latticeRectangle (-(n : ℤ) - 2 - 3 * (m : ℤ)) (-(n : ℤ) - 2)
      (-(9 * (m : ℤ))) (9 * (m : ℤ))

/-- The lattice symmetry carrying the P5 rectangle to the corresponding frame. -/
def p5FrameLatticeIso (n m : ℕ) (i : Fin 4) :
    PottsContinuity.squareLattice ≃g PottsContinuity.squareLattice :=
  match i.val with
  | 0 => p5TranslationIso (-(8 * (m : ℤ)), (n : ℤ) + 2 + (m : ℤ))
  | 1 => p5TranslationIso (-(8 * (m : ℤ)), -(n : ℤ) - 2 - 2 * (m : ℤ))
  | 2 => p5QuarterTurnIso.trans
      (p5TranslationIso ((n : ℤ) + 2 + 2 * (m : ℤ), -(8 * (m : ℤ))))
  | _ => (p5QuarterTurnIso.trans p5ReflectXIso).trans
      (p5TranslationIso (-(n : ℤ) - 2 - 2 * (m : ℤ), -(8 * (m : ℤ))))

private theorem p5FrameLatticeIso_apply (n m : ℕ) (i : Fin 4) (z : ℤ × ℤ) :
    p5FrameLatticeIso n m i z =
      match i.val with
      | 0 => (z.1 - 8 * (m : ℤ), z.2 + (n : ℤ) + 2 + (m : ℤ))
      | 1 => (z.1 - 8 * (m : ℤ), z.2 - (n : ℤ) - 2 - 2 * (m : ℤ))
      | 2 => ((n : ℤ) + 2 + 2 * (m : ℤ) - z.2, z.1 - 8 * (m : ℤ))
      | _ => (z.2 - (n : ℤ) - 2 - 2 * (m : ℤ), z.1 - 8 * (m : ℤ)) := by
  fin_cases i <;>
    simp [p5FrameLatticeIso, p5TranslationIso, p5Translate,
      p5QuarterTurnIso, p5QuarterTurn, p5ReflectXIso, p5ReflectX] <;> omega

 theorem p5FrameLatticeIso_mem (n m : ℕ) (i : Fin 4) (z : ℤ × ℤ) :
    p5FrameLatticeIso n m i z ∈ p5FrameDomain n m i ↔ z ∈ p5BaseDomain m := by
  fin_cases i <;>
    simp [p5FrameLatticeIso, p5FrameDomain, p5BaseDomain,
      p5TranslationIso, p5Translate, p5QuarterTurnIso,
      p5QuarterTurn, p5ReflectXIso, p5ReflectX,
      latticeRectangle, Finset.mem_product, Finset.mem_Icc] <;> omega

/-- Restrict a lattice graph isomorphism to two finite vertex sets. -/
def p5InducedIso (e : PottsContinuity.squareLattice ≃g
    PottsContinuity.squareLattice)
    (V W : Finset (ℤ × ℤ))
    (hmem : ∀ z, e z ∈ W ↔ z ∈ V) :
    PottsContinuity.squareLattice.induce (V : Set (ℤ × ℤ)) ≃g
      PottsContinuity.squareLattice.induce (W : Set (ℤ × ℤ)) where
  toEquiv :=
    { toFun := fun z => ⟨e z.1, (hmem z.1).2 z.2⟩
      invFun := fun z => ⟨e.symm z.1, by
        apply (hmem (e.symm z.1)).1
        simp⟩
      left_inv := by intro z; apply Subtype.ext; exact e.left_inv z.1
      right_inv := by intro z; apply Subtype.ext; exact e.right_inv z.1 }
  map_rel_iff' := by
    intro x y
    exact e.map_rel_iff'

/-- The induced graph isomorphism from the P5 rectangle to one frame rectangle. -/
def p5FrameIso (n m : ℕ) (i : Fin 4) :
    PottsContinuity.squareLattice.induce (p5BaseDomain m : Set (ℤ × ℤ)) ≃g
      PottsContinuity.squareLattice.induce (p5FrameDomain n m i : Set (ℤ × ℤ)) :=
  p5InducedIso (p5FrameLatticeIso n m i) (p5BaseDomain m)
    (p5FrameDomain n m i) (p5FrameLatticeIso_mem n m i)

/-- The crossing event on the ambient frame rectangle. -/
def p5FrameCrossingOnDomain (n m : ℕ) (i : Fin 4)
    (ω : (PottsContinuity.squareLattice.induce
      (p5FrameDomain n m i : Set (ℤ × ℤ))).edgeSet → Bool) : Prop :=
  match i.val with
  | 0 => horizontalCrossing (p5FrameDomain n m i)
      (-(8 * (m : ℤ))) (8 * (m : ℤ))
      ((n : ℤ) + 2 + (m : ℤ)) ((n : ℤ) + 2 + 2 * (m : ℤ)) ω
  | 1 => horizontalCrossing (p5FrameDomain n m i)
      (-(8 * (m : ℤ))) (8 * (m : ℤ))
      (-(n : ℤ) - 2 - 2 * (m : ℤ)) (-(n : ℤ) - 2 - (m : ℤ)) ω
  | 2 => p5VerticalCrossing (p5FrameDomain n m i)
      (-(8 * (m : ℤ))) (8 * (m : ℤ))
      ((n : ℤ) + 2 + (m : ℤ)) ((n : ℤ) + 2 + 2 * (m : ℤ)) ω
  | _ => p5VerticalCrossing (p5FrameDomain n m i)
      (-(8 * (m : ℤ))) (8 * (m : ℤ))
      (-(n : ℤ) - 2 - 2 * (m : ℤ)) (-(n : ℤ) - 2 - (m : ℤ)) ω

private theorem p5FrameCrossing_transport (n m : ℕ) (i : Fin 4)
    (ω : (PottsContinuity.squareLattice.induce
      (p5BaseDomain m : Set (ℤ × ℤ))).edgeSet → Bool)
    (hω : p5BaseCrossing m ω) :
    p5FrameCrossingOnDomain n m i
      (RSW.finiteBoolIso (p5BaseDomain m) (p5FrameDomain n m i)
        (p5FrameIso n m i) ω) := by
  rcases hω with ⟨x, y, w, hx, hy, hsupport⟩
  let eOpen := RSW.finiteBoolOpenIso (p5BaseDomain m) (p5FrameDomain n m i)
    (p5FrameIso n m i) ω
  let x' := eOpen x
  let y' := eOpen y
  let w' := w.map eOpen.toHom
  have hval (z : (p5BaseDomain m : Set (ℤ × ℤ))) :
      (eOpen z).val = p5FrameLatticeIso n m i z.val := rfl
  have hsource (z : (p5BaseDomain m : Set (ℤ × ℤ))) (hz : z ∈ w.support) :
      z.val ∈ Set.Icc 0 (16 * (m : ℤ)) ×ˢ Set.Icc 0 (m : ℤ) := by
    have hz' := hsupport z hz
    change z.val ∈ Set.Icc 0 (16 * (m : ℤ)) ×ˢ Set.Icc 0 (m : ℤ) at hz'
    exact hz'
  have hmapped (v : (p5FrameDomain n m i : Set (ℤ × ℤ)))
      (hv : v ∈ w'.support) : ∃ z ∈ w.support, eOpen z = v := by
    change v ∈ (w.map eOpen.toHom).support at hv
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
    exact hv
  fin_cases i
  · refine ⟨x', y', w', ?_, ?_, ?_⟩
    · change (x'.val).1 = -(8 * (m : ℤ)) ∧
        (x'.val).2 ∈ Set.Icc ((n : ℤ) + 2 + (m : ℤ))
          ((n : ℤ) + 2 + 2 * (m : ℤ))
      rw [hval x]
      simp only [p5FrameLatticeIso_apply, Set.mem_Icc]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hx
      omega
    · change (y'.val).1 = 8 * (m : ℤ) ∧
        (y'.val).2 ∈ Set.Icc ((n : ℤ) + 2 + (m : ℤ))
          ((n : ℤ) + 2 + 2 * (m : ℤ))
      rw [hval y]
      simp only [p5FrameLatticeIso_apply, Set.mem_Icc]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hy
      omega
    · intro v hv
      rcases hmapped v hv with ⟨z, hz, rfl⟩
      rw [hval z]
      simp only [p5FrameLatticeIso_apply]
      have hsz := hsource z hz
      simp only [Set.mem_prod, Set.mem_Icc] at hsz ⊢
      omega
  · refine ⟨x', y', w', ?_, ?_, ?_⟩
    · change (x'.val).1 = -(8 * (m : ℤ)) ∧
        (x'.val).2 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * (m : ℤ))
          (-(n : ℤ) - 2 - (m : ℤ))
      rw [hval x]
      simp only [p5FrameLatticeIso_apply, Set.mem_Icc]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hx
      omega
    · change (y'.val).1 = 8 * (m : ℤ) ∧
        (y'.val).2 ∈ Set.Icc (-(n : ℤ) - 2 - 2 * (m : ℤ))
          (-(n : ℤ) - 2 - (m : ℤ))
      rw [hval y]
      simp only [p5FrameLatticeIso_apply, Set.mem_Icc]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hy
      omega
    · intro v hv
      rcases hmapped v hv with ⟨z, hz, rfl⟩
      rw [hval z]
      simp only [p5FrameLatticeIso_apply]
      have hsz := hsource z hz
      simp only [Set.mem_prod, Set.mem_Icc] at hsz ⊢
      omega
  · refine ⟨x', y', w', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hval x]
      simp only [p5FrameLatticeIso_apply]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hx
      omega
    · rw [hval y]
      simp only [p5FrameLatticeIso_apply]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hy
      omega
    · rw [hval x]
      simp only [p5FrameLatticeIso_apply, Set.mem_Icc]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hx
      omega
    · rw [hval y]
      simp only [p5FrameLatticeIso_apply, Set.mem_Icc]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hy
      omega
    · intro v hv
      rcases hmapped v hv with ⟨z, hz, rfl⟩
      rw [hval z]
      simp only [p5FrameLatticeIso_apply]
      have hsz := hsource z hz
      simp only [Set.mem_prod, Set.mem_Icc] at hsz ⊢
      omega
  · refine ⟨x', y', w', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hval x]
      simp only [p5FrameLatticeIso_apply]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hx
      omega
    · rw [hval y]
      simp only [p5FrameLatticeIso_apply]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hy
      omega
    · rw [hval x]
      simp only [p5FrameLatticeIso_apply, Set.mem_Icc]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hx
      omega
    · rw [hval y]
      simp only [p5FrameLatticeIso_apply, Set.mem_Icc]
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hy
      omega
    · intro v hv
      rcases hmapped v hv with ⟨z, hz, rfl⟩
      rw [hval z]
      simp only [p5FrameLatticeIso_apply]
      have hsz := hsource z hz
      simp only [Set.mem_prod, Set.mem_Icc] at hsz ⊢
      omega

private theorem p5VerticalCrossingOnDomain_isUpperSet (V : Finset (ℤ × ℤ))
    (a b c d : ℤ) :
    IsUpperSet {ω | p5VerticalCrossing V a b c d ω} := by
  intro ω η hωη hcross
  rcases hcross with ⟨x, y, w, hx, hy, hxc, hyc, hsupport⟩
  refine ⟨x, y, w.mapLe (RSW.rcOpenGraph_mono V hωη), hx, hy, hxc, hyc, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
  exact hsupport v hv

private theorem p5FrameCrossingOnDomain_isUpperSet (n m : ℕ) (i : Fin 4) :
    IsUpperSet {ω | p5FrameCrossingOnDomain n m i ω} := by
  fin_cases i <;> simp only [p5FrameCrossingOnDomain] <;>
    first
    | exact RSW.horizontalCrossing_isUpperSet _ _ _ _ _
    | exact p5VerticalCrossingOnDomain_isUpperSet _ _ _ _ _

private theorem p5FiniteBoundaryEventProbability_mono (V : Finset (ℤ × ℤ))
    (θ : Parameters) (ξ : BoundaryCondition (V : Set (ℤ × ℤ)))
    (E F : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop)
    (hEF : ∀ ω, E ω → F ω) :
    RSW.finiteBoundaryEventProbability V θ ξ E ≤
      RSW.finiteBoundaryEventProbability V θ ξ F := by
  unfold RSW.finiteBoundaryEventProbability
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro A hA
  change E ((boolConfigurationEquiv _).symm A) at hA
  change F ((boolConfigurationEquiv _).symm A)
  exact hEF _ hA

private theorem p5FrameDomainProbability_ge_base (θ : Parameters) (n m : ℕ)
    (i : Fin 4) :
    RSW.finiteBoundaryEventProbability (p5BaseDomain m) θ
      (frozenBoundaryCondition (p5BaseDomain m) 0) (p5BaseCrossing m) ≤
    RSW.finiteBoundaryEventProbability (p5FrameDomain n m i) θ
      (frozenBoundaryCondition (p5FrameDomain n m i) 0)
      (p5FrameCrossingOnDomain n m i) := by
  have hmono := p5FiniteBoundaryEventProbability_mono (p5BaseDomain m) θ
    (frozenBoundaryCondition (p5BaseDomain m) 0) (p5BaseCrossing m)
    (fun ω => p5FrameCrossingOnDomain n m i
      (RSW.finiteBoolIso (p5BaseDomain m) (p5FrameDomain n m i)
        (p5FrameIso n m i) ω))
    (fun ω hω => p5FrameCrossing_transport n m i ω hω)
  have hiso := RSW.finite_free_probability_iso (p5BaseDomain m)
    (p5FrameDomain n m i) (p5FrameIso n m i) θ
    (p5FrameCrossingOnDomain n m i)
  calc
    RSW.finiteBoundaryEventProbability (p5BaseDomain m) θ
        (frozenBoundaryCondition (p5BaseDomain m) 0) (p5BaseCrossing m) ≤
      RSW.finiteBoundaryEventProbability (p5BaseDomain m) θ
        (frozenBoundaryCondition (p5BaseDomain m) 0)
        (fun ω => p5FrameCrossingOnDomain n m i
          (RSW.finiteBoolIso (p5BaseDomain m) (p5FrameDomain n m i)
            (p5FrameIso n m i) ω)) := hmono
    _ = RSW.finiteBoundaryEventProbability (p5FrameDomain n m i) θ
        (frozenBoundaryCondition (p5FrameDomain n m i) 0)
        (p5FrameCrossingOnDomain n m i) := hiso.symm

private theorem p5HorizontalCrossing_embedded_restriction
    (V W : Finset (ℤ × ℤ))
    (f : (V : Set (ℤ × ℤ)) ↪ (W : Set (ℤ × ℤ)))
    (hGH : (squareLattice.induce (V : Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (W : Set (ℤ × ℤ)))
    (hf : ∀ z, (f z).val = z.val)
    (a b c d : ℤ) (A : Configuration (squareLattice.induce (W : Set (ℤ × ℤ)))) :
    horizontalCrossing V a b c d
        ((boolConfigurationEquiv (squareLattice.induce (V : Set (ℤ × ℤ)))).symm
          (embeddedConfigurationRestriction
            (squareLattice.induce (V : Set (ℤ × ℤ)))
            (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH A)) →
      horizontalCrossing W a b c d
        ((boolConfigurationEquiv (squareLattice.induce (W : Set (ℤ × ℤ)))).symm A) := by
  let ωV := (boolConfigurationEquiv
    (squareLattice.induce (V : Set (ℤ × ℤ)))).symm
      (embeddedConfigurationRestriction (squareLattice.induce (V : Set (ℤ × ℤ)))
        (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH A)
  let ωW := (boolConfigurationEquiv
    (squareLattice.induce (W : Set (ℤ × ℤ)))).symm A
  intro hcross
  rcases hcross with ⟨x, y, w, hx, hy, hsupport⟩
  let hom : rcOpenGraph V ωV →g
      openGraph (squareLattice.induce (W : Set (ℤ × ℤ))) A := {
    toFun := f
    map_rel' := by
      intro u v huv
      have huv' : (openGraph (squareLattice.induce (V : Set (ℤ × ℤ)))
          (embeddedConfigurationRestriction (squareLattice.induce (V : Set (ℤ × ℤ)))
            (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH A)).Adj u v := by
        rw [← RSW.rcOpenGraph_boolConfigurationEquiv_symm]
        exact huv
      exact (RSW.embeddedRestrictionOpenHom
        (squareLattice.induce (V : Set (ℤ × ℤ)))
        (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH A).map_rel huv'
  }
  let w' := w.map hom
  have hhom_val (z : (V : Set (ℤ × ℤ))) : hom z = f z := rfl
  have hhom_coord (z : (V : Set (ℤ × ℤ))) : (hom z).val = z.val := by
    rw [hhom_val z, hf z]
  change horizontalCrossing W a b c d ωW
  unfold horizontalCrossing
  rw [RSW.rcOpenGraph_boolConfigurationEquiv_symm]
  refine ⟨hom x, hom y, w', ?_, ?_, ?_⟩
  · simpa only [hhom_coord] using hx
  · simpa only [hhom_coord] using hy
  · intro z hz
    change z ∈ (w.map hom).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    simpa only [hhom_coord] using hsupport u hu

private theorem p5VerticalCrossing_embedded_restriction
    (V W : Finset (ℤ × ℤ))
    (f : (V : Set (ℤ × ℤ)) ↪ (W : Set (ℤ × ℤ)))
    (hGH : (squareLattice.induce (V : Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (W : Set (ℤ × ℤ)))
    (hf : ∀ z, (f z).val = z.val)
    (a b c d : ℤ) (A : Configuration (squareLattice.induce (W : Set (ℤ × ℤ)))) :
    p5VerticalCrossing V a b c d
        ((boolConfigurationEquiv (squareLattice.induce (V : Set (ℤ × ℤ)))).symm
          (embeddedConfigurationRestriction
            (squareLattice.induce (V : Set (ℤ × ℤ)))
            (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH A)) →
      p5VerticalCrossing W a b c d
        ((boolConfigurationEquiv (squareLattice.induce (W : Set (ℤ × ℤ)))).symm A) := by
  let ωW := (boolConfigurationEquiv
    (squareLattice.induce (W : Set (ℤ × ℤ)))).symm A
  intro hcross
  rcases hcross with ⟨x, y, w, hx, hy, hxc, hyc, hsupport⟩
  let hom : rcOpenGraph V
      ((boolConfigurationEquiv
        (squareLattice.induce (V : Set (ℤ × ℤ)))).symm
        (embeddedConfigurationRestriction
          (squareLattice.induce (V : Set (ℤ × ℤ)))
          (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH A)) →g
      openGraph (squareLattice.induce (W : Set (ℤ × ℤ))) A := {
    toFun := f
    map_rel' := by
      intro u v huv
      have huv' : (openGraph (squareLattice.induce (V : Set (ℤ × ℤ)))
          (embeddedConfigurationRestriction (squareLattice.induce (V : Set (ℤ × ℤ)))
            (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH A)).Adj u v := by
        rw [← RSW.rcOpenGraph_boolConfigurationEquiv_symm]
        exact huv
      exact (RSW.embeddedRestrictionOpenHom
        (squareLattice.induce (V : Set (ℤ × ℤ)))
        (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH A).map_rel huv'
  }
  let w' := w.map hom
  have hhom_val (z : (V : Set (ℤ × ℤ))) : hom z = f z := rfl
  have hhom_coord (z : (V : Set (ℤ × ℤ))) : (hom z).val = z.val := by
    rw [hhom_val z, hf z]
  change p5VerticalCrossing W a b c d ωW
  unfold p5VerticalCrossing
  rw [RSW.rcOpenGraph_boolConfigurationEquiv_symm]
  refine ⟨hom x, hom y, w', ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hhom_coord] using hx
  · simpa only [hhom_coord] using hy
  · simpa only [hhom_coord] using hxc
  · simpa only [hhom_coord] using hyc
  · intro z hz
    change z ∈ (w.map hom).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    simpa only [hhom_coord] using hsupport u hu

private theorem p5FrameDomain_subset_p5aAnnulusVertexSet
    (n m : ℕ) (i : Fin 4)
    (hnm : n + 2 + 3 * m ≤ 2 * n) (h9m : 9 * m ≤ 2 * n) :
    p5FrameDomain n m i ⊆ p5aAnnulusVertexSet n := by
  intro z hz
  rw [p5aAnnulusVertexSet, Finset.mem_sdiff]
  constructor
  · apply (Foundations.mem_box_iff_interval (2 * n) z).2
    fin_cases i <;>
      simp [p5FrameDomain, latticeRectangle, Finset.mem_product, Finset.mem_Icc] at hz ⊢ <;>
      omega
  · intro hzinner
    have hb := (Foundations.mem_box_iff_interval (n + 1) z).mp hzinner
    fin_cases i <;>
      simp [p5FrameDomain, latticeRectangle, Finset.mem_product, Finset.mem_Icc] at hz hb ⊢ <;>
      omega

private theorem p5FrameCrossing_embedded_restriction
    (n m : ℕ) (i : Fin 4)
    (f : (p5FrameDomain n m i : Set (ℤ × ℤ)) ↪
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ)))
    (hGH : (squareLattice.induce (p5FrameDomain n m i : Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (p5aAnnulusVertexSet n : Set (ℤ × ℤ)))
    (hf : ∀ z, (f z).val = z.val)
    (A : Configuration (squareLattice.induce (p5aAnnulusVertexSet n : Set (ℤ × ℤ)))) :
    p5FrameCrossingOnDomain n m i
        ((boolConfigurationEquiv
          (squareLattice.induce (p5FrameDomain n m i : Set (ℤ × ℤ)))).symm
          (embeddedConfigurationRestriction
            (squareLattice.induce (p5FrameDomain n m i : Set (ℤ × ℤ)))
            (squareLattice.induce (p5aAnnulusVertexSet n : Set (ℤ × ℤ))) f hGH A)) →
      p5FrameCrossing n m i
        ((boolConfigurationEquiv
          (squareLattice.induce (p5aAnnulusVertexSet n : Set (ℤ × ℤ)))).symm A) := by
  fin_cases i
  · simpa [p5FrameCrossingOnDomain, p5FrameCrossing] using
      p5HorizontalCrossing_embedded_restriction
        (p5FrameDomain n m 0) (p5aAnnulusVertexSet n) f hGH hf
        (-(8 * (m : ℤ))) (8 * (m : ℤ))
        ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) A
  · simpa [p5FrameCrossingOnDomain, p5FrameCrossing] using
      p5HorizontalCrossing_embedded_restriction
        (p5FrameDomain n m 1) (p5aAnnulusVertexSet n) f hGH hf
        (-(8 * (m : ℤ))) (8 * (m : ℤ))
        (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) A
  · simpa [p5FrameCrossingOnDomain, p5FrameCrossing] using
      p5VerticalCrossing_embedded_restriction
        (p5FrameDomain n m 2) (p5aAnnulusVertexSet n) f hGH hf
        (-(8 * (m : ℤ))) (8 * (m : ℤ))
        ((n : ℤ) + 2 + m) ((n : ℤ) + 2 + 2 * m) A
  · simpa [p5FrameCrossingOnDomain, p5FrameCrossing] using
      p5VerticalCrossing_embedded_restriction
        (p5FrameDomain n m 3) (p5aAnnulusVertexSet n) f hGH hf
        (-(8 * (m : ℤ))) (8 * (m : ℤ))
        (-(n : ℤ) - 2 - 2 * m) (-(n : ℤ) - 2 - m) A

private theorem p5FiniteBoundaryFreeMeasure_eq (V : Finset (ℤ × ℤ))
    (θ : Parameters)
    (E : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop) :
    RSW.finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0) E =
      (PD.FK.measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ
        (BoundaryCondition.free ∅)
        (RSW.finiteBoolEvent V E)).toReal := by
  have hpart : (frozenBoundaryCondition V 0).partition =
      (BoundaryCondition.free ∅).partition := by
    simp [PD.FK.frozenBoundaryCondition, PD.FK.BoundaryCondition.free]
  have hlaw : PD.FK.law (squareLattice.induce (V : Set (ℤ × ℤ))) θ
      (frozenBoundaryCondition V 0) =
        PD.FK.law (squareLattice.induce (V : Set (ℤ × ℤ))) θ
          (BoundaryCondition.free ∅) :=
    PD.FK.law_eq_of_boundary_partition_eq θ _ _ hpart
  unfold RSW.finiteBoundaryEventProbability PD.FK.measure
  rw [hlaw]

private theorem p5FrameDomainProbability_le_annulus
    (θ : Parameters) (n m : ℕ) (i : Fin 4)
    (hnm : n + 2 + 3 * m ≤ 2 * n) (h9m : 9 * m ≤ 2 * n) :
    RSW.finiteBoundaryEventProbability (p5FrameDomain n m i) θ
      (frozenBoundaryCondition (p5FrameDomain n m i) 0)
      (p5FrameCrossingOnDomain n m i) ≤
    RSW.finiteBoundaryEventProbability (p5aAnnulusVertexSet n) θ
      (frozenBoundaryCondition (p5aAnnulusVertexSet n) 0)
      (p5FrameCrossing n m i) := by
  let V := p5FrameDomain n m i
  let W := p5aAnnulusVertexSet n
  have hVW : V ⊆ W := by
    exact p5FrameDomain_subset_p5aAnnulusVertexSet n m i hnm h9m
  let f : (V : Set (ℤ × ℤ)) ↪ (W : Set (ℤ × ℤ)) :=
    ⟨fun z => ⟨z.val, hVW z.property⟩,
      fun x y h => by
        apply Subtype.ext
        exact congrArg (fun z : (W : Set (ℤ × ℤ)) => z.val) h⟩
  have hf (z : (V : Set (ℤ × ℤ))) : (f z).val = z.val := rfl
  have hGH : (squareLattice.induce (V : Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (W : Set (ℤ × ℤ)) := by
    rw [SimpleGraph.map_le_iff_le_comap]
    intro x y hxy
    exact hxy
  let E := p5FrameCrossingOnDomain n m i
  let S := RSW.finiteBoolEvent V E
  have hE : IsUpperSet S := by
    exact RSW.finiteBoolEvent_isUpperSet V E
      (p5FrameCrossingOnDomain_isUpperSet n m i)
  have hcmp := RSW.embedded_free_probability_le
    (squareLattice.induce (V : Set (ℤ × ℤ)))
    (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH θ S hE
  have hsub :
      {A | embeddedConfigurationRestriction
          (squareLattice.induce (V : Set (ℤ × ℤ)))
          (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH A ∈ S} ⊆
        RSW.finiteBoolEvent W (p5FrameCrossing n m i) := by
    intro A hA
    change E ((boolConfigurationEquiv
      (squareLattice.induce (V : Set (ℤ × ℤ)))).symm
        (embeddedConfigurationRestriction
          (squareLattice.induce (V : Set (ℤ × ℤ)))
          (squareLattice.induce (W : Set (ℤ × ℤ))) f hGH A)) at hA
    change p5FrameCrossing n m i ((boolConfigurationEquiv
      (squareLattice.induce (W : Set (ℤ × ℤ)))).symm A)
    exact p5FrameCrossing_embedded_restriction n m i f hGH hf A hA
  have hcmp' := hcmp.trans (measureReal_mono hsub)
  calc
    RSW.finiteBoundaryEventProbability (p5FrameDomain n m i) θ
        (frozenBoundaryCondition (p5FrameDomain n m i) 0)
        (p5FrameCrossingOnDomain n m i) =
      (PD.FK.measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ
        (BoundaryCondition.free ∅) (RSW.finiteBoolEvent V E)).toReal := by
          simpa [V, E] using p5FiniteBoundaryFreeMeasure_eq V θ E
    _ ≤ (PD.FK.measure (squareLattice.induce (W : Set (ℤ × ℤ))) θ
        (BoundaryCondition.free ∅)
        (RSW.finiteBoolEvent W (p5FrameCrossing n m i))).toReal := hcmp'
    _ = RSW.finiteBoundaryEventProbability (p5aAnnulusVertexSet n) θ
        (frozenBoundaryCondition (p5aAnnulusVertexSet n) 0)
        (p5FrameCrossing n m i) := by
          symm
          simpa [W] using
            p5FiniteBoundaryFreeMeasure_eq W θ (p5FrameCrossing n m i)

/-- The α=16 P5 rectangle lower bound transports to each buffered side frame
inside the finite annulus whenever the frame fits in the outer box. -/
theorem p5Aspect16_frameProbability_lower_bound
    (θ : Parameters) (n m : ℕ) (c : ℝ)
    (hP5 : c ≤ rcEventProb (p5BaseDomain m) θ.toP θ.toQ 0
      (p5BaseCrossing m))
    (hfit : n + 2 + 3 * m ≤ 2 * n) (houter : 9 * m ≤ 2 * n) :
    ∀ i : Fin 4,
      c ≤ RSW.finiteBoundaryEventProbability (p5aAnnulusVertexSet n) θ
        (frozenBoundaryCondition (p5aAnnulusVertexSet n) 0)
        (p5FrameCrossing n m i) := by
  intro i
  have hbase :
      RSW.finiteBoundaryEventProbability (p5BaseDomain m) θ
        (frozenBoundaryCondition (p5BaseDomain m) 0) (p5BaseCrossing m) =
        rcEventProb (p5BaseDomain m) θ.toP θ.toQ 0 (p5BaseCrossing m) := by
    exact RSW.finiteBoundaryEventProbability_frozen (p5BaseDomain m) θ 0
      (p5BaseCrossing m)
  calc
    c ≤ rcEventProb (p5BaseDomain m) θ.toP θ.toQ 0 (p5BaseCrossing m) := hP5
    _ = RSW.finiteBoundaryEventProbability (p5BaseDomain m) θ
        (frozenBoundaryCondition (p5BaseDomain m) 0) (p5BaseCrossing m) := hbase.symm
    _ ≤ RSW.finiteBoundaryEventProbability (p5FrameDomain n m i) θ
        (frozenBoundaryCondition (p5FrameDomain n m i) 0)
        (p5FrameCrossingOnDomain n m i) := p5FrameDomainProbability_ge_base θ n m i
    _ ≤ RSW.finiteBoundaryEventProbability (p5aAnnulusVertexSet n) θ
        (frozenBoundaryCondition (p5aAnnulusVertexSet n) 0)
        (p5FrameCrossing n m i) := p5FrameDomainProbability_le_annulus θ n m i hfit houter

/-- P5 at aspect ratio 16 gives a uniform positive free-annulus circuit bound
once the explicit four-frame circuit extraction `hgeometry` is supplied. The statement
uses the corrected P5a range `n ≥ 2`. -/
theorem p5a_uniform_lower_bound_of_p5Aspect16_and_frameGeometry
    (θ : Parameters)
    (hP5Aspect16 : ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      c ≤ rcEventProb (p5BaseDomain m) θ.toP θ.toQ 0 (p5BaseCrossing m))
    (hgeometry : ∀ (n m : ℕ), 2 ≤ n → 1 ≤ m → n + 2 ≤ 6 * m →
      n + 2 + 3 * m ≤ 2 * n → 9 * m ≤ 2 * n →
      ∀ ω, p5FrameCrossing n m 0 ω ∧ p5FrameCrossing n m 1 ω ∧
        p5FrameCrossing n m 2 ω ∧ p5FrameCrossing n m 3 ω →
        p5aAnnulusCircuitEvent n ω) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ n : ℕ, 2 ≤ n →
      c₂ ≤ p5aAnnulusProbability θ n := by
  obtain ⟨c, hc, hP5⟩ := hP5Aspect16
  have hlarge : ∀ n : ℕ, 72 ≤ n → ∃ m : ℕ, 1 ≤ m ∧
      n + 2 ≤ 6 * m ∧ n + 2 + 3 * m ≤ 2 * n ∧ 9 * m ≤ 2 * n ∧
      ∀ i : Fin 4,
        c ≤ RSW.finiteBoundaryEventProbability (p5aAnnulusVertexSet n) θ
          (frozenBoundaryCondition (p5aAnnulusVertexSet n) 0)
          (p5FrameCrossing n m i) := by
    intro n hn
    let m := (n + 7) / 6
    have hm : 1 ≤ m := by dsimp [m]; omega
    have hscale : n + 2 ≤ 6 * m := by dsimp [m]; omega
    have hfit : n + 2 + 3 * m ≤ 2 * n := by dsimp [m]; omega
    have houter : 9 * m ≤ 2 * n := by dsimp [m]; omega
    refine ⟨m, hm, hscale, hfit, houter, ?_⟩
    intro i
    exact p5Aspect16_frameProbability_lower_bound θ n m c
      (hP5 m hm) hfit houter i
  exact exists_p5a_uniform_lower_bound_of_largeFrameCrossings θ 72 (by omega)
    c hc hlarge hgeometry

end PottsContinuity.Thm3.Easy
