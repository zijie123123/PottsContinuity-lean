module

public import PottsContinuity.PlanarTopology.RectangleConnectionReflection
public import PottsContinuity.PlanarTopology.BalancedSeedCell

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section

/-- Reflection of an admissible seed anchor; the whole seed square is reflected
in the bisector of the full rectangle of width W+s. -/
def rectangleSeedReflectXAnchor {W H : ℕ} (v : Fin (W+1) × Fin (H+1)) :
    Fin (W+1) × Fin (H+1) := (⟨W-v.1.val,by omega⟩,v.2)

theorem reflectionXLaw_rectangleSeedConnectionEvent (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) (T : Set LatticeVertex) :
    (μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso)).real
      (rectangleSeedConnectionEvent W H s (rectangleSeedReflectXAnchor v) T) =
    μ.real (rectangleSeedConnectionEvent W H s v
      ((fun z : LatticeVertex => (((W+s:ℕ):ℤ)-z.1,z.2)) ⁻¹' T)) := by
  have hh := reflectionXLaw_rectangleConnectionEvent μ htranslation (W+s) (H+s)
    (PD.FK.latticeRectangle (((rectangleSeedReflectXAnchor v).1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex) T
  have hsum : (W-v.1.val)+v.1.val = W := Nat.sub_add_cancel (by have hv := v.1.isLt; omega)
  have hs : (fun z : LatticeVertex => (((W+s:ℕ):ℤ)-z.1,z.2)) ⁻¹'
      (PD.FK.latticeRectangle (((rectangleSeedReflectXAnchor v).1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex) =
      (PD.FK.latticeRectangle ((v.1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex) := by
    ext z
    simp only [Set.mem_preimage,Finset.mem_coe,mem_latticeRectangle,
      rectangleSeedReflectXAnchor]
    omega
  rw [hs] at hh
  exact congrArg ENNReal.toReal hh

theorem reflectionXLaw_rectangleSeedLeftProbability (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) :
    rectangleSeedLeftProbability (μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso))
      W H s (rectangleSeedReflectXAnchor v) = rectangleSeedRightProbability μ W H s v := by
  have hh := reflectionXLaw_rectangleSeedConnectionEvent μ htranslation W H s v {z | z.1 = 0}
  have ht : (fun z : LatticeVertex => (((W+s:ℕ):ℤ)-z.1,z.2)) ⁻¹' {z | z.1 = 0} =
      {z : LatticeVertex | z.1 = ((W+s:ℕ):ℤ)} := by ext z; simp only [Set.mem_preimage,Set.mem_ofPred_eq]; omega
  rwa [ht] at hh

theorem reflectionXLaw_rectangleSeedRightProbability (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) :
    rectangleSeedRightProbability (μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso))
      W H s (rectangleSeedReflectXAnchor v) = rectangleSeedLeftProbability μ W H s v := by
  have hh := reflectionXLaw_rectangleSeedConnectionEvent μ htranslation W H s v
    {z | z.1 = ((W+s:ℕ):ℤ)}
  have ht : (fun z : LatticeVertex => (((W+s:ℕ):ℤ)-z.1,z.2)) ⁻¹'
      {z | z.1 = ((W+s:ℕ):ℤ)} = {z : LatticeVertex | z.1 = 0} := by
    ext z; simp only [Set.mem_preimage,Set.mem_ofPred_eq]; omega
  rwa [ht] at hh

theorem reflectionXLaw_rectangleSeedBottomProbability (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) :
    rectangleSeedBottomProbability (μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso))
      W H s (rectangleSeedReflectXAnchor v) = rectangleSeedBottomProbability μ W H s v :=
  reflectionXLaw_rectangleSeedConnectionEvent μ htranslation W H s v {z | z.2 = 0}

theorem reflectionXLaw_rectangleSeedTopProbability (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (W H s : ℕ) (v : Fin (W+1) × Fin (H+1)) :
    rectangleSeedTopProbability (μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso))
      W H s (rectangleSeedReflectXAnchor v) = rectangleSeedTopProbability μ W H s v :=
  reflectionXLaw_rectangleSeedConnectionEvent μ htranslation W H s v {z | z.2 = ((H+s:ℕ):ℤ)}

theorem rectangleSeedReflectXAnchor_close {W H : ℕ} {v y : Fin (W+1) × Fin (H+1)}
    (hy : y.1.val ≤ v.1.val+1 ∧ v.1.val ≤ y.1.val+1) :
    (rectangleSeedReflectXAnchor y).1.val ≤ (rectangleSeedReflectXAnchor v).1.val+1 ∧
    (rectangleSeedReflectXAnchor v).1.val ≤ (rectangleSeedReflectXAnchor y).1.val+1 := by
  have hv := v.1.isLt
  have hy' := y.1.isLt
  dsimp [rectangleSeedReflectXAnchor]
  omega

end
end PottsContinuity.PlanarTopology
