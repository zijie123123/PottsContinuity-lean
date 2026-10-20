module

public import PottsContinuity.PlanarTopology.RectangleConnectionTransport
public import PottsContinuity.PlanarTopology.ReflectionLaw

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

/-- Reflection in the vertical bisector preserves the actual open rectangle,
with the configuration transported by reflection followed by translation. -/
def rectangleOpenReflectionXHom (w h : ℕ) (ω : LatticeConfiguration) :
    (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle (0,0) w h : Set LatticeVertex) →g
      (PD.rcInfiniteOpenGraph (edgeTranslate ((w:ℤ),0)
        (latticeConfigurationIsoHomeomorph kstReflectionXIso ω))).induce
        (PD.FK.latticeRectangle (0,0) w h : Set LatticeVertex) where
  toFun u := ⟨((w:ℤ)-u.val.1,u.val.2),by
    have hu := (mem_latticeRectangle (0,0) u.val w h).mp u.property
    apply (mem_latticeRectangle (0,0) _ w h).mpr
    dsimp at *
    omega⟩
  map_rel' := by
    intro u v huv
    have hr := (rcOpenConfigurationIso kstReflectionXIso ω).map_rel_iff'.mpr huv
    have ht := (openGraphTranslationIso ((w:ℤ),0)
      (latticeConfigurationIsoHomeomorph kstReflectionXIso ω)).map_rel_iff'.mpr hr
    change (PD.rcInfiniteOpenGraph (edgeTranslate ((w:ℤ),0)
      (latticeConfigurationIsoHomeomorph kstReflectionXIso ω))).Adj
      (-u.val.1+(w:ℤ),u.val.2+0) (-v.val.1+(w:ℤ),v.val.2+0) at ht
    have heq (z : LatticeVertex) : (-z.1+(w:ℤ),z.2+0) = ((w:ℤ)-z.1,z.2) := by
      ext <;> dsimp <;> omega
    rw [heq,heq] at ht
    exact ht

theorem rectangleReflectionConfiguration_twice (w : ℕ) (ω : LatticeConfiguration) :
    edgeTranslate ((w:ℤ),0) (latticeConfigurationIsoHomeomorph kstReflectionXIso
      (edgeTranslate ((w:ℤ),0) (latticeConfigurationIsoHomeomorph kstReflectionXIso ω))) = ω := by
  rw [reflectionXConfiguration_translate,reflectionXConfiguration_twice]
  simp only [← edgeTranslate_add,Prod.mk_add_mk,
    zero_add,add_neg_cancel]
  exact edgeTranslate_zero ω

theorem rectangleConnectionEvent_reflectionX_iff (w h : ℕ)
    (S T : Set LatticeVertex) (ω : LatticeConfiguration) :
    edgeTranslate ((w:ℤ),0) (latticeConfigurationIsoHomeomorph kstReflectionXIso ω) ∈
      rectangleConnectionEvent (0,0) w h S T ↔
    ω ∈ rectangleConnectionEvent (0,0) w h
      ((fun z : LatticeVertex => ((w:ℤ)-z.1,z.2)) ⁻¹' S)
      ((fun z : LatticeVertex => ((w:ℤ)-z.1,z.2)) ⁻¹' T) := by
  constructor
  · intro hh
    obtain ⟨u,hu,v,hv,hconn⟩ := (rectangleConnectionEvent_iff _ _ _ _ _ _).mp hh
    let f := rectangleOpenReflectionXHom w h
      (edgeTranslate ((w:ℤ),0) (latticeConfigurationIsoHomeomorph kstReflectionXIso ω))
    have hu' : ((w:ℤ)-((w:ℤ)-u.val.1),u.val.2) = u.val := by ext <;> dsimp; omega
    have hv' : ((w:ℤ)-((w:ℤ)-v.val.1),v.val.2) = v.val := by ext <;> dsimp; omega
    have ht := (rectangleConnectionEvent_iff (0,0) w h
      ((fun z : LatticeVertex => ((w:ℤ)-z.1,z.2)) ⁻¹' S)
      ((fun z : LatticeVertex => ((w:ℤ)-z.1,z.2)) ⁻¹' T) _).mpr
      ⟨f u,by change ((w:ℤ)-((w:ℤ)-u.val.1),u.val.2) ∈ S; rwa [hu'],
        f v,by change ((w:ℤ)-((w:ℤ)-v.val.1),v.val.2) ∈ T; rwa [hv'],hconn.map f⟩
    simpa only [rectangleReflectionConfiguration_twice] using ht
  · intro hh
    obtain ⟨u,hu,v,hv,hconn⟩ := (rectangleConnectionEvent_iff _ _ _ _ _ _).mp hh
    let f := rectangleOpenReflectionXHom w h ω
    exact (rectangleConnectionEvent_iff _ _ _ _ _ _).mpr ⟨f u,hu,f v,hv,hconn.map f⟩

/-- Rectangle reflection exchanges marked sets under the reflected law;
translation invariance removes the position of the bisector. -/
theorem reflectionXLaw_rectangleConnectionEvent (μ : Measure LatticeConfiguration)
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (w h : ℕ) (S T : Set LatticeVertex) :
    μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso)
      (rectangleConnectionEvent (0,0) w h S T) =
    μ (rectangleConnectionEvent (0,0) w h
      ((fun z : LatticeVertex => ((w:ℤ)-z.1,z.2)) ⁻¹' S)
      ((fun z : LatticeVertex => ((w:ℤ)-z.1,z.2)) ⁻¹' T)) := by
  let ν := μ.map (latticeConfigurationIsoHomeomorph kstReflectionXIso)
  have hinv := reflectionXLaw_translation_invariant μ htranslation ((w:ℤ),0)
  calc
    _ = ν.map (edgeTranslate ((w:ℤ),0)) (rectangleConnectionEvent (0,0) w h S T) := by rw [hinv]
    _ = μ ((edgeTranslate ((w:ℤ),0) ∘ latticeConfigurationIsoHomeomorph kstReflectionXIso) ⁻¹'
      rectangleConnectionEvent (0,0) w h S T) := by
        rw [Measure.map_map (edgeTranslate_measurable _) (latticeConfigurationIsoHomeomorph_measurable _)]
        rw [Measure.map_apply ((edgeTranslate_measurable _).comp (latticeConfigurationIsoHomeomorph_measurable _))
          (rectangleConnectionEvent_measurableSet _ _ _ _ _)]
    _ = _ := by
      congr 1
      ext ω
      exact rectangleConnectionEvent_reflectionX_iff w h S T ω

end
end PottsContinuity.PlanarTopology
