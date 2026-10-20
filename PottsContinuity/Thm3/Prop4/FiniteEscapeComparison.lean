module

public import PottsContinuity.Thm3.Prop4.FirstSeparatorPrefix
public import PottsContinuity.Thm3.Prop4.CensoredArcComparison

/-!
# Cropping a finite FK connection at a deterministic exterior separator

The existing censored-cluster comparison applies because every escaping
walk visits the physical separator. The exterior target can be arbitrary;
only its disjointness from the crop and the boundary support are needed.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
attribute [local instance] configurationMeasurableSpace

/-- A connection to an exterior target is bounded by the actual cropped
root-to-separator probability with just that separator wired. -/
theorem finite_exterior_target_probability_le_crop (θ : Parameters)
    (D W T : Set V) (hWD : W ⊆ D) (hT : T ⊆ Dᶜ)
    (hsep : ∀ x ∈ D, ∀ y, G.Adj x y → y ∉ D → x ∈ W)
    (ξ : BoundaryCondition V) (hξ : ξ.boundary ⊆ Dᶜ ∪ W) (x : D) :
    (measure G θ ξ (targetConnectionEvent x.val T)).toReal ≤
      (measure (G.induce D) θ (BoundaryCondition.wired (Subtype.val ⁻¹' W))
        (targetConnectionEvent x (Subtype.val ⁻¹' W))).toReal := by
  have hsub : targetConnectionEvent (G := G) x.val T ⊆ finiteArcIsolationEvent (G := G) D W x.val := by
    intro A hA
    have hlocal : ∀ a ∈ D, ∀ b, (openGraph G A).Adj a b → b ∉ D → a ∈ W :=
      fun a ha b hab hb => hsep a ha b (openGraph_le G A hab) hb
    obtain ⟨y,hy,p⟩ := hA
    obtain ⟨p⟩ := p
    obtain ⟨z,hz,q,_,_,_⟩ := walk_to_first_separator D W hWD hlocal x.property (hT hy) p
    refine ⟨⟨z,hz,⟨q⟩⟩,?_⟩
    intro y hy p
    exact walk_escape_hits_separator D W hWD hlocal x.property hy p
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (finite_arc_isolation_probability_le θ D W hWD ξ hξ x)

/-- In particular a finite strip whose wired target lies outside the crop
is bounded by the crop with its physical separator wired. -/
theorem finite_wired_exterior_target_probability_le_crop (θ : Parameters)
    (D W T : Set V) (hWD : W ⊆ D) (hT : T ⊆ Dᶜ)
    (hsep : ∀ x ∈ D, ∀ y, G.Adj x y → y ∉ D → x ∈ W) (x : D) :
    (measure G θ (BoundaryCondition.wired T) (targetConnectionEvent x.val T)).toReal ≤
      (measure (G.induce D) θ (BoundaryCondition.wired (Subtype.val ⁻¹' W))
        (targetConnectionEvent x (Subtype.val ⁻¹' W))).toReal := by
  apply finite_exterior_target_probability_le_crop G θ D W T hWD hT hsep
  exact fun _ h => Or.inl (hT h)

end
end PottsContinuity.Thm3.Prop4
