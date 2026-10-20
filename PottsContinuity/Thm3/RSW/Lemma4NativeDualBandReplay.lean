module

public import PottsContinuity.Thm3.RSW.BottomCollarNativeWalkReplay
public import PottsContinuity.Thm3.RSW.Lemma4NativeDualBand
public import PottsContinuity.Thm3.RSW.FiniteClosedDualRectangle

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- A native residual-dual band crossing is an actual closed-dual band
crossing of the original normalized side rectangle, with every path vertex
confined to the original face rows and horizontal endpoints. -/
theorem lemma4_nativeDualBand_normalized_replay (n : ℕ)
    (A : Configuration (rectangleGraph (-56*(n:ℤ),0) (112*n) (54*n)))
    (hA : bottomCollarInducedDualEquiv (-56*(n:ℤ),0) (112*n) (54*n) A ∈
      lemma4NativeDualBandEvent n) :
    A ∈ finiteClosedDualHorizontalRectangle
      (PD.FK.latticeRectangle (-56*(n:ℤ),0) (112*n) (54*n))
      (-56*(n:ℤ)-1) (56*(n:ℤ)) 0 ((n:ℤ)-1) := by
  obtain ⟨u,v,p,hu,hv,hp⟩ := hA
  let φ := bottomCollarDualClosedExtensionHom (-56*(n:ℤ),0) (112*n) (54*n) A
  refine ⟨u.val,v.val,p.map φ,hu,hv,?_⟩
  intro z hz
  have hs : (p.map φ).support = p.support.map Subtype.val :=
    bottomCollarDualClosedExtensionHom_support (-56*(n:ℤ),0) (112*n) (54*n) A p
  have hz' : z ∈ p.support.map Subtype.val := Eq.mp (congrArg (fun L => z ∈ L) hs) hz
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz'
  exact hp x hx

/-- The normalized replay holds on every residual dual sample under the
unique inverse original configuration, without any probability premise. -/
theorem lemma4_nativeDualBand_normalized_inverse_replay (n : ℕ)
    (D : Configuration (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n)))
    (hD : D ∈ lemma4NativeDualBandEvent n) :
    (bottomCollarInducedDualEquiv (-56*(n:ℤ),0) (112*n) (54*n)).symm D ∈
      finiteClosedDualHorizontalRectangle
        (PD.FK.latticeRectangle (-56*(n:ℤ),0) (112*n) (54*n))
        (-56*(n:ℤ)-1) (56*(n:ℤ)) 0 ((n:ℤ)-1) := by
  apply lemma4_nativeDualBand_normalized_replay
  simpa only [Equiv.apply_symm_apply] using hD

end
end PottsContinuity.RSW
