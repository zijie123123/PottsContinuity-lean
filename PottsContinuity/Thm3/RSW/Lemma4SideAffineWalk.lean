module

public import PottsContinuity.Thm3.RSW.Lemma4SideAffineStates
public import PottsContinuity.Thm3.RSW.Lemma4DualBands

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- Undoing the side coordinates replays every closed-dual step on the
original included side sample. -/
def lemma4SideInverseClosedDualHom (n : ℕ) (i : Fin 2)
    (A : Configuration (rectangleGraph (-56*(n:ℤ),0) (112*n) (54*n))) :
    wholePlaneClosedDualGraph (finiteSubgraphConfiguration
      (PD.FK.latticeRectangle (-56*(n:ℤ),0) (112*n) (54*n)) 0 A) →g
    wholePlaneClosedDualGraph (finiteSubgraphConfiguration (box (56*n)) 0
      (inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i))
        ((configurationIso (lemma4SideFullRectangleIso n (lemma4SideSign i)
          (lemma4SideSign_eq_one_or_neg_one i))).symm A))) where
  toFun := lemma4SideInverseFace n i
  map_rel' := by
    intro u v huv
    obtain ⟨b,hb,hpair⟩ := huv
    have hb' := (lemma4SideInverse_bondState n i A b).trans hb
    have hfaces := lemma4SideInverseBond_faces n i b
    have hp : s(lemma4SideInverseFace n i u,lemma4SideInverseFace n i v) =
        s((lemma4SideInverseBond n i b).faceBase false,
          (lemma4SideInverseBond n i b).faceBase true) := by
      have hsource : s(u,v) = s(b.faceBase false,b.faceBase true) := Sym2.eq_iff.mpr hpair
      exact (congrArg (Sym2.map (lemma4SideInverseFace n i)) hsource).trans hfaces.symm
    exact ⟨lemma4SideInverseBond n i b,hb',Sym2.eq_iff.mp hp⟩

/-- The side replay preserves the image of the complete original walk support. -/
theorem lemma4SideInverseClosedDualHom_support (n : ℕ) (i : Fin 2)
    (A : Configuration (rectangleGraph (-56*(n:ℤ),0) (112*n) (54*n)))
    {u v : LatticeVertex}
    (p : (wholePlaneClosedDualGraph (finiteSubgraphConfiguration
      (PD.FK.latticeRectangle (-56*(n:ℤ),0) (112*n) (54*n)) 0 A)).Walk u v) :
    (p.map (lemma4SideInverseClosedDualHom n i A)).support =
      p.support.map (lemma4SideInverseFace n i) := by
  exact SimpleGraph.Walk.support_map _ _

/-- A normalized band crossing becomes the exact source upper or lower band
crossing, with the lower face-base reflection included. -/
theorem lemma4_normalizedBand_to_originalSide (n : ℕ) (i : Fin 2)
    (A : Configuration (rectangleGraph (-56*(n:ℤ),0) (112*n) (54*n)))
    (hA : A ∈ finiteClosedDualHorizontalRectangle
      (PD.FK.latticeRectangle (-56*(n:ℤ),0) (112*n) (54*n))
      (-56*(n:ℤ)-1) (56*(n:ℤ)) 0 ((n:ℤ)-1)) :
    inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i))
      ((configurationIso (lemma4SideFullRectangleIso n (lemma4SideSign i)
        (lemma4SideSign_eq_one_or_neg_one i))).symm A) ∈ lemma4DualBandEvent n i := by
  obtain ⟨u,v,p,hu,hv,hp⟩ := hA
  have hsupport : ∀ (j : Fin 2), ∀ z ∈ (p.map (lemma4SideInverseClosedDualHom n j A)).support,
      ∃ x ∈ p.support, lemma4SideInverseFace n j x = z := by
    intro j z hz
    have hs := lemma4SideInverseClosedDualHom_support n j A p
    exact List.mem_map.mp (Eq.mp (congrArg (fun L => z ∈ L) hs) hz)
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨lemma4SideInverseFace n 0 u,lemma4SideInverseFace n 0 v,
      p.map (lemma4SideInverseClosedDualHom n 0 A),hu,hv,?_⟩
    intro z hz
    obtain ⟨x,hx,rfl⟩ := hsupport 0 z hz
    have h := hp x hx
    change _ ∧ _ ∧ _ ∧ _
    simp only [lemma4SideInverseFace]
    have hi : lemma4SideSign 0 = 1 := rfl
    simp only [hi,one_mul]
    omega
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    refine ⟨lemma4SideInverseFace n 1 u,lemma4SideInverseFace n 1 v,
      p.map (lemma4SideInverseClosedDualHom n 1 A),hu,hv,?_⟩
    intro z hz
    obtain ⟨x,hx,rfl⟩ := hsupport 1 z hz
    have h := hp x hx
    change _ ∧ _ ∧ _ ∧ _
    simp only [lemma4SideInverseFace] at *
    have hi : lemma4SideSign 1 = -1 := rfl
    simp only [hi,neg_one_mul] at *
    omega

end
end PottsContinuity.RSW
