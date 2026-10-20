module

public import PottsContinuity.Thm3.Push.StripReflectionFiniteLaw

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- Reflection commutes with literal closed extension of a window state to
actual strip bonds, including bonds outside the original finite window. -/
theorem stripWindow_extension_reflection (n m : ℕ)
    (C : Configuration (PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set (ℤ × ℤ)))) :
    RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m
      (configurationIso (stripWindowHorizontalReflectionIso n m) C)) =
    stripHorizontalReflection n (RSW.stripPlaneRestriction n
      (RSW.stripWindowPlaneConfiguration n m C)) := by
  classical
  let F : (ℤ × ℤ) → (ℤ × ℤ) := fun w => (-w.1,w.2)
  have hinv (z : Sym2 (ℤ × ℤ)) : Sym2.map F (Sym2.map F z) = z := by
    induction z using Sym2.ind with
    | h a b => simp only [Sym2.map_mk,F,neg_neg]
  have hwindow (f : (PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set (ℤ × ℤ))).edgeSet) :
      ((RSW.stripWindowPlaneEmbedding n m).mapEdgeSet
        (configurationIsoEdgeEquiv (stripWindowHorizontalReflectionIso n m) f)).val =
      Sym2.map F ((RSW.stripWindowPlaneEmbedding n m).mapEdgeSet f).val := by
    change Sym2.map Subtype.val (Sym2.map (stripWindowHorizontalReflectionIso n m) f.val) =
      Sym2.map F (Sym2.map Subtype.val f.val)
    rw [Sym2.map_map,Sym2.map_map]
    rfl
  have hstrip (e : (RSW.stripGraph n).edgeSet) :
      ((RSW.stripPlaneEmbedding n).mapEdgeSet
        ((stripHorizontalReflectionIso n).mapEdgeSet e)).val =
      Sym2.map F ((RSW.stripPlaneEmbedding n).mapEdgeSet e).val := by
    change Sym2.map Subtype.val (Sym2.map (stripHorizontalReflectionIso n) e.val) =
      Sym2.map F (Sym2.map Subtype.val e.val)
    rw [Sym2.map_map,Sym2.map_map]
    rfl
  funext e
  simp only [RSW.stripPlaneRestriction,RSW.stripWindowPlaneConfiguration,
    stripHorizontalReflection,decide_eq_decide]
  constructor
  · intro h
    obtain ⟨g,hg,hge⟩ := Finset.mem_map.mp h
    obtain ⟨f,hf,hfg⟩ := Finset.mem_map.mp hg
    subst g
    refine Finset.mem_map.mpr ⟨f,hf,?_⟩
    apply Subtype.ext
    have hv := congrArg (fun z => Sym2.map F z.val) hge
    change Sym2.map F ((RSW.stripWindowPlaneEmbedding n m).mapEdgeSet
      (configurationIsoEdgeEquiv (stripWindowHorizontalReflectionIso n m) f)).val = _ at hv
    rw [hwindow f,hinv] at hv
    rw [hstrip]
    exact hv
  · intro h
    obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp h
    refine Finset.mem_map.mpr ⟨configurationIsoEdgeEquiv (stripWindowHorizontalReflectionIso n m) f,
      Finset.mem_map.mpr ⟨f,hf,rfl⟩,?_⟩
    apply Subtype.ext
    change ((RSW.stripWindowPlaneEmbedding n m).mapEdgeSet
      (configurationIsoEdgeEquiv (stripWindowHorizontalReflectionIso n m) f)).val = _
    rw [hwindow f]
    have hv := congrArg (fun z => Sym2.map F z.val) hfe
    rw [hstrip,hinv] at hv
    exact hv

end
end PottsContinuity.Push
