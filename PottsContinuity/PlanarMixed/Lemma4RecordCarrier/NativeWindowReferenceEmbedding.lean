module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.NativeWindowPartition
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ReferenceCoreAdjacency

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Square RSW
noncomputable section

abbrev lemma4ReferenceCoreVertex (n : ℕ) :=
  rectangleDualHorizontalCoreVertex (-3*(n:ℤ)+1,-3*(n:ℤ)+1) (6*n-1) (6*n-1)

abbrev lemma4ReferenceCoreGraph (n : ℕ) :=
  rectangleDualHorizontalCoreGraph (-3*(n:ℤ)+1,-3*(n:ℤ)+1) (6*n-1) (6*n-1)

/-- Translate an ACTUAL active window vertex to the reference core. -/
def lemma4ActiveWindowCoreVertex (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3)
    (u : lemma4ActiveNativeWindowVertex n A j) : lemma4ReferenceCoreVertex n := by
  have hc := lemma4_native_window_incident_vertex_coordinates n A j u
  change (10*(j:ℤ)-13)*(n:ℤ) ≤ u.val.val.1 ∧ u.val.val.1 ≤ (10*(j:ℤ)-7)*(n:ℤ) ∧
    -3*(n:ℤ) < u.val.val.2 ∧ u.val.val.2 < 3*(n:ℤ) at hc
  refine ⟨⟨(u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ),u.val.val.2),?_⟩,?_⟩
  · change (u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ),u.val.val.2) ∈
      PD.FK.latticeRectangle ((-3*(n:ℤ)+1)-1,(-3*(n:ℤ)+1)-1) ((6*n-1)+1) ((6*n-1)+1)
    rw [PD.FK.mem_latticeRectangle]
    norm_num only [Nat.cast_add,Nat.cast_one,Prod.fst,Prod.snd]
    fin_cases j <;> dsimp at hc ⊢ <;> omega
  · change -3*(n:ℤ)+1 ≤ u.val.val.2 ∧ u.val.val.2 ≤ (-3*(n:ℤ)+1)+((6*n-1:ℕ):ℤ)-1
    omega

def lemma4ActiveWindowCoreEmbedding (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :
    lemma4ActiveNativeWindowVertex n A j ↪ lemma4ReferenceCoreVertex n where
  toFun := lemma4ActiveWindowCoreVertex n hn A j
  inj' := by
    intro u v h
    have hx := congrArg (fun x : lemma4ReferenceCoreVertex n => x.val.val.1) h
    have hy := congrArg (fun x : lemma4ReferenceCoreVertex n => x.val.val.2) h
    change u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)=v.val.val.1-(10*(j:ℤ)-10)*(n:ℤ) at hx
    change u.val.val.2=v.val.val.2 at hy
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (by omega) hy

/-- Exact translation embeds every actual active window bond into the true
reference core; queried bonds never reappear in this map. -/
theorem lemma4ActiveWindowCoreGraph_map_le
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :
    (lemma4ActiveNativeWindowGraph n A j).map (lemma4ActiveWindowCoreEmbedding n hn A j) ≤
      lemma4ReferenceCoreGraph n := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  have hwin : (lemma4NativeWindowGraph n A j).Adj u.val v.val := huv
  have horig : (lemma4AmbientGraph n).Adj u.val v.val := edgeRestriction_le _ _ hwin.1
  have hadj : PD.FK.squareLattice.Adj u.val.val v.val.val := horig
  have hstep := (PD.FK.squareLattice_adj_iff _ _).mp hadj
  apply referenceDualCore_adj_of_lattice_adj (-3*(n:ℤ)+1) (6*n-1) (by omega)
  · apply (PD.FK.squareLattice_adj_iff _ _).mpr
    change (((u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ))+1=v.val.val.1-(10*(j:ℤ)-10)*(n:ℤ) ∨
      (v.val.val.1-(10*(j:ℤ)-10)*(n:ℤ))+1=u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)) ∧ u.val.val.2=v.val.val.2) ∨
      (u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)=v.val.val.1-(10*(j:ℤ)-10)*(n:ℤ) ∧
        (u.val.val.2+1=v.val.val.2 ∨ v.val.val.2+1=u.val.val.2))
    omega
  · intro hleft
    change u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)=(-3*(n:ℤ)+1)-1 ∧
      v.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)=(-3*(n:ℤ)+1)-1 at hleft
    apply hwin.2.2.2.1
    fin_cases j <;> dsimp at hleft ⊢ <;> omega
  · intro hright
    change u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)=(-3*(n:ℤ)+1)+((6*n-1:ℕ):ℤ) ∧
      v.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)=(-3*(n:ℤ)+1)+((6*n-1:ℕ):ℤ) at hright
    apply hwin.2.2.2.2
    fin_cases j <;> dsimp at hright ⊢ <;> omega

/-- Pulling back the reference wiring gives exactly the actual joined sides. -/
theorem lemma4ActiveWindowCore_boundary_pullback
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3) :
    isolatedExtensionPullbackBoundary (lemma4ActiveWindowCoreEmbedding n hn A j)
      (BoundaryCondition.wired {u : lemma4ReferenceCoreVertex n |
        rectangleDualHorizontalCoreInclusion (-3*(n:ℤ)+1,-3*(n:ℤ)+1) (6*n-1) (6*n-1) u ∈
          rectangleDoubleCollarDualInnerVerticalSides (-3*(n:ℤ)+1,-3*(n:ℤ)+1) (6*n-1) (6*n-1)}) =
      BoundaryCondition.wired (lemma4ActiveNativeWindowSides n A j) := by
  have hset : (lemma4ActiveWindowCoreEmbedding n hn A j) ⁻¹'
      {u : lemma4ReferenceCoreVertex n |
        rectangleDualHorizontalCoreInclusion (-3*(n:ℤ)+1,-3*(n:ℤ)+1) (6*n-1) (6*n-1) u ∈
          rectangleDoubleCollarDualInnerVerticalSides (-3*(n:ℤ)+1,-3*(n:ℤ)+1) (6*n-1) (6*n-1)} =
      lemma4ActiveNativeWindowSides n A j := by
    ext u
    change (u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)=(-3*(n:ℤ)+1)-1 ∨
      u.val.val.1-(10*(j:ℤ)-10)*(n:ℤ)=(-3*(n:ℤ)+1)+((6*n-1:ℕ):ℤ)) ↔ _
    change _ ↔ (u.val.val.1=(10*(j:ℤ)-13)*(n:ℤ) ∨ u.val.val.1=(10*(j:ℤ)-7)*(n:ℤ))
    fin_cases j <;> dsimp <;> omega
  change BoundaryCondition.mk _ _ _ = BoundaryCondition.mk _ _ _
  rw [BoundaryCondition.mk.injEq]
  constructor
  · exact hset
  · ext u v
    change ((lemma4ActiveWindowCoreEmbedding n hn A j) u=(lemma4ActiveWindowCoreEmbedding n hn A j) v ∨ _) ↔ _
    rw [Function.Embedding.apply_eq_iff_eq]
    exact or_congr Iff.rfl (and_congr (Set.ext_iff.mp hset u) (Set.ext_iff.mp hset v))

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
