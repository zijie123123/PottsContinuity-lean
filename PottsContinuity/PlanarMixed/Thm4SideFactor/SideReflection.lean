module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.UniformSideAverage
public import PottsContinuity.FKC.FiniteFK.SlitBoxHorizontalReflection

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open FKC FKC.Medial FKC.FiniteFK
noncomputable section

def slitSideConfigurationReflection (m : ℕ) :
    PD.FK.Configuration (slitBoxGraph (16*m)) ≃ PD.FK.Configuration (slitBoxGraph (16*m)) :=
  PD.FK.configurationIso (slitBoxGraphHorizontalReflectionIso (16*m))

def slitSideDualReflection (z : LatticeVertex) : LatticeVertex := (-z.1-1,z.2)

def slitSideDualBondReflection (d : LatticeBond) : LatticeBond :=
  match d.axis with
  | .horizontal => ⟨(-d.base.1-2,d.base.2),.horizontal⟩
  | .vertical => ⟨(-d.base.1-1,d.base.2),.vertical⟩

theorem slitSideDualReflection_involutive : Function.Involutive slitSideDualReflection := by
  intro z
  rcases z with ⟨x,y⟩
  simp [slitSideDualReflection]

theorem slitSideDualReflection_mem_faces (m : ℕ) (z : LatticeVertex) :
    slitSideDualReflection z ∈ slitScreenLeftFaceBases m ↔ z ∈ slitScreenRightFaceBases m := by
  simp only [slitSideDualReflection,slitScreenLeftFaceBases,slitScreenRightFaceBases,
    Finset.mem_product,Finset.mem_Icc]
  omega

theorem slitSideDualBondReflection_pair (d : LatticeBond) :
    (slitSideDualBondReflection d).toSym2 = Sym2.map slitSideDualReflection d.toSym2 := by
  rcases d with ⟨⟨x,y⟩,ax⟩
  cases ax <;>
    simp [slitSideDualBondReflection,LatticeBond.toSym2,LatticeBond.source,LatticeBond.target,
      slitSideDualReflection]; omega

theorem slitSideDualBondReflection_primal_pair (d : LatticeBond) :
    (primalBondOfDual (slitSideDualBondReflection d)).toSym2 =
      Sym2.map (fun z : LatticeVertex => (-z.1,z.2)) (primalBondOfDual d).toSym2 := by
  rcases d with ⟨⟨x,y⟩,ax⟩
  cases ax <;>
    simp [slitSideDualBondReflection,primalBondOfDual,LatticeBond.toSym2,LatticeBond.source,
      LatticeBond.target] <;> omega

theorem slitSideEdgeReflection_physical (m : ℕ) (e : (slitBoxGraph (16*m)).edgeSet) :
    Sym2.map Subtype.val
      (PD.FK.configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso (16*m)) e).val =
    Sym2.map (fun z : LatticeVertex => (-z.1,z.2)) (Sym2.map Subtype.val e.val) := by
  change Sym2.map Subtype.val (Sym2.map (slitBoxGraphHorizontalReflectionIso (16*m)) e.val) = _
  rw [Sym2.map_map,Sym2.map_map]
  rfl

theorem slitSideActualDual_reflected_adj (m : ℕ)
    (F F' : Finset LatticeVertex)
    (hfaces : ∀ z, slitSideDualReflection z ∈ F' ↔ z ∈ F)
    (A : PD.FK.Configuration (slitBoxGraph (16*m))) {u v : LatticeVertex}
    (huv : (slitScreenActualConfigurationClosedDualGraph m A F).Adj u v) :
    (slitScreenActualConfigurationClosedDualGraph m (slitSideConfigurationReflection m A)
      F').Adj (slitSideDualReflection u) (slitSideDualReflection v) := by
  classical
  obtain ⟨d,e,he,hn,hdir,hu,hv⟩ := huv
  let er := PD.FK.configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso (16*m)) e
  have hep : (latticeBondEdge (primalBondOfDual (slitSideDualBondReflection d))) =
      slitBoxEdgeEmbedding (16*m) er := by
    apply Subtype.ext
    change (primalBondOfDual (slitSideDualBondReflection d)).toSym2 = Sym2.map Subtype.val er.val
    rw [slitSideDualBondReflection_primal_pair,slitSideEdgeReflection_physical]
    exact congrArg (Sym2.map (fun z : LatticeVertex => (-z.1,z.2))) (congrArg Subtype.val he)
  have hen : er ∉ slitSideConfigurationReflection m A := by
    simpa only [slitSideConfigurationReflection,PD.FK.configurationIso,Equiv.finsetCongr_apply,
      Finset.mem_map_equiv,er,Equiv.symm_apply_apply] using hn
  refine ⟨slitSideDualBondReflection d,er,hep,hen,?_,
    (hfaces u).mpr hu,(hfaces v).mpr hv⟩
  have hpair : s(slitSideDualReflection u,slitSideDualReflection v) =
      (slitSideDualBondReflection d).toSym2 := by
    rw [slitSideDualBondReflection_pair]
    rcases hdir with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · simp [LatticeBond.toSym2,Sym2.eq_swap]
  exact Sym2.eq_iff.mp hpair

theorem slitSideConfigurationReflection_involutive (m : ℕ) :
    Function.Involutive (slitSideConfigurationReflection m) := by
  intro A
  change (A.map _).map _ = A
  rw [Finset.map_map]
  have he : (PD.FK.configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso (16*m))).toEmbedding.trans
      (PD.FK.configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso (16*m))).toEmbedding =
      Function.Embedding.refl _ := by
    apply Function.Embedding.ext
    intro e
    apply Subtype.ext
    change Sym2.map (slitBoxGraphHorizontalReflectionIso (16*m))
      (Sym2.map (slitBoxGraphHorizontalReflectionIso (16*m)) e.val) = e.val
    rw [Sym2.map_map]
    have hf : (slitBoxGraphHorizontalReflectionIso (16*m)) ∘
        (slitBoxGraphHorizontalReflectionIso (16*m)) = id := by
      funext z
      apply Subtype.ext
      simp [slitBoxGraphHorizontalReflectionIso,slitBoxHorizontalReflectionVertexEquiv]
    rw [hf,Sym2.map_id]
    rfl
  rw [he,Finset.map_refl]

theorem slitSideActualCrossing_reflection_forward (m : ℕ)
    (F F' : Finset LatticeVertex)
    (hfaces : ∀ z, slitSideDualReflection z ∈ F' ↔ z ∈ F)
    (A : PD.FK.Configuration (slitBoxGraph (16*m)))
    (hA : ∃ x ∈ slitScreenBottomTerminals m F,
      ∃ y ∈ slitScreenTopTerminals m F,
        (slitScreenActualConfigurationClosedDualGraph m A F).Reachable x y) :
    ∃ x ∈ slitScreenBottomTerminals m F',
      ∃ y ∈ slitScreenTopTerminals m F',
        (slitScreenActualConfigurationClosedDualGraph m (slitSideConfigurationReflection m A) F').Reachable x y := by
  obtain ⟨x,hx,y,hy,⟨p⟩⟩ := hA
  let f : slitScreenActualConfigurationClosedDualGraph m A F →g
      slitScreenActualConfigurationClosedDualGraph m (slitSideConfigurationReflection m A) F' :=
    ⟨slitSideDualReflection,fun h => slitSideActualDual_reflected_adj m F F' hfaces A h⟩
  refine ⟨slitSideDualReflection x,⟨(hfaces x).mpr hx.1,hx.2⟩,
    slitSideDualReflection y,⟨(hfaces y).mpr hy.1,hy.2⟩,⟨p.map f⟩⟩

theorem slitScreenRightCrossingEvent_reflection_iff (m : ℕ) (hm : 1 ≤ m)
    (A : PD.FK.Configuration (slitBoxGraph (16*m))) :
    A ∈ slitScreenRightCrossingEvent m ↔
      slitSideConfigurationReflection m A ∈ slitScreenLeftCrossingEvent m := by
  rw [slitScreenRightCrossingEvent_eq_actualClosedDual m hm,
    slitScreenLeftCrossingEvent_eq_actualClosedDual m hm]
  constructor
  · exact slitSideActualCrossing_reflection_forward m _ _ (slitSideDualReflection_mem_faces m) A
  · intro h
    have hfaces : ∀ z, slitSideDualReflection z ∈ slitScreenRightFaceBases m ↔
        z ∈ slitScreenLeftFaceBases m := by
      intro z
      have h := slitSideDualReflection_mem_faces m (slitSideDualReflection z)
      simpa only [slitSideDualReflection_involutive z] using h.symm
    have hback := slitSideActualCrossing_reflection_forward m _ _ hfaces
      (slitSideConfigurationReflection m A) h
    simpa only [slitSideConfigurationReflection_involutive m A,
      slitScreenRightActualClosedDualCrossingEvent,Set.mem_ofPred_eq] using hback

theorem slitScreenLeftCrossingEvent_reflection_iff (m : ℕ) (hm : 1 ≤ m)
    (A : PD.FK.Configuration (slitBoxGraph (16*m))) :
    A ∈ slitScreenLeftCrossingEvent m ↔
      slitSideConfigurationReflection m A ∈ slitScreenRightCrossingEvent m := by
  have h := slitScreenRightCrossingEvent_reflection_iff m hm (slitSideConfigurationReflection m A)
  simpa only [slitSideConfigurationReflection_involutive m A] using h.symm

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
