module

public import PottsContinuity.Thm4Plane.ScreenActiveConnectorSourcePaths
public import PottsContinuity.FKC.FiniteFK.SlitScreenDualEdgeClassification
public import PottsContinuity.FKC.FiniteFK.SlitBoxConfigurationExtension
public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC.Medial

noncomputable section

abbrev SlitRStarGraph (m : ℕ) :=
  PottsContinuity.PD.FK.rectangleGraph (slitScreenRStarBase m)
    (slitScreenRStarSide m) (slitScreenRStarSide m)

abbrev SlitRStarVertex (m : ℕ) :=
  PottsContinuity.PD.FK.RectangleVertex (slitScreenRStarBase m)
    (slitScreenRStarSide m) (slitScreenRStarSide m)

local instance rstarDualEdgeFintype (m : ℕ) :
    Fintype (SlitRStarGraph m).edgeSet := Fintype.ofFinite _

local instance rstarDualEdgeDecidableEq (m : ℕ) :
    DecidableEq (SlitRStarGraph m).edgeSet := Classical.decEq _

local instance rstarSourceEdgeDecidableEq (m : ℕ) :
    DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _

local instance rstarSourceEdgeFintype (m : ℕ) :
    Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _

local instance rstarConfigMeasurableSpace (m : ℕ) :
    MeasurableSpace (PottsContinuity.PD.FK.Configuration
      (SlitRStarGraph m)) :=
  PottsContinuity.PD.FK.configurationMeasurableSpace _

structure SlitRStarEdgeBridge (m : ℕ) (hm : 1 ≤ m)
    (e : (SlitRStarGraph m).edgeSet) where
  dualBond : PottsContinuity.FKC.Medial.LatticeBond
  primalEdge : (slitBoxGraph (16 * m)).edgeSet
  endpoints : dualBond.source ∈ slitScreenMiddleFaceBases m ∧
    dualBond.target ∈ slitScreenMiddleFaceBases m
  crosses : latticeBondEdge (primalBondOfDual dualBond) =
    slitBoxEdgeEmbedding (16 * m) primalEdge
  pairEq : dualBond.toSym2 =
    Sym2.map (fun z : SlitRStarVertex m => z.val) e.val

 theorem slitRStarVertex_memMiddle (m : ℕ)
    (hm : 1 ≤ m) (u : SlitRStarVertex m) :
    u.val ∈ slitScreenMiddleFaceBases m := by
  change u.val ∈ Finset.Icc (-(5 * (m : ℤ))) (5 * (m : ℤ) - 1) ×ˢ
    Finset.Icc (-(12 * (m : ℤ))) (-(2 * (m : ℤ)) - 1)
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  have hu := (PottsContinuity.PD.FK.mem_latticeRectangle
    (slitScreenRStarBase m) u.val (slitScreenRStarSide m)
    (slitScreenRStarSide m)).mp u.property
  dsimp [slitScreenRStarBase, slitScreenRStarSide] at hu ⊢
  have hm' : 0 < m := by omega
  constructor <;> constructor <;> omega

 theorem slitRStarEdge_dualBond (m : ℕ)
    (e : (SlitRStarGraph m).edgeSet) :
    ∃ d : PottsContinuity.FKC.Medial.LatticeBond,
      d.toSym2 = Sym2.map (fun z : SlitRStarVertex m => z.val) e.val := by
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  have hAdj₀ : (SlitRStarGraph m).Adj p.1 p.2 := by
    apply (SlitRStarGraph m).mem_edgeSet.mp
    have he : e.1 ∈ (SlitRStarGraph m).edgeSet := e.2
    rw [← hrepr] at he
    exact he
  have hAdjPD := (PottsContinuity.PD.FK.rectangleGraph_adj_iff
    (slitScreenRStarBase m) (slitScreenRStarSide m)
    (slitScreenRStarSide m) p.1 p.2).mp hAdj₀
  have hAdjFKC : PottsContinuity.FKC.squareLattice.Adj
      p.1.val p.2.val := by
    rw [PottsContinuity.PD.FK.squareLattice_adj_iff] at hAdjPD
    rw [PottsContinuity.FKC.squareLattice_adj_iff]
    exact hAdjPD
  let fke : PottsContinuity.FKC.squareLattice.edgeSet :=
    ⟨s(p.1.val, p.2.val), hAdjFKC⟩
  let d := PottsContinuity.FKC.Medial.wholePlaneBondEdgeEquiv.symm fke
  refine ⟨d, ?_⟩
  have hd := congrArg Subtype.val
    (Equiv.apply_symm_apply
      PottsContinuity.FKC.Medial.wholePlaneBondEdgeEquiv fke)
  have hmap : Sym2.map (fun z : SlitRStarVertex m => z.val)
      (s(p.1, p.2)) = Sym2.map (fun z : SlitRStarVertex m => z.val) e.val := by
    exact congrArg (Sym2.map (fun z : SlitRStarVertex m => z.val)) hrepr
  have hpair : d.toSym2 =
      Sym2.map (fun z : SlitRStarVertex m => z.val) e.val := by
    calc
      d.toSym2 = s(p.1.val, p.2.val) := by
        simpa [d, fke, PottsContinuity.FKC.Medial.wholePlaneBondEdgeEquiv,
          PottsContinuity.FKC.Medial.latticeBondEdge] using hd
      _ = Sym2.map (fun z : SlitRStarVertex m => z.val) (s(p.1, p.2)) := by
        simp only [Sym2.map_mk]
      _ = Sym2.map (fun z : SlitRStarVertex m => z.val) e.val := hmap
  exact hpair

noncomputable def slitRStarEdgeBridge (m : ℕ) (hm : 1 ≤ m)
    (e : (SlitRStarGraph m).edgeSet) : SlitRStarEdgeBridge m hm e := by
  classical
  let hdual := slitRStarEdge_dualBond m e
  let d := Classical.choose hdual
  have hpair : d.toSym2 =
      Sym2.map (fun z : SlitRStarVertex m => z.val) e.val := by
    simpa only [d] using Classical.choose_spec hdual
  have hpair' : s(d.source, d.target) =
      Sym2.map (fun z : SlitRStarVertex m => z.val) e.val := by
    simpa [PottsContinuity.FKC.Medial.LatticeBond.toSym2] using hpair
  have hpairOut : s(d.source, d.target) =
      s(e.1.out.1.val, e.1.out.2.val) := by
    have hrepr : s(e.1.out.1, e.1.out.2) = e.1 := Quot.out_eq _
    have hreprMap : Sym2.map (fun z : SlitRStarVertex m => z.val) e.val =
        Sym2.map (fun z : SlitRStarVertex m => z.val)
          (s(e.1.out.1, e.1.out.2)) :=
      (congrArg (Sym2.map (fun z : SlitRStarVertex m => z.val)) hrepr).symm
    calc
      s(d.source, d.target) =
          Sym2.map (fun z : SlitRStarVertex m => z.val) e.val := hpair'
      _ = Sym2.map (fun z : SlitRStarVertex m => z.val)
          (s(e.1.out.1, e.1.out.2)) := hreprMap
      _ = s(e.1.out.1.val, e.1.out.2.val) := by simp
  have hdSource : d.source ∈ slitScreenMiddleFaceBases m := by
    rcases Sym2.eq_iff.mp hpairOut with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simpa [hs] using slitRStarVertex_memMiddle m hm e.1.out.1
    · simpa [hs] using slitRStarVertex_memMiddle m hm e.1.out.2
  have hdTarget : d.target ∈ slitScreenMiddleFaceBases m := by
    rcases Sym2.eq_iff.mp hpairOut with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simpa [ht] using slitRStarVertex_memMiddle m hm e.1.out.2
    · simpa [ht] using slitRStarVertex_memMiddle m hm e.1.out.1
  let hsource := slitScreenMiddleFaceBond_primalBondInSlit m hm d hdSource hdTarget
  let u := Classical.choose hsource
  let hsource' := Classical.choose_spec hsource
  let v := Classical.choose hsource'
  have hu : u.val = (primalBondOfDual d).source :=
    (Classical.choose_spec hsource').1
  have hv : v.val = (primalBondOfDual d).target :=
    (Classical.choose_spec hsource').2.1
  have he : s(u, v) ∈ (slitBoxGraph (16 * m)).edgeSet :=
    (Classical.choose_spec hsource').2.2
  let pe : (slitBoxGraph (16 * m)).edgeSet := ⟨s(u, v), he⟩
  have hcross : latticeBondEdge (primalBondOfDual d) =
      slitBoxEdgeEmbedding (16 * m) pe := by
    apply Subtype.ext
    rw [PottsContinuity.FKC.FiniteFK.slitBoxEdgeEmbedding_val]
    change (PottsContinuity.FKC.Medial.LatticeBond.toSym2
        (PottsContinuity.FKC.Medial.primalBondOfDual d)) =
      Sym2.map Subtype.val (s(u, v))
    change s((PottsContinuity.FKC.Medial.primalBondOfDual d).source,
        (PottsContinuity.FKC.Medial.primalBondOfDual d).target) = _
    simp only [Sym2.map_mk]
    rw [hu, hv]
  refine ⟨d, pe, ⟨hdSource, hdTarget⟩, hcross, ?_⟩
  simpa [pe, Sym2.map_mk] using hpair

noncomputable def slitRStarDualConfiguration (m : ℕ) (hm : 1 ≤ m)
    (A : PottsContinuity.PD.FK.Configuration (slitBoxGraph (16 * m))) :
    PottsContinuity.PD.FK.Configuration (SlitRStarGraph m) := by
  classical
  exact Finset.univ.filter fun e => (slitRStarEdgeBridge m hm e).primalEdge ∉ A

@[simp] theorem mem_slitRStarDualConfiguration (m : ℕ) (hm : 1 ≤ m)
    (A : PottsContinuity.PD.FK.Configuration (slitBoxGraph (16 * m)))
    (e : (SlitRStarGraph m).edgeSet) :
    e ∈ slitRStarDualConfiguration m hm A ↔
      (slitRStarEdgeBridge m hm e).primalEdge ∉ A := by
  simp [slitRStarDualConfiguration]

end
end PottsContinuity.Thm4Plane
