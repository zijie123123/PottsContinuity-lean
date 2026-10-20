module

public import PottsContinuity.Thm4Plane.ScreenTargetCapComponent
public import PottsContinuity.Thm4Plane.ScreenTargetCapPlaneEvent
public import PottsContinuity.Infinite.FiniteGraphComparison
public import PottsContinuity.Foundations.BoxBoundary

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.Infinite

noncomputable section

local instance screenCapDomainVertexFinite (m : ℕ)
    (D : Set (SlitBoxVertex (16 * m))) :
    Finite {v : SlitBoxVertex (16 * m) // v ∈ D} := by infer_instance

local instance screenCapDomainEdgeFintype (m : ℕ)
    (R : PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m))) :
    Fintype ((PottsContinuity.FKC.FiniteFK.edgeRestriction
      (slitBoxGraph (16 * m)) R).induce D).edgeSet :=
  Fintype.ofFinite _

/-- The coordinate embedding of an induced slit-box domain into the plane. -/
def screenCapDomainVertexEmbedding (m : ℕ)
    (D : Set (SlitBoxVertex (16 * m))) :
    {v : SlitBoxVertex (16 * m) // v ∈ D} ↪ LatticeVertex where
  toFun v := v.val.val
  inj' := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact h

/-- The graph remaining after deleting `R`, restricted to the proposed cap
interior `D`. -/
def screenCapEdgeDeletedDomainGraph (m : ℕ)
    (R : PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m))) :
    SimpleGraph {v : SlitBoxVertex (16 * m) // v ∈ D} :=
  (PottsContinuity.FKC.FiniteFK.edgeRestriction
    (slitBoxGraph (16 * m)) R).induce D

/-- The induced edge-deleted domain still embeds in the whole square lattice. -/
theorem screenCapEdgeDeletedDomainGraph_map_to_PD (m : ℕ)
    (R : PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m))) :
    (screenCapEdgeDeletedDomainGraph m R D).map
      (screenCapDomainVertexEmbedding m D) ≤ PD.FK.squareLattice := by
  intro u v huv
  obtain ⟨u', v', hadj, rfl, rfl⟩ :=
    (SimpleGraph.map_adj (screenCapDomainVertexEmbedding m D)
      (screenCapEdgeDeletedDomainGraph m R D) u v).mp huv
  change ((PottsContinuity.FKC.FiniteFK.edgeRestriction
    (slitBoxGraph (16 * m)) R).induce D).Adj u' v' at hadj
  have hAdjRemoved : (PottsContinuity.FKC.FiniteFK.edgeRestriction
      (slitBoxGraph (16 * m)) R).Adj
      u'.val v'.val := SimpleGraph.induce_adj.mp hadj
  have hAdjSlit : (slitBoxGraph (16 * m)).Adj u'.val v'.val :=
    PottsContinuity.FKC.FiniteFK.edgeRestriction_le
      (slitBoxGraph (16 * m)) R hAdjRemoved
  have hAdjMap := (SimpleGraph.map_adj (screenSlitVertexEmbedding (16 * m))
    (slitBoxGraph (16 * m)) (u'.val.val) (v'.val.val)).mpr
      ⟨u'.val, v'.val, hAdjSlit, rfl, rfl⟩
  exact screenSlitGraph_map_to_PD (16 * m) hAdjMap

/-- A finite residual configuration connects the cap center to the indicated
part of the translated box boundary. -/
def screenCapBoundaryConnectionEvent (m : ℕ)
    (R : PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m)))
    (hcap : screenTargetCap m ⊆ D) :
    Set (PottsContinuity.FKC.FiniteFK.Configuration
      (screenCapEdgeDeletedDomainGraph m R D)) :=
  {A | ∃ v : {v : SlitBoxVertex (16 * m) // v ∈ D},
    v.val ∈ screenTargetCap m ∧
      (|v.val.val.1| = (m : ℤ) ∨ v.val.val.2 = -(15 * (m : ℤ))) ∧
      (PottsContinuity.FKC.FiniteFK.openGraph
        (screenCapEdgeDeletedDomainGraph m R D) A).Reachable
        ⟨slitBoxBottomCenterVertex (16 * m),
          hcap (screenTargetCap_bottomCenter_mem m)⟩ v}

/-- The source `E` path transfers to an edge-deleted induced domain once its
open edges in the cap are retained by the residual configuration. -/
theorem generalEScreenEvent_residualCapBoundaryConnection_of_adjacencyAgreement
    (m : ℕ)
    (R : PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m)))
    (hcap : screenTargetCap m ⊆ D)
    (A : PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m)))
    (hE : A ∈ generalEScreenEvent (16 * m))
    (B : PottsContinuity.FKC.FiniteFK.Configuration
      (screenCapEdgeDeletedDomainGraph m R D))
    (hAgree : ∀ {u v : SlitBoxVertex (16 * m)},
      (hu : u ∈ screenTargetCap m) → (hv : v ∈ screenTargetCap m) →
      (PottsContinuity.FKC.FiniteFK.openGraph
        (slitBoxGraph (16 * m)) A).Adj u v →
      (PottsContinuity.FKC.FiniteFK.openGraph
        (screenCapEdgeDeletedDomainGraph m R D) B).Adj
          ⟨u, hcap hu⟩ ⟨v, hcap hv⟩) :
    B ∈ screenCapBoundaryConnectionEvent m R D hcap := by
  obtain ⟨v, hv, hb, p, hsupport⟩ :=
    generalEScreenEvent_has_path_in_screenTargetCap m A hE
  let capBottom : {x : SlitBoxVertex (16 * m) // x ∈ screenTargetCap m} :=
    ⟨slitBoxBottomCenterVertex (16 * m), screenTargetCap_bottomCenter_mem m⟩
  let j : {x : SlitBoxVertex (16 * m) // x ∈ screenTargetCap m} →
      {x : SlitBoxVertex (16 * m) // x ∈ D} :=
    fun x => ⟨x.val, hcap x.property⟩
  let hom : (PottsContinuity.FKC.FiniteFK.openGraph
      (slitBoxGraph (16 * m)) A).induce (screenTargetCap m) →g
      PottsContinuity.FKC.FiniteFK.openGraph
        (screenCapEdgeDeletedDomainGraph m R D) B :=
    { toFun := j
      map_rel' := by
        intro x y hxy
        exact hAgree x.property y.property (SimpleGraph.induce_adj.mp hxy) }
  let pCap := p.induce (screenTargetCap m) hsupport
  have hpath := pCap.map hom
  change ∃ w : {x : SlitBoxVertex (16 * m) // x ∈ D},
      w.val ∈ screenTargetCap m ∧
        (|w.val.val.1| = (m : ℤ) ∨ w.val.val.2 = -(15 * (m : ℤ))) ∧
        (PottsContinuity.FKC.FiniteFK.openGraph
          (screenCapEdgeDeletedDomainGraph m R D) B).Reachable
            ⟨slitBoxBottomCenterVertex (16 * m),
              hcap (screenTargetCap_bottomCenter_mem m)⟩ w
  refine ⟨⟨v, hcap hv⟩, hv, hb, ?_⟩
  have hstart : j capBottom =
      ⟨slitBoxBottomCenterVertex (16 * m),
        hcap (screenTargetCap_bottomCenter_mem m)⟩ := rfl
  have hend : j ⟨v, hv⟩ = ⟨v, hcap hv⟩ := rfl
  have hreach := hpath.reachable
  change (PottsContinuity.FKC.FiniteFK.openGraph
      (screenCapEdgeDeletedDomainGraph m R D) B).Reachable
        (j capBottom) (j ⟨v, hv⟩) at hreach
  rw [hstart, hend] at hreach
  exact hreach

end
end PottsContinuity.Thm4Plane
