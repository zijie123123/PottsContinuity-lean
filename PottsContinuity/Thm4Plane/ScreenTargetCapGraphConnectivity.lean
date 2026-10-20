module

public import PottsContinuity.Thm4Plane.ScreenTargetCap
public import PottsContinuity.FKC.FiniteFK.RectangleConnectivity
public import PottsContinuity.FKC.FiniteFK.EdgeRestriction

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK

/-- An edge is internal to the clipped cap when both endpoints lie in that
cap. -/
def screenTargetCapInternalEdge (m : ℕ)
    (e : (slitBoxGraph (16 * m)).edgeSet) : Prop :=
  ∃ u v : screenTargetCap m, e.val = s(u.val, v.val)

def screenTargetCapRectangleVertex (m : ℕ)
    (v : screenTargetCap m) : RectangleVertex
      (-(m : ℤ), -(16 * (m : ℤ))) (2 * m) m := by
  refine ⟨v.val.val, ?_⟩
  rw [mem_latticeRectangle]
  have hv := v.property
  dsimp [screenTargetCap] at hv
  constructor
  · constructor <;> omega
  · constructor <;> omega

def screenTargetCapRectToCap (m : ℕ)
    (v : RectangleVertex
      (-(m : ℤ), -(16 * (m : ℤ))) (2 * m) m) : screenTargetCap m := by
  refine ⟨⟨v.val, ?_⟩, ?_⟩
  · rw [mem_latticeRectangle]
    have hv := (mem_latticeRectangle _ _ _ _).mp v.property
    constructor
    · constructor <;> omega
    · constructor <;> omega
  · have hv := (mem_latticeRectangle _ _ _ _).mp v.property
    dsimp [screenTargetCap]
    exact ⟨hv.1.1, by omega, hv.2.1, by omega⟩

private theorem screenTargetCapRectToCap_val (m : ℕ)
    (v : RectangleVertex
      (-(m : ℤ), -(16 * (m : ℤ))) (2 * m) m) :
    (screenTargetCapRectToCap m v).val.val = v.val := rfl

def screenTargetCapRectangleEmbedding (m : ℕ) (hm : 1 ≤ m) :
    rectangleGraph (-(m : ℤ), -(16 * (m : ℤ))) (2 * m) m ↪g
      (slitBoxGraph (16 * m)).induce (screenTargetCap m) where
  toFun := screenTargetCapRectToCap m
  inj' := by
    intro u v h
    apply Subtype.ext
    exact congrArg (fun z : screenTargetCap m => z.val.val) h
  map_rel_iff' := by
    intro u v
    change (slitBoxGraph (16 * m)).Adj
        (screenTargetCapRectToCap m u).val
        (screenTargetCapRectToCap m v).val ↔
      (rectangleGraph (-(m : ℤ), -(16 * (m : ℤ))) (2 * m) m).Adj u v
    rw [slitBoxGraph_adj_iff, rectangleGraph_adj_iff,
      screenTargetCapRectToCap_val, screenTargetCapRectToCap_val]
    constructor
    · intro huv
      exact huv.1
    · intro huv
      refine ⟨?_, ?_⟩
      · exact huv
      · intro hwire
        rcases hwire with ⟨⟨_, hu0, huy⟩, ⟨_, hv0, hvy⟩⟩
        have huCap := (screenTargetCapRectToCap m u).property
        have hvCap := (screenTargetCapRectToCap m v).property
        dsimp [screenTargetCap] at huCap hvCap
        rw [screenTargetCapRectToCap_val] at huCap hvCap
        omega

/-- The induced graph on the clipped target cap is connected. The cap is a
rectangle strictly below the wired arc, so the slit deletion removes none of
its edges. -/
theorem screenTargetCap_inducedGraph_reachable (m : ℕ) (hm : 1 ≤ m)
    (u v : screenTargetCap m) :
    ((slitBoxGraph (16 * m)).induce (screenTargetCap m)).Reachable u v := by
  let e := screenTargetCapRectangleEmbedding m hm
  let ur := screenTargetCapRectangleVertex m u
  let vr := screenTargetCapRectangleVertex m v
  have hrect := rectangleGraph_reachable_all
    (-(m : ℤ), -(16 * (m : ℤ))) (2 * m) m ur vr
  have hmap := SimpleGraph.Reachable.map e.toHom hrect
  have heqU : e.toHom ur = u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have heqV : e.toHom vr = v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [heqU, heqV] at hmap
  exact hmap

/-- The cap remains a single component in any graph that retains all of its
induced slit-box edges. This is the deterministic input needed when removing
the bonds crossed by the exterior dual arch. -/
theorem screenTargetCap_reachable_of_all_cap_edges_retained
    (m : ℕ) (hm : 1 ≤ m)
    (H : SimpleGraph (SlitBoxVertex (16 * m)))
    (hkeep : ∀ ⦃u v : screenTargetCap m⦄,
      ((slitBoxGraph (16 * m)).induce (screenTargetCap m)).Adj u v →
        H.Adj u.val v.val)
    (u v : screenTargetCap m) :
    H.Reachable u.val v.val := by
  let φ : (slitBoxGraph (16 * m)).induce (screenTargetCap m) →g H :=
    { toFun := fun z => z.val
      map_rel' := by
        intro x y hxy
        exact hkeep hxy }
  exact SimpleGraph.Reachable.map φ
    (screenTargetCap_inducedGraph_reachable m hm u v)

/-- Deleting any set of edges disjoint from the cap's internal bonds leaves
the cap connected in the resulting graph. -/
theorem screenTargetCap_reachable_in_edgeRestriction_of_no_internal_removal
    (m : ℕ) (hm : 1 ≤ m)
    (R : Configuration (slitBoxGraph (16 * m)))
    (hR : ∀ e ∈ R, ¬ screenTargetCapInternalEdge m e)
    (u v : screenTargetCap m) :
    (edgeRestriction (slitBoxGraph (16 * m)) R).Reachable u.val v.val := by
  let G := slitBoxGraph (16 * m)
  let H := edgeRestriction G R
  have hkeep : ∀ ⦃x y : screenTargetCap m⦄,
      (G.induce (screenTargetCap m)).Adj x y → H.Adj x.val y.val := by
    intro x y hxy
    have hG : G.Adj x.val y.val := SimpleGraph.induce_adj.mp hxy
    have he : s(x.val, y.val) ∈ G.edgeSet := G.mem_edgeSet.mpr hG
    have hnotR : (⟨s(x.val, y.val), he⟩ : G.edgeSet) ∉ R := by
      intro heR
      exact hR _ heR ⟨x, y, rfl⟩
    have hHedge : s(x.val, y.val) ∈ H.edgeSet := by
      rw [edgeRestriction_edgeSet]
      refine ⟨he, ?_⟩
      intro hopen
      exact hnotR ((coe_mem_openEdges_iff G R ⟨s(x.val, y.val), he⟩).mp hopen)
    exact H.mem_edgeSet.mpr hHedge
  exact screenTargetCap_reachable_of_all_cap_edges_retained m hm H hkeep u v

end PottsContinuity.Thm4Plane
