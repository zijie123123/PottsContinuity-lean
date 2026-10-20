module

public import PottsContinuity.PlanarMixed.FiniteSlit.ForcedDualState
public import PottsContinuity.PlanarMixed.FiniteSlit.IsolatedWiring
public import PottsContinuity.PD.FK.ComponentBoundarySupport

/-! The finite induced dual boundary is dominated by the canonical joined
B'-K' wiring, up to the proved irrelevant isolated exterior faces. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial PD.Duality BD12 DualityExt
noncomputable section

/-- All forced-open dual endpoints lie on the original slit face column. -/
theorem dualExteriorState_endpoint_on_slit (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (e : (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M).edgeSet)
    (he : e ∈ (dualExteriorState M x y).val)
    (z : RectangleDualVertex (x-(M : ℤ),0) (2*M-1) M) (hz : z ∈ e.val) :
    z.val.1 = x-1 ∧ y ≤ z.val.2 := by
  obtain ⟨p,rfl⟩ := (rectangleDualEdgeEquiv (x-(M : ℤ),0) (2*M-1) M).surjective e
  let b := rectanglePrimalEdgeBondEquiv (x-(M : ℤ),0) (2*M-1) M p
  have hp : originalBondEdge M x b.val b.property.1 b.property.2 = p :=
    (rectanglePrimalEdgeBondEquiv (x-(M : ℤ),0) (2*M-1) M).symm_apply_apply p
  rw [← hp] at he hz
  have hslit := (dualExteriorState_mem_crossing_iff_slit M x y hM hy hyM b.val _ _).mp he
  have hpair := congrArg Subtype.val (crossingEdge_global M x b.val b.property.1 b.property.2)
  change Sym2.map Subtype.val
    (rectangleDualEdgeEquiv (x-(M : ℤ),0) (2*M-1) M
      (originalBondEdge M x b.val b.property.1 b.property.2)).val =
      (dualBondOfPrimal b.val).toSym2 at hpair
  have hz' : z.val ∈ (dualBondOfPrimal b.val).toSym2 := by
    rw [← hpair]
    exact Sym2.mem_map.mpr ⟨z,hz,rfl⟩
  rcases b with ⟨⟨⟨a,k⟩,ax⟩,hs,ht⟩
  cases ax
  · rcases (Sym2.mem_iff').mp hz' with hz' | hz'
    all_goals
      have hx := congrArg Prod.fst hz'
      have hk := congrArg Prod.snd hz'
      simp only [dualBondOfPrimal,LatticeBond.source,LatticeBond.target] at hx hk
      simp only at hslit
      exact ⟨by omega,by omega⟩
  · cases hslit.1

/-- Which embedded cells meet the actual wired rectangle exterior. -/
theorem cellEmbedding_mem_rectangleBoundary_iff (M : ℕ) (x : ℤ) (hM : 2 ≤ M)
    (u : Vertex M x) :
    cellEmbedding M x hM u ∈
      (rectangleDualBoundaryCondition (x-(M : ℤ),0) (2*M-1) M).boundary ↔
        u.val.1 = x-(M : ℤ) ∨ u.val.2 = 0 := by
  have hu := (mem_rectangle_iff M x (by omega) u.val).mp u.property
  have hw : ((2*M-1 : ℕ) : ℤ) = 2*(M : ℤ)-1 := by omega
  change faceMap x u.val ∈ rectangleDualBoundary (x-(M : ℤ),0) (2*M-1) M ↔ _
  simp only [rectangleDualBoundary,Finset.mem_filter]
  have hexp := faceMap_mem_expanded M x hM u
  dsimp only [faceMap] at hexp
  simp only [true_and,rectangleDualInterior,Finset.mem_filter,hexp,
    faceMap,hw,zero_add]
  omega

/-- A forced-open chain endpoint or rectangle exterior pulls back to B', K',
or one of the explicitly isolated extra exterior faces. -/
theorem cellEmbedding_boundary_or_slit_subset (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (u : Vertex M x)
    (hu : cellEmbedding M x hM u ∈
        (rectangleDualBoundaryCondition (x-(M : ℤ),0) (2*M-1) M).boundary ∨
      ((cellEmbedding M x hM u).val.1 = x-1 ∧ y ≤ (cellEmbedding M x hM u).val.2)) :
    u ∈ (dualBottom M x ∪ dualRay M x y) ∪ irrelevantExterior M x := by
  rcases hu with hb | hk
  · rcases (cellEmbedding_mem_rectangleBoundary_iff M x hM u).mp hb with hl | hb
    · exact Or.inr (Or.inl hl)
    · by_cases huB : u ∈ dualBottom M x
      · exact Or.inl (Or.inl huB)
      · exact Or.inr (Or.inr ⟨hb,huB⟩)
  · apply Or.inl ∘ Or.inr
    change u.val.1 = x ∧ y+1 ≤ u.val.2
    change (2*x-1-u.val.1 = x-1 ∧ y ≤ u.val.2-1) at hk
    constructor <;> omega

/-- Every actual induced relation is below joined marked-arc wiring plus
isolated faces. This suffices for the mixed probability estimate. -/
theorem inducedDualBoundary_partition_le_extra (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    (inducedDualBoundary M x y hM).partition ≤
      (BoundaryCondition.wired ((dualBottom M x ∪ dualRay M x y) ∪ irrelevantExterior M x)).partition := by
  let ξ := rectangleDualBoundaryCondition (x-(M : ℤ),0) (2*M-1) M
  let S : Set (RectangleDualVertex (x-(M : ℤ),0) (2*M-1) M) :=
    {z | z.val.1 = x-1 ∧ y ≤ z.val.2}
  have hup := componentSetoid_le_wired_union_of_edge_endpoints ξ S
    (dualExteriorState M x y).val
    (fun e he z hz => dualExteriorState_endpoint_on_slit M x y hM hy hyM e he z hz)
  intro u v huv
  have hbig := hup huv
  rcases (BoundaryCondition.wired_rel (ξ.boundary ∪ S) _ _).mp hbig with heq | ⟨hu,hv⟩
  · exact (BoundaryCondition.wired_rel _ u v).mpr (Or.inl ((cellEmbedding M x hM).injective heq))
  · exact (BoundaryCondition.wired_rel _ u v).mpr (Or.inr
      ⟨cellEmbedding_boundary_or_slit_subset M x y hM u hu,
       cellEmbedding_boundary_or_slit_subset M x y hM v hv⟩)

end
end PottsContinuity.PlanarMixed.FiniteSlit
