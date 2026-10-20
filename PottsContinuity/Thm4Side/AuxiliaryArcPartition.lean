module

public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain
public import PottsContinuity.PlanarMixed.AuxiliaryArcRealization

@[expose] public section

namespace PottsContinuity.Thm4Side

open PottsContinuity.PD.FK
open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.PlanarMixed

noncomputable section

local instance sideRingEdgeFintype (n : ℕ) :
    Fintype (PD.FK.rectangleGraph
      (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
      (2 * (n + 1)) (2 * (n + 1))).edgeSet := Fintype.ofFinite _

local instance sideRingEdgeDecidableEq (n : ℕ) :
    DecidableEq (PD.FK.rectangleGraph
      (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
      (2 * (n + 1)) (2 * (n + 1))).edgeSet := Classical.decEq _

abbrev SideHostVertex (n : ℕ) :=
  PD.FK.RectangleVertex
    (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
    (2 * (n + 1)) (2 * (n + 1))

abbrev SideHostGraph (n : ℕ) := PD.FK.rectangleGraph
  (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
  (2 * (n + 1)) (2 * (n + 1))

 theorem slitSourceArcVertex_mem (n k : ℕ) (hk : k ≤ n) :
    (0, (k : ℤ)) ∈ FKC.latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) := by
  rw [FKC.mem_latticeRectangle]
  push_cast
  omega

noncomputable def slitSourceArcVertex (n k : ℕ) (hk : k ≤ n) :
    SlitBoxVertex n :=
  ⟨(0, (k : ℤ)), slitSourceArcVertex_mem n k hk⟩

private theorem slitSourceArcVertex_mem_wiredArc (n k : ℕ) (hk : k ≤ n) :
    slitSourceArcVertex n k hk ∈ slitBoxWiredArc n := by
  rw [mem_slitBoxWiredArc_iff]
  change (0 : ℤ) = 0 ∧ 0 ≤ (k : ℤ) ∧ (k : ℤ) ≤ (n : ℤ)
  exact ⟨rfl, by omega, by exact_mod_cast hk⟩

/-- Embed the slit box into a free rectangular host extended by one layer. -/
noncomputable def slitBoxAuxiliaryHostEmbedding (n : ℕ) :
    SlitBoxVertex n ↪ SideHostVertex n where
  toFun v := ⟨v.val, by
    have hv := v.property
    rw [FKC.mem_latticeRectangle] at hv
    rw [PD.FK.mem_latticeRectangle]
    push_cast at hv ⊢
    omega⟩
  inj' := by
    intro u v h
    have hval : u.val = v.val :=
      congrArg (fun x : SideHostVertex n => x.val) h
    exact Subtype.ext hval

 theorem slitHostArcVertex_mem (n k : ℕ) (hk : k ≤ n) :
    (0, (k : ℤ)) ∈ PD.FK.latticeRectangle
      (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
      (2 * (n + 1)) (2 * (n + 1)) := by
  rw [PD.FK.mem_latticeRectangle]
  push_cast
  omega

noncomputable def slitHostArcVertex (n k : ℕ) (hk : k ≤ n) :
    SideHostVertex n :=
  ⟨(0, (k : ℤ)), slitHostArcVertex_mem n k hk⟩

/-- The image in the host of the retained slit-box Dobrushin arc. -/
def slitBoxAuxiliaryHostArc (n : ℕ) : Set (SideHostVertex n) :=
  slitBoxAuxiliaryHostEmbedding n '' (slitBoxWiredArc n : Set (SlitBoxVertex n))

/-- The host bonds along the wired arc, fixed open to realize its partition. -/
noncomputable def slitBoxAuxiliaryArcRing (n : ℕ) :
    PD.FK.Configuration (SideHostGraph n) := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ u v : SideHostVertex n,
      u ∈ slitBoxAuxiliaryHostArc n ∧ v ∈ slitBoxAuxiliaryHostArc n ∧
        e.val = s(u, v)

theorem mem_slitBoxAuxiliaryArcRing_iff (n : ℕ)
    (e : (SideHostGraph n).edgeSet) :
    e ∈ slitBoxAuxiliaryArcRing n ↔
      ∃ u v : SideHostVertex n,
        u ∈ slitBoxAuxiliaryHostArc n ∧ v ∈ slitBoxAuxiliaryHostArc n ∧
          e.val = s(u, v) := by
  classical
  simp [slitBoxAuxiliaryArcRing]

private theorem slitHostArc_adjacent (n k : ℕ) (hk : k < n) :
    (SideHostGraph n).Adj
      (slitHostArcVertex n k (Nat.le_of_lt hk))
      (slitHostArcVertex n (k + 1) (Nat.succ_le_of_lt hk)) := by
  rw [PD.FK.rectangleGraph_adj_iff]
  apply (PD.FK.squareLattice_adj_iff _ _).mpr
  simp only [slitHostArcVertex]
  exact Or.inr ⟨by simp, Or.inl (by norm_cast)⟩

private theorem slitArcHostOpenWalk (n : ℕ) :
    ∀ k d : ℕ, (hk : k + d ≤ n) →
      Nonempty ((PD.FK.openGraph (SideHostGraph n) (slitBoxAuxiliaryArcRing n)).Walk
        (slitHostArcVertex n k (by omega))
        (slitHostArcVertex n (k + d) (by omega))) := by
  intro k d hk
  induction d generalizing k with
  | zero =>
      have hend : slitHostArcVertex n (k + 0) (by omega) =
          slitHostArcVertex n k (by omega) := by
        apply Subtype.ext
        rfl
      exact ⟨(SimpleGraph.Walk.nil :
        (PD.FK.openGraph (SideHostGraph n) (slitBoxAuxiliaryArcRing n)).Walk
          (slitHostArcVertex n k (by omega))
          (slitHostArcVertex n k (by omega))).copy rfl hend⟩
  | succ d ih =>
      have hkn : k < n := by omega
      have hnext : k + 1 ≤ n := Nat.succ_le_of_lt hkn
      let u := slitHostArcVertex n k (Nat.le_of_lt hkn)
      let v := slitHostArcVertex n (k + 1) hnext
      have hadj : (SideHostGraph n).Adj u v := by
        exact slitHostArc_adjacent n k hkn
      have hu : u ∈ slitBoxAuxiliaryHostArc n := by
        refine ⟨slitSourceArcVertex n k (Nat.le_of_lt hkn),
          slitSourceArcVertex_mem_wiredArc n k (Nat.le_of_lt hkn), ?_⟩
        apply Subtype.ext
        rfl
      have hv : v ∈ slitBoxAuxiliaryHostArc n := by
        refine ⟨slitSourceArcVertex n (k + 1) hnext,
          slitSourceArcVertex_mem_wiredArc n (k + 1) hnext, ?_⟩
        apply Subtype.ext
        rfl
      have he : (⟨s(u, v), (SideHostGraph n).mem_edgeSet.mpr hadj⟩ :
          (SideHostGraph n).edgeSet) ∈ slitBoxAuxiliaryArcRing n := by
        rw [mem_slitBoxAuxiliaryArcRing_iff]
        exact ⟨u, v, hu, hv, rfl⟩
      have hOpen : (PD.FK.openGraph (SideHostGraph n)
          (slitBoxAuxiliaryArcRing n)).Adj u v := by
        rw [PD.FK.openGraph_adj]
        unfold PD.FK.openEdges
        exact (Set.mem_image _ _ _).mpr
          ⟨⟨s(u, v), (SideHostGraph n).mem_edgeSet.mpr hadj⟩,
            Finset.mem_coe.mpr he, rfl⟩
      have htail := ih (k + 1) (by omega)
      obtain ⟨tail⟩ := htail
      have hend : slitHostArcVertex n ((k + 1) + d) (by omega) =
          slitHostArcVertex n (k + (d + 1)) (by omega) := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · change (((k + 1) + d : ℕ) : ℤ) = ((k + (d + 1) : ℕ) : ℤ)
          congr 1; omega
      have hhead : u = slitHostArcVertex n k (by omega) := by
        apply Subtype.ext
        rfl
      have htailStart : v = slitHostArcVertex n (k + 1) (by omega) := by
        apply Subtype.ext
        rfl
      exact ⟨(SimpleGraph.Walk.cons hOpen (tail.copy htailStart.symm hend))
        |>.copy hhead.symm rfl⟩

private theorem slitArcRing_connected (n : ℕ)
    {u v : SideHostVertex n}
    (hu : u ∈ slitBoxAuxiliaryHostArc n)
    (hv : v ∈ slitBoxAuxiliaryHostArc n) :
    PD.FK.ActualConnected (SideHostGraph n) (slitBoxAuxiliaryArcRing n) u v := by
  change u ∈ slitBoxAuxiliaryHostEmbedding n ''
    (slitBoxWiredArc n : Set (SlitBoxVertex n)) at hu
  change v ∈ slitBoxAuxiliaryHostEmbedding n ''
    (slitBoxWiredArc n : Set (SlitBoxVertex n)) at hv
  rcases (Set.mem_image _ _ _).mp hu with ⟨u₀, hu₀, rfl⟩
  rcases (Set.mem_image _ _ _).mp hv with ⟨v₀, hv₀, rfl⟩
  have hu' := (mem_slitBoxWiredArc_iff n u₀).mp hu₀
  have hv' := (mem_slitBoxWiredArc_iff n v₀).mp hv₀
  let k := u₀.val.2.toNat
  let l := v₀.val.2.toNat
  have hk : (k : ℤ) = u₀.val.2 := by
    dsimp [k]
    exact Int.toNat_of_nonneg hu'.2.1
  have hl : (l : ℤ) = v₀.val.2 := by
    dsimp [l]
    exact Int.toNat_of_nonneg hv'.2.1
  have hkle : k ≤ n := by
    have : (k : ℤ) ≤ n := by rw [hk]; exact hu'.2.2
    exact_mod_cast this
  have hllE : l ≤ n := by
    have : (l : ℤ) ≤ n := by rw [hl]; exact hv'.2.2
    exact_mod_cast this
  have hku : slitHostArcVertex n k hkle = slitBoxAuxiliaryHostEmbedding n u₀ := by
    apply Subtype.ext
    apply Prod.ext
    · exact hu'.1.symm
    · exact hk
  have hlv : slitHostArcVertex n l hllE = slitBoxAuxiliaryHostEmbedding n v₀ := by
    apply Subtype.ext
    apply Prod.ext
    · exact hv'.1.symm
    · exact hl
  by_cases hkl : k ≤ l
  · have hwalk := slitArcHostOpenWalk n k (l - k) (by omega)
    have hEq : k + (l - k) = l := by omega
    obtain ⟨p⟩ := hwalk
    have hstart : slitHostArcVertex n k (by omega) =
        slitBoxAuxiliaryHostEmbedding n u₀ := hku
    have hend : slitHostArcVertex n (k + (l - k)) (by omega) =
        slitBoxAuxiliaryHostEmbedding n v₀ := by
      apply Subtype.ext
      change (0, ((k + (l - k) : ℕ) : ℤ)) = v₀.val
      apply Prod.ext
      · exact hv'.1.symm
      · rw [hEq, hl]
    exact (PD.FK.actualConnected_iff_walk _ _ _ _).mpr ⟨p.copy hstart hend⟩
  · have hwalk := slitArcHostOpenWalk n l (k - l) (by omega)
    have hEq : l + (k - l) = k := by omega
    obtain ⟨p⟩ := hwalk
    have hstart : slitHostArcVertex n l (by omega) =
        slitBoxAuxiliaryHostEmbedding n v₀ := hlv
    have hend : slitHostArcVertex n (l + (k - l)) (by omega) =
        slitBoxAuxiliaryHostEmbedding n u₀ := by
      apply Subtype.ext
      change (0, ((l + (k - l) : ℕ) : ℤ)) = u₀.val
      apply Prod.ext
      · exact hu'.1.symm
      · rw [hEq, hk]
    exact (PD.FK.actualConnected_iff_walk _ _ _ _).mpr ⟨p.reverse.copy hend hstart⟩

theorem slitBoxAuxiliaryHostEmbedding_graph_le (n : ℕ) :
    (slitBoxGraph n).map (slitBoxAuxiliaryHostEmbedding n) ≤ SideHostGraph n := by
  intro u v huv
  rw [SimpleGraph.map_adj] at huv
  rcases huv with ⟨u₀, v₀, hadj, rfl, rfl⟩
  rw [PD.FK.rectangleGraph_adj_iff]
  exact (PD.FK.squareLattice_adj_iff _ _).mpr
    ((slitBoxGraph_adj_iff n u₀ v₀).mp hadj).1

/-- The edge embedding induced by the full slit-box embedding into its host. -/
noncomputable def slitBoxAuxiliaryHostEdgeEmbedding (n : ℕ) :
    (slitBoxGraph n).edgeSet ↪ (SideHostGraph n).edgeSet where
  toFun e := ⟨(slitBoxAuxiliaryHostEmbedding n).sym2Map e.val, by
    have heMap : (slitBoxAuxiliaryHostEmbedding n).sym2Map e.val ∈
        ((slitBoxGraph n).map (slitBoxAuxiliaryHostEmbedding n)).edgeSet := by
      rw [SimpleGraph.edgeSet_map]
      exact Set.mem_image_of_mem _ e.property
    exact SimpleGraph.edgeSet_mono (slitBoxAuxiliaryHostEmbedding_graph_le n) heMap⟩
  inj' := by
    intro e₁ e₂ h
    apply Subtype.ext
    apply Sym2.map.injective (slitBoxAuxiliaryHostEmbedding n).injective
    exact congrArg Subtype.val h

/-- Transport a slit-box bond state into the larger rectangular host. -/
noncomputable def slitBoxAuxiliaryMapConfiguration (n : ℕ)
    (A : PD.FK.Configuration (slitBoxGraph n)) :
    PD.FK.Configuration (SideHostGraph n) :=
  A.map (slitBoxAuxiliaryHostEdgeEmbedding n)

@[simp] theorem slitBoxAuxiliaryMapConfiguration_openEdges (n : ℕ)
    (A : PD.FK.Configuration (slitBoxGraph n)) :
    PD.FK.openEdges (SideHostGraph n) (slitBoxAuxiliaryMapConfiguration n A) =
      Sym2.map (slitBoxAuxiliaryHostEmbedding n) ''
        PD.FK.openEdges (slitBoxGraph n) A := by
  classical
  unfold PD.FK.openEdges slitBoxAuxiliaryMapConfiguration
  simp only [Finset.coe_map, Set.image_image]
  congr 1

theorem slitBoxAuxiliaryArcRing_removed (n : ℕ) :
    slitBoxAuxiliaryArcRing n ⊆
      PD.FK.subgraphRemovedEdges
        ((slitBoxGraph n).map (slitBoxAuxiliaryHostEmbedding n)) (SideHostGraph n) := by
  intro e he
  rw [PD.FK.mem_subgraphRemovedEdges]
  intro heMap
  rcases (mem_slitBoxAuxiliaryArcRing_iff n e).mp he with
    ⟨u, v, hu, hv, hval⟩
  have hEdge : s(u, v) ∈ ((slitBoxGraph n).map
      (slitBoxAuxiliaryHostEmbedding n)).edgeSet := by
    simpa [hval] using heMap
  have hAdj : ((slitBoxGraph n).map (slitBoxAuxiliaryHostEmbedding n)).Adj u v :=
    ((slitBoxGraph n).map (slitBoxAuxiliaryHostEmbedding n)).mem_edgeSet.mp hEdge
  rcases SimpleGraph.map_adj (slitBoxAuxiliaryHostEmbedding n) (slitBoxGraph n) u v |>.mp hAdj with
    ⟨a, b, hab, hfa, hfb⟩
  have ha : a ∈ slitBoxWiredArc n := by
    change u ∈ slitBoxAuxiliaryHostEmbedding n ''
      (slitBoxWiredArc n : Set (SlitBoxVertex n)) at hu
    rcases (Set.mem_image _ _ _).mp hu with ⟨c, hc, hfc⟩
    have : a = c := (slitBoxAuxiliaryHostEmbedding n).injective (hfa.trans hfc.symm)
    exact this ▸ hc
  have hb : b ∈ slitBoxWiredArc n := by
    change v ∈ slitBoxAuxiliaryHostEmbedding n ''
      (slitBoxWiredArc n : Set (SlitBoxVertex n)) at hv
    rcases (Set.mem_image _ _ _).mp hv with ⟨c, hc, hfc⟩
    have : b = c := (slitBoxAuxiliaryHostEmbedding n).injective (hfb.trans hfc.symm)
    exact this ▸ hc
  have haCoords := (mem_slitBoxWiredArc_iff n a).mp ha
  have hbCoords := (mem_slitBoxWiredArc_iff n b).mp hb
  exact ((slitBoxGraph_adj_iff n a b).mp hab).2 ⟨haCoords, hbCoords⟩

/-- The auxiliary open-ring theorem `PlanarMixed.auxiliaryArc_source_partition_eq` realizes
the exact slit-box wired arc
partition in the one-larger free host. -/
theorem slitBoxAuxiliaryArcRing_partition_eq (n : ℕ) :
    (PD.FK.isolatedExtensionPullbackBoundary (slitBoxAuxiliaryHostEmbedding n)
      (PD.FK.frozenBoundary (PD.FK.BoundaryCondition.free ∅)
        (slitBoxAuxiliaryArcRing n))).partition =
      (PD.FK.BoundaryCondition.wired
        (slitBoxWiredArc n : Set (SlitBoxVertex n))).partition := by
  let V := SlitBoxVertex n
  let G := slitBoxGraph n
  let f := slitBoxAuxiliaryHostEmbedding n
  let A : Set V := slitBoxWiredArc n
  let C : Set V := ∅
  have hAC : Disjoint A C := Set.disjoint_right.mpr (by simp [C])
  let Hstate : PD.FK.RemovedConfiguration (SideHostGraph n)
      (PD.FK.subgraphRemovedEdges (G.map f) (SideHostGraph n)) :=
    ⟨slitBoxAuxiliaryArcRing n, slitBoxAuxiliaryArcRing_removed n⟩
  have hring := PlanarMixed.auxiliaryArc_source_partition_eq f A C hAC Hstate
    (by
      intro e he
      left
      intro z hz
      rcases (mem_slitBoxAuxiliaryArcRing_iff n e).mp he with
        ⟨u, v, hu, hv, hval⟩
      rw [hval] at hz
      rcases Sym2.mem_iff.mp hz with h | h
      · subst z
        simpa [slitBoxAuxiliaryHostArc, A, f] using hu
      · subst z
        simpa [slitBoxAuxiliaryHostArc, A, f] using hv
    )
    (by
      intro u hu v hv
      exact slitArcRing_connected n
        ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩)
    (by
      intro u hu v hv
      exact hv.elim)
  have htwo : (BD12.twoBlockBoundary A C hAC).partition =
      (PD.FK.BoundaryCondition.wired A).partition := by
    apply Setoid.ext
    intro u v
    rw [BD12.twoBlockBoundary_partition_rel, PD.FK.BoundaryCondition.wired_rel]
    simp [C]
  rw [htwo] at hring
  simpa [V, G, f, A, C, Hstate] using hring.symm

end
end PottsContinuity.Thm4Side
