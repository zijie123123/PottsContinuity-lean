module

public import PottsContinuity.Thm4Side.AuxiliaryArcPartition
public import PottsContinuity.PD.FK.DomainMarkov
public import PottsContinuity.PD.FK.IsolatedBoundaryComponents
public import PottsContinuity.PD.FK.EdgeRestriction
public import PottsContinuity.PD.FK.SubgraphComparison
public import PottsContinuity.DualityExt.PositiveIsolatedBoundaryLaw

@[expose] public section

namespace PottsContinuity.Thm4Side

open PottsContinuity.PD.FK
open PottsContinuity.FKC.FiniteFK

noncomputable section

abbrev SideStateHostVertex (n : ℕ) :=
  PD.FK.RectangleVertex
    (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
    (2 * (n + 1)) (2 * (n + 1))

local instance sideStateSourceEdgeFintype (n : ℕ) :
    Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _

local instance sideStateSourceEdgeDecidableEq (n : ℕ) :
    DecidableEq (slitBoxGraph n).edgeSet := Classical.decEq _

local instance sideStateHostEdgeFintype (n : ℕ) :
    Fintype (PD.FK.rectangleGraph
      (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
      (2 * (n + 1)) (2 * (n + 1))).edgeSet := Fintype.ofFinite _

local instance sideStateHostEdgeDecidableEq (n : ℕ) :
    DecidableEq (PD.FK.rectangleGraph
      (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
      (2 * (n + 1)) (2 * (n + 1))).edgeSet := Classical.decEq _

private theorem mapWalk_preimage {V W : Type*} (f : V ↪ W) (G : SimpleGraph V)
    {x y : W} (p : (G.map f).Walk x y)
    (hx : ∃ a, f a = x) (hy : ∃ b, f b = y) :
    ∃ a b, f a = x ∧ f b = y ∧ Nonempty (G.Walk a b) := by
  induction p with
  | nil =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      have hab : a = b := f.injective (ha.trans hb.symm)
      subst b
      exact ⟨a, a, ha, ha, ⟨SimpleGraph.Walk.nil⟩⟩
  | @cons x y z hadj tail ih =>
      rcases (SimpleGraph.map_adj f G x y).mp hadj with
        ⟨a, b, hab, hfa, hfb⟩
      obtain ⟨b', c, hfb', hfc, ⟨htail⟩⟩ := ih ⟨b, hfb⟩ hy
      have hbb' : b = b' := f.injective (hfb.trans hfb'.symm)
      subst b'
      exact ⟨a, c, hfa, hfc, ⟨SimpleGraph.Walk.cons hab htail⟩⟩

private theorem mapWalk_endpoint_mem_range {V W : Type*} (f : V ↪ W)
    (G : SimpleGraph V) {x y : W} (p : (G.map f).Walk x y)
    (hx : x ∈ Set.range f) : y ∈ Set.range f := by
  induction p with
  | nil => exact hx
  | @cons x y z hadj tail ih =>
      rcases (SimpleGraph.map_adj f G x y).mp hadj with
        ⟨_, b, _, _, hfb⟩
      have hy : y ∈ Set.range f := ⟨b, hfb⟩
      exact ih hy

private theorem actualConnected_endpoint_mem_range {W V : Type*}
    (K : SimpleGraph W) (C : PD.FK.Configuration K) (f : V ↪ W)
    (hEdges : ∀ e : K.edgeSet, e ∈ C →
      ∀ z ∈ e.val, z ∈ Set.range f)
    {x y : W} (hconn : PD.FK.ActualConnected K C x y)
    (hx : x ∈ Set.range f) : y ∈ Set.range f := by
  rcases hconn with ⟨p⟩
  revert hx
  induction p with
  | nil =>
      intro hx
      exact hx
  | @cons x y z hadj tail ih =>
      intro hx
      rcases (PD.FK.openGraph_adj K C x y).mp hadj with ⟨e, he, hxy⟩
      have hy : y ∈ Set.range f :=
        hEdges e he y (by rw [hxy]; simp)
      exact ih hy

private theorem reachable_map_iff {V W : Type*} (f : V ↪ W)
    (G : SimpleGraph V) (a b : V) :
    (G.map f).Reachable (f a) (f b) ↔ G.Reachable a b := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨a', b', hfa, hfb, p'⟩ :=
      mapWalk_preimage f G p ⟨a, rfl⟩ ⟨b, rfl⟩
    have ha : a' = a := f.injective hfa
    have hb : b' = b := f.injective hfb
    subst a'
    subst b'
    exact Nonempty.elim p' fun w => w.reachable
  · intro h
    exact h.map ⟨f, fun hadj => (SimpleGraph.map_adj_apply).mpr hadj⟩

private theorem mappedOpenGraph_eq_map (n : ℕ)
    (A : PD.FK.Configuration (slitBoxGraph n)) :
    PD.FK.openGraph (PD.FK.rectangleGraph
        (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
        (2 * (n + 1)) (2 * (n + 1))) (slitBoxAuxiliaryMapConfiguration n A) =
      (PD.FK.openGraph (slitBoxGraph n) A).map
        (slitBoxAuxiliaryHostEmbedding n) := by
  apply SimpleGraph.edgeSet_injective
  calc
    (PD.FK.openGraph (PD.FK.rectangleGraph
        (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
        (2 * (n + 1)) (2 * (n + 1))) (slitBoxAuxiliaryMapConfiguration n A)).edgeSet =
        PD.FK.openEdges (PD.FK.rectangleGraph
          (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
          (2 * (n + 1)) (2 * (n + 1)))
          (slitBoxAuxiliaryMapConfiguration n A) :=
      PD.FK.openGraph_edgeSet _ _
    _ = Sym2.map (slitBoxAuxiliaryHostEmbedding n) ''
        PD.FK.openEdges (slitBoxGraph n) A :=
      slitBoxAuxiliaryMapConfiguration_openEdges n A
    _ = Sym2.map (slitBoxAuxiliaryHostEmbedding n) ''
        (PD.FK.openGraph (slitBoxGraph n) A).edgeSet := by
      rw [PD.FK.openGraph_edgeSet]
    _ = ((PD.FK.openGraph (slitBoxGraph n) A).map
        (slitBoxAuxiliaryHostEmbedding n)).edgeSet := by
      exact (SimpleGraph.edgeSet_map _ _).symm

theorem slitBoxAuxiliaryMap_actualConnected_iff (n : ℕ)
    (A : PD.FK.Configuration (slitBoxGraph n))
    (u v : SlitBoxVertex n) :
    PD.FK.ActualConnected
        (PD.FK.rectangleGraph
          (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
          (2 * (n + 1)) (2 * (n + 1)))
        (slitBoxAuxiliaryMapConfiguration n A)
        (slitBoxAuxiliaryHostEmbedding n u)
        (slitBoxAuxiliaryHostEmbedding n v) ↔
      PD.FK.ActualConnected (slitBoxGraph n) A u v := by
  rw [PD.FK.ActualConnected, PD.FK.ActualConnected, mappedOpenGraph_eq_map]
  exact reachable_map_iff (slitBoxAuxiliaryHostEmbedding n)
    (PD.FK.openGraph (slitBoxGraph n) A) u v

private theorem slitBoxAuxiliaryArcRing_openEdges_endpoints_mem_range (n : ℕ) :
    ∀ e : (PD.FK.rectangleGraph
        (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
        (2 * (n + 1)) (2 * (n + 1))).edgeSet,
      e ∈ slitBoxAuxiliaryArcRing n →
      ∀ z ∈ e.val, z ∈ Set.range (slitBoxAuxiliaryHostEmbedding n) := by
  intro e he z hz
  rcases (mem_slitBoxAuxiliaryArcRing_iff n e).mp he with
    ⟨u, v, hu, hv, hpair⟩
  have hz' : z ∈ s(u, v) := by simpa [hpair] using hz
  rcases (Sym2.mem_iff').mp hz' with hzu | hzv
  · subst z
    change u ∈ slitBoxAuxiliaryHostEmbedding n ''
      (slitBoxWiredArc n : Set (SlitBoxVertex n)) at hu
    rcases (Set.mem_image _ _ _).mp hu with ⟨a, _, hfa⟩
    exact ⟨a, hfa⟩
  · subst z
    change v ∈ slitBoxAuxiliaryHostEmbedding n ''
      (slitBoxWiredArc n : Set (SlitBoxVertex n)) at hv
    rcases (Set.mem_image _ _ _).mp hv with ⟨a, _, hfa⟩
    exact ⟨a, hfa⟩

private theorem componentSetoid_comap_of_generator_iff
    {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    (f : V ↪ W) (ξ : PD.FK.BoundaryCondition V)
    (ζ : PD.FK.BoundaryCondition W) (A : PD.FK.Configuration G)
    (B : PD.FK.Configuration K)
    (sourceRel : V → V → Prop) (hostRel : W → W → Prop)
    (hsource : ∀ u v, sourceRel u v ↔
      (PD.FK.ActualConnected G A u v ∨ ξ.partition.r u v))
    (hhost : ∀ u v, hostRel u v ↔
      (PD.FK.ActualConnected K B u v ∨ ζ.partition.r u v))
    (hstep : ∀ {x y}, hostRel x y → ∀ {a}, f a = x →
      ∃ b, f b = y ∧ sourceRel a b)
    (hsymm : ∀ {x y}, hostRel x y → hostRel y x)
    (hmap : ∀ u v, sourceRel u v → hostRel (f u) (f v)) :
    Setoid.comap f (PD.FK.componentSetoid K ζ B) =
      PD.FK.componentSetoid G ξ A := by
  apply Setoid.ext
  intro u v
  rw [Setoid.comap_rel, PD.FK.componentSetoid_rel_iff,
    PD.FK.componentSetoid_rel_iff]
  constructor
  · intro h
    let : Std.Symm hostRel := ⟨fun x y hxy => hsymm hxy⟩
    have hforward : ∀ {x y}, Relation.ReflTransGen hostRel x y →
        ∀ {a}, f a = x → ∃ b, f b = y ∧ Relation.ReflTransGen sourceRel a b := by
      intro x y hxy
      induction hxy with
      | tail hxy hyz ih =>
          intro a hfa
          obtain ⟨b, hfb, hab⟩ := ih hfa
          obtain ⟨c, hfc, hbc⟩ := hstep hyz hfb
          exact ⟨c, hfc, Relation.ReflTransGen.tail hab hbc⟩
      | refl =>
          intro a hfa
          exact ⟨a, hfa, Relation.ReflTransGen.refl⟩
    have hrt : Relation.ReflTransGen hostRel (f u) (f v) := by
      have h' : Relation.EqvGen hostRel (f u) (f v) :=
        (Relation.EqvGen.mono
          (r := fun x y => PD.FK.ActualConnected K B x y ∨ ζ.partition.r x y)
          (p := hostRel)
          (fun x y hxy => (hhost x y).mpr hxy)) (f u) (f v) h
      have heq : Relation.EqvGen hostRel (f u) (f v) =
          Relation.ReflTransGen hostRel (f u) (f v) :=
        congrArg (fun r : W → W → Prop =>
          r (f u) (f v))
          (Relation.EqvGen.eqvGen_eq_reflTransGen (r := hostRel))
      exact heq.mp h'
    obtain ⟨b, hfb, hab⟩ := hforward hrt rfl
    have hb : b = v := f.injective (hfb.trans rfl.symm)
    subst b
    have hab' : Relation.ReflTransGen
        (fun x y => PD.FK.ActualConnected G A x y ∨ ξ.partition.r x y) u v :=
      Relation.ReflTransGen.mono (fun x y hxy => (hsource x y).mp hxy) u v hab
    exact Relation.EqvGen.reflTransGen_le_eqvGen
      (fun x y => PD.FK.ActualConnected G A x y ∨ ξ.partition.r x y) u v hab'
  · intro h
    induction h with
    | rel x y hxy =>
        exact Relation.EqvGen.rel _ _ ((hhost (f x) (f y)).mp
          (hmap x y ((hsource x y).mpr hxy)))
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The free host with both the reveal state and auxiliary open arc ring
induces exactly the source frozen boundary, after restriction to slit-box
vertices. -/
theorem slitBoxAuxiliaryFrozenBoundary_partition_eq (n : ℕ)
    (A : PD.FK.Configuration (slitBoxGraph n)) :
    (PD.FK.isolatedExtensionPullbackBoundary (slitBoxAuxiliaryHostEmbedding n)
      (PD.FK.frozenBoundary (PD.FK.BoundaryCondition.free ∅)
        (slitBoxAuxiliaryArcRing n ∪ slitBoxAuxiliaryMapConfiguration n A))).partition =
    (PD.FK.frozenBoundary
      (PD.FK.BoundaryCondition.wired (slitBoxWiredArc n : Set (SlitBoxVertex n)))
      A).partition := by
  let f := slitBoxAuxiliaryHostEmbedding n
  let G := slitBoxGraph n
  let K := PD.FK.rectangleGraph
    (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
    (2 * (n + 1)) (2 * (n + 1))
  let ξ := PD.FK.BoundaryCondition.wired (slitBoxWiredArc n : Set (SlitBoxVertex n))
  let ζ := PD.FK.frozenBoundary (PD.FK.BoundaryCondition.free ∅)
    (slitBoxAuxiliaryArcRing n)
  let B := slitBoxAuxiliaryMapConfiguration n A
  let sourceRel : SlitBoxVertex n → SlitBoxVertex n → Prop := fun u v =>
    PD.FK.ActualConnected G A u v ∨ ξ.partition.r u v
  let hostRel : SideStateHostVertex n → SideStateHostVertex n → Prop := fun u v =>
    PD.FK.ActualConnected K B u v ∨ ζ.partition.r u v
  have hbase : (PD.FK.isolatedExtensionPullbackBoundary f ζ).partition = ξ.partition := by
    exact slitBoxAuxiliaryArcRing_partition_eq n
  have hbaseRel : ∀ u v, ξ.partition.r u v ↔ ζ.partition.r (f u) (f v) := by
    intro u v
    have hset : Setoid.comap f ζ.partition = ξ.partition := hbase
    have hrel := congrArg (fun s : Setoid (SlitBoxVertex n) => s.r u v) hset
    have hiff : ζ.partition.r (f u) (f v) ↔ ξ.partition.r u v := by
      simpa only [Setoid.comap_rel] using hrel.to_iff
    exact hiff.symm
  have hstep : ∀ {x y}, hostRel x y → ∀ {a}, f a = x →
      ∃ b, f b = y ∧ sourceRel a b := by
    intro x y hxy a hfa
    rcases hxy with hc | hb
    · have hc' : PD.FK.ActualConnected K B (f a) y := by
        simpa [hfa] using hc
      rw [PD.FK.ActualConnected, mappedOpenGraph_eq_map n A] at hc'
      rcases hc' with ⟨p⟩
      have hy : y ∈ Set.range f := mapWalk_endpoint_mem_range f
        (PD.FK.openGraph G A) p ⟨a, rfl⟩
      rcases hy with ⟨b, hfb⟩
      refine ⟨b, hfb, Or.inl ?_⟩
      have hcMap : PD.FK.ActualConnected K B (f a) (f b) := by
        change (PD.FK.openGraph K B).Reachable (f a) (f b)
        rw [mappedOpenGraph_eq_map n A]
        exact ⟨p.copy rfl hfb.symm⟩
      exact (slitBoxAuxiliaryMap_actualConnected_iff n A a b).mp hcMap
    · have hb' : ζ.partition.r (f a) y := by simpa [hfa] using hb
      have hconn : PD.FK.ActualConnected K
        (slitBoxAuxiliaryArcRing n) (f a) y := by
          change (PD.FK.componentSetoid K
            (PD.FK.BoundaryCondition.free ∅) (slitBoxAuxiliaryArcRing n)).r
            (f a) y at hb'
          rw [PD.FK.componentSetoid_free] at hb'
          change (PD.FK.openGraph K (slitBoxAuxiliaryArcRing n)).Reachable
            (f a) y
          exact hb'
      have hy := actualConnected_endpoint_mem_range K
        (slitBoxAuxiliaryArcRing n) f
        (slitBoxAuxiliaryArcRing_openEdges_endpoints_mem_range n) hconn ⟨a, rfl⟩
      rcases hy with ⟨b, hfb⟩
      have hb'' : ζ.partition.r (f a) (f b) := by simpa [hfb] using hb'
      exact ⟨b, hfb, Or.inr ((hbaseRel a b).mpr hb'')⟩
  have hsource : ∀ u v, sourceRel u v ↔
      (PD.FK.ActualConnected G A u v ∨ ξ.partition.r u v) := by
    intro u v
    rfl
  have hhost : ∀ u v, hostRel u v ↔
      (PD.FK.ActualConnected K B u v ∨ ζ.partition.r u v) := by
    intro u v
    rfl
  have hsymm : ∀ {x y}, hostRel x y → hostRel y x := by
    intro x y hxy
    rcases hxy with hc | hb
    · exact Or.inl (by simpa [PD.FK.ActualConnected] using hc.symm)
    · exact Or.inr (Setoid.symm' ζ.partition hb)
  have hmap : ∀ u v, sourceRel u v → hostRel (f u) (f v) := by
    intro u v huv
    rcases huv with hc | hb
    · exact Or.inl ((slitBoxAuxiliaryMap_actualConnected_iff n A u v).mpr hc)
    · exact Or.inr ((hbaseRel u v).mp hb)
  have hcomap : Setoid.comap f (PD.FK.componentSetoid K ζ B) =
      PD.FK.componentSetoid G ξ A :=
    componentSetoid_comap_of_generator_iff f ξ ζ A B sourceRel hostRel
      hsource hhost hstep hsymm hmap
  have hunion : PD.FK.componentSetoid K
      (PD.FK.BoundaryCondition.free ∅)
      (slitBoxAuxiliaryArcRing n ∪ B) =
      PD.FK.componentSetoid K ζ B := by
    rw [show slitBoxAuxiliaryArcRing n ∪ B = B ∪ slitBoxAuxiliaryArcRing n by
      exact Finset.union_comm _ _]
    exact PD.FK.componentSetoid_union_frozen
      (PD.FK.BoundaryCondition.free ∅) B (slitBoxAuxiliaryArcRing n)
  apply Setoid.ext
  intro u v
  change (Setoid.comap f
      (PD.FK.componentSetoid K (PD.FK.BoundaryCondition.free ∅)
        (slitBoxAuxiliaryArcRing n ∪ B))).r u v ↔
    (PD.FK.componentSetoid G ξ A).r u v
  rw [hunion, hcomap]

/-- Pulling the full-source identity back once more gives the exact
partition equality on any retained active carrier. -/
theorem slitBoxAuxiliaryPullbackFrozenBoundary_partition_eq
    {V : Type*} (n : ℕ) (i : V ↪ SlitBoxVertex n)
    (A : PD.FK.Configuration (slitBoxGraph n)) :
    (PD.FK.isolatedExtensionPullbackBoundary (i.trans
      (slitBoxAuxiliaryHostEmbedding n))
      (PD.FK.frozenBoundary (PD.FK.BoundaryCondition.free ∅)
        (slitBoxAuxiliaryArcRing n ∪ slitBoxAuxiliaryMapConfiguration n A))).partition =
    (PD.FK.isolatedExtensionPullbackBoundary i
      (PD.FK.frozenBoundary
        (PD.FK.BoundaryCondition.wired
          (slitBoxWiredArc n : Set (SlitBoxVertex n))) A)).partition := by
  apply Setoid.ext
  intro u v
  have h := congrArg (fun s : Setoid (SlitBoxVertex n) => s.r (i u) (i v))
    (slitBoxAuxiliaryFrozenBoundary_partition_eq n A)
  change (PD.FK.frozenBoundary (PD.FK.BoundaryCondition.free ∅)
      (slitBoxAuxiliaryArcRing n ∪ slitBoxAuxiliaryMapConfiguration n A)).partition.r
        (slitBoxAuxiliaryHostEmbedding n (i u))
        (slitBoxAuxiliaryHostEmbedding n (i v)) ↔
    (PD.FK.frozenBoundary
      (PD.FK.BoundaryCondition.wired
        (slitBoxWiredArc n : Set (SlitBoxVertex n))) A).partition.r (i u) (i v)
  exact h.to_iff

/-- The mapped revealed open bonds and the auxiliary arc ring are both
outside the residual edge restriction. -/
theorem slitBoxAuxiliaryRevealState_removed (n : ℕ)
    (R A : PD.FK.Configuration (slitBoxGraph n)) (hAR : A ⊆ R) :
    slitBoxAuxiliaryArcRing n ∪ slitBoxAuxiliaryMapConfiguration n A ⊆
      PD.FK.subgraphRemovedEdges
        ((PD.FK.edgeRestriction (slitBoxGraph n) R).map
          (slitBoxAuxiliaryHostEmbedding n))
        (PD.FK.rectangleGraph
          (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
          (2 * (n + 1)) (2 * (n + 1))) := by
  intro e he
  rw [Finset.mem_union] at he
  apply (PD.FK.mem_subgraphRemovedEdges e).2
  intro heResidual
  rcases he with heRing | heReveal
  · have heFull := (PD.FK.mem_subgraphRemovedEdges e).mp
      (slitBoxAuxiliaryArcRing_removed n heRing)
    have hmapLe :
        ((PD.FK.edgeRestriction (slitBoxGraph n) R).map
            (slitBoxAuxiliaryHostEmbedding n)) ≤
          (slitBoxGraph n).map (slitBoxAuxiliaryHostEmbedding n) := by
      intro u v huv
      rw [SimpleGraph.map_adj] at huv ⊢
      rcases huv with ⟨u₀, v₀, hadj, rfl, rfl⟩
      exact ⟨u₀, v₀, PD.FK.edgeRestriction_le (slitBoxGraph n) R hadj,
        rfl, rfl⟩
    exact heFull (SimpleGraph.edgeSet_mono hmapLe heResidual)
  · obtain ⟨e₀, he₀, heEq⟩ := Finset.mem_map.mp heReveal
    have heOpen : e₀.val ∈ PD.FK.openEdges (slitBoxGraph n) R :=
      (PD.FK.coe_mem_openEdges_iff (slitBoxGraph n) R e₀).mpr (hAR he₀)
    have heMap : e.val ∈ (slitBoxAuxiliaryHostEmbedding n).sym2Map ''
        (PD.FK.edgeRestriction (slitBoxGraph n) R).edgeSet := by
      rw [SimpleGraph.edgeSet_map] at heResidual
      exact heResidual
    obtain ⟨e₁, he₁, he₁Eq⟩ := heMap
    have heCoeff : (slitBoxAuxiliaryHostEmbedding n).sym2Map e₀.val =
        (slitBoxAuxiliaryHostEmbedding n).sym2Map e₁ := by
      calc
        _ = (slitBoxAuxiliaryHostEdgeEmbedding n e₀).val := rfl
        _ = e.val := congrArg Subtype.val heEq
        _ = _ := he₁Eq.symm
    have heSource : e₀.val = e₁ :=
      Sym2.map.injective (slitBoxAuxiliaryHostEmbedding n).injective heCoeff
    have he₁notOpen : e₁ ∉ PD.FK.openEdges (slitBoxGraph n) R := by
      have hmem : e₁ ∈ (PD.FK.edgeRestriction (slitBoxGraph n) R).edgeSet := he₁
      rw [PD.FK.edgeRestriction_edgeSet] at hmem
      simp only [Set.mem_sdiff] at hmem
      exact hmem.2
    exact he₁notOpen (heSource ▸ heOpen)

/-- The same removed-state inclusion on the endpoint-only residual carrier
`DualityExt.positiveActiveGraph`. -/
theorem slitBoxAuxiliaryActiveRevealState_removed (n : ℕ)
    (R A : PD.FK.Configuration (slitBoxGraph n)) (hAR : A ⊆ R) :
    slitBoxAuxiliaryArcRing n ∪ slitBoxAuxiliaryMapConfiguration n A ⊆
      PD.FK.subgraphRemovedEdges
        ((PottsContinuity.DualityExt.positiveActiveGraph
            (PD.FK.edgeRestriction (slitBoxGraph n) R)).map
          ((PottsContinuity.DualityExt.positiveActiveInclusion
              (PD.FK.edgeRestriction (slitBoxGraph n) R)).trans
            (slitBoxAuxiliaryHostEmbedding n)))
        (PD.FK.rectangleGraph
          (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
          (2 * (n + 1)) (2 * (n + 1))) := by
  have hremoved := slitBoxAuxiliaryRevealState_removed n R A hAR
  have hgraph :
      (PottsContinuity.DualityExt.positiveActiveGraph
          (PD.FK.edgeRestriction (slitBoxGraph n) R)).map
        ((PottsContinuity.DualityExt.positiveActiveInclusion
            (PD.FK.edgeRestriction (slitBoxGraph n) R)).trans
          (slitBoxAuxiliaryHostEmbedding n)) =
        (PD.FK.edgeRestriction (slitBoxGraph n) R).map
          (slitBoxAuxiliaryHostEmbedding n) := by
    change (PottsContinuity.DualityExt.positiveActiveGraph
        (PD.FK.edgeRestriction (slitBoxGraph n) R)).map
          (slitBoxAuxiliaryHostEmbedding n ∘
            PottsContinuity.DualityExt.positiveActiveInclusion
              (PD.FK.edgeRestriction (slitBoxGraph n) R)) = _
    rw [← SimpleGraph.map_map]
    rw [PottsContinuity.DualityExt.positiveActiveGraph_map_subtype]
  rw [hgraph]
  exact hremoved

/-- The reveal-and-ring frozen partition has the exact pullback required by
the positive active residual carrier. -/
theorem slitBoxAuxiliaryActiveFrozenBoundary_partition_eq (n : ℕ)
    (R A : PD.FK.Configuration (slitBoxGraph n)) :
    (PD.FK.isolatedExtensionPullbackBoundary
      ((PottsContinuity.DualityExt.positiveActiveInclusion
          (PD.FK.edgeRestriction (slitBoxGraph n) R)).trans
        (slitBoxAuxiliaryHostEmbedding n))
      (PD.FK.frozenBoundary (PD.FK.BoundaryCondition.free ∅)
        (slitBoxAuxiliaryArcRing n ∪ slitBoxAuxiliaryMapConfiguration n A))).partition =
    (PD.FK.isolatedExtensionPullbackBoundary
      (PottsContinuity.DualityExt.positiveActiveInclusion
        (PD.FK.edgeRestriction (slitBoxGraph n) R))
      (PD.FK.frozenBoundary
        (PD.FK.BoundaryCondition.wired
          (slitBoxWiredArc n : Set (SlitBoxVertex n))) A)).partition :=
  slitBoxAuxiliaryPullbackFrozenBoundary_partition_eq n
    (PottsContinuity.DualityExt.positiveActiveInclusion
      (PD.FK.edgeRestriction (slitBoxGraph n) R)) A

end
end PottsContinuity.Thm4Side
