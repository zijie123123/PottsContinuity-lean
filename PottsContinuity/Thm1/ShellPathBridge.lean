module

public import PottsContinuity.Thm1.ShellGhostConnectivity
public import PottsContinuity.Thm1.ShellBondLimit
public import PottsContinuity.PD.FK.Graph
public import PottsContinuity.PD.Defs.RCInfiniteOpenGraph
public import PottsContinuity.PD.RCInfinite.ClusterEvents

@[expose] public section

namespace PottsContinuity.Thm1

open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD
open PottsContinuity.PD.RCInfinite

noncomputable section

def pottsESVertexCoordinate (V : Finset (ℤ × ℤ)) :
    PottsESVertex V → ℤ × ℤ
  | none => (0, 0)
  | some x => x.1

def pottsESLiftLatticeVertex (V : Finset (ℤ × ℤ))
    (x : ℤ × ℤ) : PottsESVertex V :=
  if hx : x ∈ pottsESSupport V then some ⟨x, hx⟩ else none

private theorem pottsESForgetVertex_injective (V : Finset (ℤ × ℤ)) :
    Function.Injective (fun x : PottsESVertex V => Option.map Subtype.val x) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => simp at h
  | some x =>
    cases y with
    | none => simp at h
    | some y =>
      have hv : x.1 = y.1 := Option.some.inj h
      exact congrArg some (Subtype.ext hv)

 theorem pottsESOpenAdj_to_latticeOpen
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    {x y : PottsESVertex V}
    (hxy : (openGraph (pottsESGraph V) A).Adj x y) :
    (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).Adj
      (pottsESVertexCoordinate V x) (pottsESVertexCoordinate V y) := by
  obtain ⟨u, v, hxu, hyv, huv⟩ :=
    pottsESGraph_adj_endpoints V (openGraph_le _ _ hxy)
  rw [hxu, hyv]
  have hOpenEdge : s(some u, some v) ∈ openEdges (pottsESGraph V) A :=
    (openGraph_adj (pottsESGraph V) A (some u) (some v)).mp (by simpa [hxu, hyv] using hxy)
  rcases hOpenEdge with ⟨g, hgA, hgv⟩
  let e := (pottsESEdgeEquiv V).symm g
  have hEquiv := congrArg Subtype.val
    (Equiv.apply_symm_apply (pottsESEdgeEquiv V) g)
  have hMap :
      Sym2.map (fun z : PottsESVertex V => Option.map Subtype.val z) g.1 =
        Sym2.map some e.1 := by
    rw [← hEquiv]
    exact pottsESEdgeEquiv_map_forget V e
  have hOriginal : e.1 = s(u.1, v.1) := by
    apply (Sym2.map.injective (Option.some_injective _))
    calc
      Sym2.map some e.1 =
          Sym2.map (fun z : PottsESVertex V => Option.map Subtype.val z) g.1 := hMap.symm
      _ = Sym2.map (fun z : PottsESVertex V => Option.map Subtype.val z)
          s(some u, some v) := congrArg
            (Sym2.map (fun z : PottsESVertex V => Option.map Subtype.val z)) hgv
      _ = Sym2.map some s(u.1, v.1) := by simp
  let edge : PottsContinuity.PD.squareLattice.edgeSet :=
    ⟨s(u.1, v.1), PottsContinuity.PD.squareLattice.mem_edgeSet.mpr huv⟩
  have hOpenExtension : pottsESShellBondExtension V A edge = true :=
    (pottsESShellBondExtension_edge_open_iff V A edge).2 ⟨g, hgA, hOriginal⟩
  simpa [pottsESVertexCoordinate] using
    (rcInfiniteOpenGraph_adj _ _ _).mpr ⟨edge.2, hOpenExtension⟩

private theorem pottsESOpenAdj_from_latticeOpen
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    {x y : ℤ × ℤ}
    (hxy : (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).Adj x y) :
    x ∈ pottsESSupport V ∧ y ∈ pottsESSupport V ∧
      (openGraph (pottsESGraph V) A).Adj
        (pottsESLiftLatticeVertex V x) (pottsESLiftLatticeVertex V y) := by
  obtain ⟨hedge, hstate⟩ := (rcInfiniteOpenGraph_adj _ x y).mp hxy
  let edge : PottsContinuity.PD.squareLattice.edgeSet := ⟨s(x, y), hedge⟩
  obtain ⟨g, hgA, hOriginal⟩ :=
    (pottsESShellBondExtension_edge_open_iff V A edge).mp hstate
  let e := (pottsESEdgeEquiv V).symm g
  have hOrig : e.1 = s(x, y) := by simpa [edge] using hOriginal
  have hxEdge : x ∈ e.1 := by rw [hOrig]; exact Sym2.mem_mk_left x y
  have hyEdge : y ∈ e.1 := by rw [hOrig]; exact Sym2.mem_mk_right x y
  have hxSupport := pottsEdges_endpoints_support V e.2 hxEdge
  have hySupport := pottsEdges_endpoints_support V e.2 hyEdge
  have hEquiv := congrArg Subtype.val
    (Equiv.apply_symm_apply (pottsESEdgeEquiv V) g)
  have hMap :
      Sym2.map (fun z : PottsESVertex V => Option.map Subtype.val z) g.1 =
        Sym2.map some e.1 := by
    rw [← hEquiv]
    exact pottsESEdgeEquiv_map_forget V e
  have hLiftMap :
      Sym2.map (fun z : PottsESVertex V => Option.map Subtype.val z)
          s(pottsESLiftLatticeVertex V x, pottsESLiftLatticeVertex V y) =
        Sym2.map some e.1 := by
    calc
      _ = Sym2.map some s(x, y) := by simp [pottsESLiftLatticeVertex, hxSupport, hySupport]
      _ = Sym2.map some e.1 := congrArg (Sym2.map some) hOrig.symm
  have hVal : g.1 =
      s(pottsESLiftLatticeVertex V x, pottsESLiftLatticeVertex V y) := by
    apply (Sym2.map.injective (pottsESForgetVertex_injective V))
    exact hMap.trans hLiftMap.symm
  have hOpen : s(pottsESLiftLatticeVertex V x, pottsESLiftLatticeVertex V y) ∈
      openEdges (pottsESGraph V) A := ⟨g, hgA, hVal⟩
  refine ⟨hxSupport, hySupport, ?_⟩
  exact (openGraph_adj (pottsESGraph V) A _ _).mpr hOpen

def pottsESOpenGraphToLatticeHom
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V)) :
    openGraph (pottsESGraph V) A →g
      PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A) where
  toFun := pottsESVertexCoordinate V
  map_rel' := fun h => pottsESOpenAdj_to_latticeOpen V A h

def pottsESLatticeToOpenGraphHom
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V)) :
    PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A) →g
      openGraph (pottsESGraph V) A where
  toFun := pottsESLiftLatticeVertex V
  map_rel' := by
    intro x y hxy
    exact (pottsESOpenAdj_from_latticeOpen V A hxy).2.2

theorem pottsESSupport_of_rcInfiniteSupport
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    {x : ℤ × ℤ}
    (hx : x ∈ (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).support) :
    x ∈ pottsESSupport V := by
  obtain ⟨y, hxy⟩ := (SimpleGraph.mem_support _).mp hx
  exact (pottsESOpenAdj_from_latticeOpen V A hxy).1

/-- Actual connectivity between physical shell vertices agrees with
reachability in the whole-lattice extension. -/
theorem pottsESActualConnected_iff_latticeReachable
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    (x y : ℤ × ℤ) (hx : x ∈ pottsESSupport V) (hy : y ∈ pottsESSupport V) :
    ActualConnected (pottsESGraph V) A (some ⟨x, hx⟩) (some ⟨y, hy⟩) ↔
      (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).Reachable x y := by
  constructor
  · intro h
    have hmapped := h.map (pottsESOpenGraphToLatticeHom V A)
    change (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).Reachable
      (pottsESVertexCoordinate V (some ⟨x, hx⟩))
      (pottsESVertexCoordinate V (some ⟨y, hy⟩)) at hmapped
    simpa [pottsESVertexCoordinate] using hmapped
  · intro h
    have hmapped := h.map (pottsESLatticeToOpenGraphHom V A)
    change ActualConnected (pottsESGraph V) A
      (pottsESLiftLatticeVertex V x) (pottsESLiftLatticeVertex V y) at hmapped
    simpa [pottsESLiftLatticeVertex, hx, hy] using hmapped

/-- In the whole-lattice extension, origin-to-exterior reachability is exactly
the finite shell graph's origin-to-ghost connection. -/
theorem pottsESOriginExteriorConnected_iff_latticeExit
    (V : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ V)
    (A : Configuration (pottsESGraph V)) :
    pottsESOriginExteriorConnected V h0 A ↔
      ∃ y : ℤ × ℤ, y ∉ V ∧
        (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).Reachable (0, 0) y := by
  constructor
  · intro h
    obtain ⟨y, hy, hpath⟩ :=
      (pottsESOriginExteriorConnected_iff_reachesExteriorSite V h0 A).mp h
    refine ⟨y.1, hy, ?_⟩
    have hmapped := hpath.map (pottsESOpenGraphToLatticeHom V A)
    change (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).Reachable
      (pottsESVertexCoordinate V (pottsESOriginVertex V h0))
      (pottsESVertexCoordinate V (some y)) at hmapped
    simpa [pottsESVertexCoordinate, pottsESOriginVertex] using hmapped
  · rintro ⟨y, hy, hpath⟩
    have hne : (0, 0) ≠ y := by
      intro heq
      subst y
      exact hy h0
    have hyRC : y ∈ (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).support :=
      SimpleGraph.mem_support_of_reachable hne.symm hpath.symm
    have hySupport := pottsESSupport_of_rcInfiniteSupport V A hyRC
    have h0Support : (0, 0) ∈ pottsESSupport V :=
      Finset.mem_union.mpr (Or.inl h0)
    have hOrigin : pottsESLiftLatticeVertex V (0, 0) = pottsESOriginVertex V h0 := by
      simp [pottsESLiftLatticeVertex, pottsESOriginVertex, h0Support]
    have hEnd : pottsESLiftLatticeVertex V y = some ⟨y, hySupport⟩ := by
      simp [pottsESLiftLatticeVertex, hySupport]
    have hmapped := hpath.map (pottsESLatticeToOpenGraphHom V A)
    change (openGraph (pottsESGraph V) A).Reachable
      (pottsESLiftLatticeVertex V (0, 0)) (pottsESLiftLatticeVertex V y) at hmapped
    rw [hOrigin, hEnd] at hmapped
    exact (pottsESOriginExteriorConnected_iff_reachesExteriorSite V h0 A).mpr
      ⟨⟨y, hySupport⟩, hy, hmapped⟩

end

end PottsContinuity.Thm1
