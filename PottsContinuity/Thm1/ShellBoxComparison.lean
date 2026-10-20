module

public import PottsContinuity.Thm1.FiniteES
public import PottsContinuity.PD.FK.Lattice
public import PottsContinuity.PD.FK.EmbeddedClosedInteriorOuterComparison
public import PottsContinuity.PD.FK.WiredBoxLaw
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

 theorem shellSupport_of_mem (V : Finset (ℤ × ℤ)) {x : ℤ × ℤ}
    (hx : x ∈ V) : x ∈ pottsESSupport V :=
  Finset.mem_union.mpr (Or.inl hx)

def forgetESVertex (V : Finset (ℤ × ℤ)) :
    PottsESVertex V → Option (ℤ × ℤ) := Option.map Subtype.val

private theorem forgetESVertex_injective (V : Finset (ℤ × ℤ)) :
    Function.Injective (forgetESVertex V) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => simp [forgetESVertex] at h
  | some x =>
    cases y with
    | none => simp [forgetESVertex] at h
    | some y =>
      have h' : x.val = y.val := by simpa [forgetESVertex] using h
      exact congrArg some (Subtype.ext h')

theorem pottsEdges_contains_adjacent_pair {V : Finset (ℤ × ℤ)}
    {x y : ℤ × ℤ} (hx : x ∈ V)
    (hxy : PottsContinuity.PD.FK.squareLattice.Adj x y) :
    s(x, y) ∈ pottsEdges V := by
  have hdir : ∃ d ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)),
      y = x + d := by
    have hadj := (PottsContinuity.PD.FK.squareLattice_adj_iff x y).mp hxy
    rcases hadj with ⟨hcoord, hother⟩ | ⟨hcoord, hother⟩
    · rcases hcoord with hcoord | hcoord
      · refine ⟨(1, 0), by simp, ?_⟩
        ext <;> dsimp <;> omega
      · refine ⟨(-1, 0), by simp, ?_⟩
        ext <;> dsimp <;> omega
    · rcases hother with hcoord | hcoord
      · refine ⟨(0, 1), by simp, ?_⟩
        ext <;> dsimp <;> omega
      · refine ⟨(0, -1), by simp, ?_⟩
        ext <;> dsimp <;> omega
  obtain ⟨d, hd, hdy⟩ := hdir
  unfold pottsEdges
  rw [Finset.mem_biUnion]
  refine ⟨x, hx, ?_⟩
  rw [Finset.mem_image]
  refine ⟨d, hd, ?_⟩
  rw [hdy]

theorem pottsEdges_endpoints_adjacent {V : Finset (ℤ × ℤ)}
    {e : Sym2 (ℤ × ℤ)} (he : e ∈ pottsEdges V)
    {x y : ℤ × ℤ} (hx : x ∈ e) (hy : y ∈ e) (hne : x ≠ y) :
    PottsContinuity.PD.FK.squareLattice.Adj x y := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pottsEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_insert, Finset.mem_singleton] at he
    obtain ⟨z, hz, d, hd, hEq⟩ := he
    have hx' : x = z ∨ x = z + d := by
      rw [← hEq] at hx
      simpa only [Sym2.mem_iff] using hx
    have hy' : y = z ∨ y = z + d := by
      rw [← hEq] at hy
      simpa only [Sym2.mem_iff] using hy
    have hd' : d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hd
    have hzy : PottsContinuity.PD.FK.squareLattice.Adj z (z + d) := by
      rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
      rcases hd' with hd' | hd' | hd' | hd' <;> subst d <;>
        simp [Prod.fst_add, Prod.snd_add]
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact False.elim (hne rfl)
    · exact hzy
    · exact hzy.symm
    · exact False.elim (hne rfl)

theorem pottsESGraph_adj_endpoints (V : Finset (ℤ × ℤ))
    {x y : PottsESVertex V} (hxy : (pottsESGraph V).Adj x y) :
    ∃ u v : PottsESSite V, x = some u ∧ y = some v ∧
      PottsContinuity.PD.FK.squareLattice.Adj u.val v.val := by
  let edge : (pottsESGraph V).edgeSet := ⟨s(x, y), (pottsESGraph V).mem_edgeSet.mpr hxy⟩
  let e : pottsEdges V := (pottsESEdgeEquiv V).symm edge
  have hedge : ((pottsESEdgeEquiv V e).1) = s(x, y) := by
    have heq := congrArg Subtype.val (Equiv.apply_symm_apply (pottsESEdgeEquiv V) edge)
    exact heq
  have hedgeMap :
      Sym2.map (forgetESVertex V) (s(x, y)) = Sym2.map some e.1 := by
    calc
      Sym2.map (forgetESVertex V) (s(x, y)) =
          Sym2.map (forgetESVertex V) ((pottsESEdgeEquiv V e).1) := by rw [hedge]
      _ = Sym2.map some e.1 := pottsESEdgeEquiv_map_forget V e
  have hxMap : forgetESVertex V x ∈ Sym2.map some e.1 := by
    rw [← hedgeMap]
    simp
  have hyMap : forgetESVertex V y ∈ Sym2.map some e.1 := by
    rw [← hedgeMap]
    simp
  obtain ⟨u, hxu, hux⟩ : ∃ u : PottsESSite V,
      x = some u ∧ u.val ∈ e.1 := by
    obtain ⟨a, ha, hfa⟩ := Sym2.mem_map.mp hxMap
    cases x with
    | none => simp [forgetESVertex] at hfa
    | some u =>
      have hau : a = u.val := Option.some.inj (by simpa [forgetESVertex] using hfa)
      subst a
      exact ⟨u, rfl, ha⟩
  obtain ⟨v, hyv, hvy⟩ : ∃ v : PottsESSite V,
      y = some v ∧ v.val ∈ e.1 := by
    obtain ⟨b, hb, hfb⟩ := Sym2.mem_map.mp hyMap
    cases y with
    | none => simp [forgetESVertex] at hfb
    | some v =>
      have hbv : b = v.val := Option.some.inj (by simpa [forgetESVertex] using hfb)
      subst b
      exact ⟨v, rfl, hb⟩
  have huv : u.val ≠ v.val := by
    intro huv
    have hne := (pottsESGraph V).ne_of_adj hxy
    apply hne
    rw [hxu, hyv]
    exact congrArg some (Subtype.ext huv)
  refine ⟨u, v, hxu, hyv, ?_⟩
  apply pottsEdges_endpoints_adjacent e.2 hux hvy huv

private theorem pottsESGraph_adj_of_sites (V : Finset (ℤ × ℤ))
    (x y : PottsESSite V) (hxV : x.val ∈ V)
    (hxy : PottsContinuity.PD.FK.squareLattice.Adj x.val y.val) :
    (pottsESGraph V).Adj (some x) (some y) := by
  have hEdge := pottsEdges_contains_adjacent_pair hxV hxy
  let e : pottsEdges V := ⟨s(x.val, y.val), hEdge⟩
  have hval : (pottsESEdgeEquiv V e).1 = s(some x, some y) := by
    apply (Sym2.map.injective (forgetESVertex_injective V))
    calc
      Sym2.map (forgetESVertex V) (pottsESEdgeEquiv V e).1 =
          Sym2.map some e.1 := pottsESEdgeEquiv_map_forget V e
      _ = Sym2.map (forgetESVertex V) s(some x, some y) := by
          simp [e, forgetESVertex]
  have hmem : s(some x, some y) ∈ (pottsESGraph V).edgeSet := by
    have he := (pottsESEdgeEquiv V e).property
    rw [hval] at he
    exact he
  exact (pottsESGraph V).mem_edgeSet.mp hmem

/-- Embed a box contained in `V` into the physical-site part of its shell graph. -/
def pottsESBoxEmbedding (V : Finset (ℤ × ℤ)) (r : ℕ)
    (hV : latticeBox (0, 0) r ⊆ V) :
    BoxVertex (0, 0) r ↪ PottsESVertex V where
  toFun := fun x => some ⟨x.val, shellSupport_of_mem V (hV x.property)⟩
  inj' := by
    intro x y h
    have hs := Option.some.inj h
    have hv : x.val = y.val := congrArg (fun z : PottsESSite V => z.1) hs
    exact Subtype.ext hv

theorem pottsESBoxEmbedding_map_le (V : Finset (ℤ × ℤ)) (r : ℕ)
    (hV : latticeBox (0, 0) r ⊆ V) :
    (boxGraph (0, 0) r).map (pottsESBoxEmbedding V r hV) ≤ pottsESGraph V := by
  intro u v huv
  obtain ⟨x, y, hxy, rfl, rfl⟩ :=
    (SimpleGraph.map_adj (pottsESBoxEmbedding V r hV) (boxGraph (0, 0) r) u v).mp huv
  have hadj : PottsContinuity.PD.FK.squareLattice.Adj x.val y.val := hxy
  have hxSupport := shellSupport_of_mem V (hV x.property)
  have hySupport := shellSupport_of_mem V (hV y.property)
  let sx : PottsESSite V := ⟨x.val, hxSupport⟩
  let sy : PottsESSite V := ⟨y.val, hySupport⟩
  exact pottsESGraph_adj_of_sites V sx sy (hV x.property) hadj

private theorem boxInterior_neighbor_closed_in_shell (V : Finset (ℤ × ℤ))
    (r : ℕ) (hV : latticeBox (0, 0) r ⊆ V)
    {x : BoxVertex (0, 0) r} (hx : x ∉ boxVertexBoundary (0, 0) r)
    {y : PottsESVertex V} (hxy : (pottsESGraph V).Adj (pottsESBoxEmbedding V r hV x) y) :
    ∃ z : BoxVertex (0, 0) r,
      pottsESBoxEmbedding V r hV z = y ∧ (boxGraph (0, 0) r).Adj x z := by
  obtain ⟨u, v, hxu, hyv, huv⟩ := pottsESGraph_adj_endpoints V hxy
  have hval : u.val = x.val := by
    have hs : (⟨x.val, shellSupport_of_mem V (hV x.property)⟩ : PottsESSite V) = u :=
      Option.some.inj (by
        change some (⟨x.val, shellSupport_of_mem V (hV x.property)⟩ : PottsESSite V) =
          some u at hxu
        exact hxu)
    exact (congrArg Subtype.val hs).symm
  have hvBox : v.val ∈ latticeBox (0, 0) r := by
    by_contra hvBox
    apply hx
    change x.val ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) r)
    refine ⟨x.property, v.val, ?_, hvBox⟩
    simpa [hval] using huv
  refine ⟨⟨v.val, hvBox⟩, ?_, ?_⟩
  · have hz : pottsESBoxEmbedding V r hV ⟨v.val, hvBox⟩ = some v := by
      change some ⟨v.val, shellSupport_of_mem V (hV hvBox)⟩ = some v
      congr 1
    exact hz.trans hyv.symm
  · apply (boxGraph_adj_iff (0, 0) r x ⟨v.val, hvBox⟩).mpr
    simpa [hval] using huv

private theorem boxInterior_avoids_shellBoundary (V : Finset (ℤ × ℤ))
    (r : ℕ) (hV : latticeBox (0, 0) r ⊆ V)
    {x : BoxVertex (0, 0) r} (_hx : x ∉ boxVertexBoundary (0, 0) r) :
    pottsESBoxEmbedding V r hV x ∉ (pottsESBoundary V) := by
  intro hboundary
  change pottsESBoxEmbedding V r hV x = none ∨
    ∃ y, pottsESBoxEmbedding V r hV x = some y ∧ y.val ∉ V at hboundary
  rcases hboundary with hnone | ⟨y, hy, hyV⟩
  · cases hnone
  · have hcoord : x.val = y.val := by
      have hs : (⟨x.val, shellSupport_of_mem V (hV x.property)⟩ : PottsESSite V) = y :=
        Option.some.inj (by
          change some (⟨x.val, shellSupport_of_mem V (hV x.property)⟩ : PottsESSite V) =
            some y at hy
          exact hy)
      exact congrArg Subtype.val hs
    exact hyV (hV (by simpa [hcoord] using x.property))

theorem pottsESWiredShell_allOpen_le_wiredBox
    (V : Finset (ℤ × ℤ)) (θ : Parameters) (r : ℕ)
    (hV : latticeBox (0, 0) r ⊆ V)
    (F : Finset PottsContinuity.PD.FK.squareLattice.edgeSet) :
    (measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
      {A | embeddedConfigurationRestriction (boxGraph (0, 0) r) (pottsESGraph V)
        (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) A ∈
          wiredBoxCylinderEvent (0, 0) r F}).toReal ≤
    (measure (boxGraph (0, 0) r) θ
      (BoundaryCondition.wired (boxVertexBoundary (0, 0) r))
      (wiredBoxCylinderEvent (0, 0) r F)).toReal := by
  exact embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) θ
    (pottsESBoundaryCondition V) (boxVertexBoundary (0, 0) r)
    (fun {x} hx {y} hxy => boxInterior_neighbor_closed_in_shell V r hV hx hxy)
    (fun {x} hx => boxInterior_avoids_shellBoundary V r hV hx)
    (wiredBoxCylinderEvent (0, 0) r F)
    (wiredBoxCylinderEvent_upper (0, 0) r F)

theorem pottsESWiredShell_upper_le_wiredBox
    (V : Finset (ℤ × ℤ)) (θ : Parameters) (r : ℕ)
    (hV : latticeBox (0, 0) r ⊆ V)
    (S : Set (Configuration (boxGraph (0, 0) r))) (hS : IsUpperSet S) :
    (measure (pottsESGraph V) θ (pottsESBoundaryCondition V)
      {A | embeddedConfigurationRestriction (boxGraph (0, 0) r)
        (pottsESGraph V) (pottsESBoxEmbedding V r hV)
        (pottsESBoxEmbedding_map_le V r hV) A ∈ S}).toReal ≤
      (measure (boxGraph (0, 0) r) θ
        (BoundaryCondition.wired (boxVertexBoundary (0, 0) r)) S).toReal := by
  exact embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    (pottsESBoxEmbedding V r hV) (pottsESBoxEmbedding_map_le V r hV) θ
    (pottsESBoundaryCondition V) (boxVertexBoundary (0, 0) r)
    (fun {x} hx {y} hxy => boxInterior_neighbor_closed_in_shell V r hV hx hxy)
    (fun {x} hx => boxInterior_avoids_shellBoundary V r hV hx)
    S hS

def shellBaseRadius (V : Finset (ℤ × ℤ)) : ℕ :=
  subgraphBoxRadius (pottsESSupport V)

def shellGhostSite (V : Finset (ℤ × ℤ)) : ℤ × ℤ :=
  (((shellBaseRadius V + 2 : ℕ) : ℤ), 0)

 theorem shellSupport_subset_baseBox (V : Finset (ℤ × ℤ)) :
    pottsESSupport V ⊆ latticeBox (0, 0) (shellBaseRadius V) :=
  subgraph_subset_boxRadius (pottsESSupport V)

private theorem shellGhostSite_notin_baseBox (V : Finset (ℤ × ℤ)) :
    shellGhostSite V ∉ latticeBox (0, 0) (shellBaseRadius V) := by
  rw [mem_latticeBox]
  dsimp [shellGhostSite]
  omega

/-- A centered box radius containing the shell graph with room for its isolated marker. -/
def pottsESShellComparisonRadius (V : Finset (ℤ × ℤ)) : ℕ :=
  PottsContinuity.PD.RCInfinite.subgraphBoxRadius (pottsESSupport V) + 3

/-- Embed the shell graph into a larger lattice box; its isolated marker is
sent to a site outside the physical shell support. -/
def pottsESShellToBoxEmbedding (V : Finset (ℤ × ℤ)) :
    PottsESVertex V ↪ BoxVertex (0, 0) (pottsESShellComparisonRadius V) where
  toFun := fun x =>
    match x with
    | none => ⟨shellGhostSite V, by
        rw [mem_latticeBox]
        dsimp [shellGhostSite, pottsESShellComparisonRadius, shellBaseRadius]
        omega⟩
    | some x => ⟨x.val, latticeBox_mono (0, 0) (by
        dsimp [pottsESShellComparisonRadius, shellBaseRadius]
        omega) (shellSupport_subset_baseBox V x.property)⟩
  inj' := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        have hybox : y.val ∈ latticeBox (0, 0) (shellBaseRadius V) :=
          shellSupport_subset_baseBox V y.property
        have hcoord := congrArg Subtype.val h
        have hghost : shellGhostSite V = y.val := hcoord
        exact False.elim (shellGhostSite_notin_baseBox V (hghost ▸ hybox))
    | some x =>
      cases y with
      | none =>
        have hxbox : x.val ∈ latticeBox (0, 0) (shellBaseRadius V) :=
          shellSupport_subset_baseBox V x.property
        have hcoord := congrArg Subtype.val h
        have hghost : x.val = shellGhostSite V := hcoord
        exact False.elim (shellGhostSite_notin_baseBox V (hghost ▸ hxbox))
      | some y =>
        have hcoord : x.val = y.val := by
          have hval := congrArg Subtype.val h
          change x.val = y.val at hval
          exact hval
        exact congrArg some (Subtype.ext hcoord)

theorem pottsESShellToBoxEmbedding_map_le (V : Finset (ℤ × ℤ)) :
    (pottsESGraph V).map (pottsESShellToBoxEmbedding V) ≤
      boxGraph (0, 0) (pottsESShellComparisonRadius V) := by
  intro u v huv
  obtain ⟨x, y, hxy, rfl, rfl⟩ :=
    (SimpleGraph.map_adj (pottsESShellToBoxEmbedding V) (pottsESGraph V) u v).mp huv
  obtain ⟨a, b, hxa, hyb, hab⟩ := pottsESGraph_adj_endpoints V hxy
  rw [hxa, hyb]
  apply (boxGraph_adj_iff (0, 0) (pottsESShellComparisonRadius V)
    (pottsESShellToBoxEmbedding V (some a)) (pottsESShellToBoxEmbedding V (some b))).mpr
  change PottsContinuity.PD.FK.squareLattice.Adj a.val b.val
  exact hab

private theorem latticeBox_neighbor_inside_larger {r s : ℕ}
    (hrs : r + 1 ≤ s) {x y : ℤ × ℤ}
    (hx : x ∈ latticeBox (0, 0) r)
    (hxy : PottsContinuity.PD.FK.squareLattice.Adj x y) :
    y ∈ latticeBox (0, 0) s := by
  rw [mem_latticeBox] at hx ⊢
  rw [PottsContinuity.PD.FK.squareLattice_adj_iff x y] at hxy
  rcases hxy with ⟨hcoord, hother⟩ | ⟨hcoord, hother⟩
  · rcases hcoord with hcoord | hcoord <;> omega
  · rcases hother with hother | hother <;> omega

private theorem shellSupport_neighbor_of_adjacent {V : Finset (ℤ × ℤ)}
    {x y : ℤ × ℤ} (hx : x ∈ V)
    (hxy : PottsContinuity.PD.FK.squareLattice.Adj x y) :
    y ∈ pottsESSupport V := by
  have hdir : ∃ d ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)),
      y = x + d := by
    have hadj := (PottsContinuity.PD.FK.squareLattice_adj_iff x y).mp hxy
    rcases hadj with ⟨hcoord, hother⟩ | ⟨hcoord, hother⟩
    · rcases hcoord with hcoord | hcoord
      · refine ⟨(1, 0), by simp, ?_⟩
        ext <;> dsimp <;> omega
      · refine ⟨(-1, 0), by simp, ?_⟩
        ext <;> dsimp <;> omega
    · rcases hother with hcoord | hcoord
      · refine ⟨(0, 1), by simp, ?_⟩
        ext <;> dsimp <;> omega
      · refine ⟨(0, -1), by simp, ?_⟩
        ext <;> dsimp <;> omega
  obtain ⟨d, hd, hdy⟩ := hdir
  change y ∈ V ∪ V.biUnion (fun z =>
    ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)).image (fun e => z + e))
  rw [Finset.mem_union]
  right
  rw [Finset.mem_biUnion]
  refine ⟨x, hx, ?_⟩
  rw [Finset.mem_image]
  exact ⟨d, hd, hdy.symm⟩

private theorem shellGhost_not_neighbor_supported {V : Finset (ℤ × ℤ)}
    {x y : ℤ × ℤ} (hx : x ∈ pottsESSupport V)
    (hxy : PottsContinuity.PD.FK.squareLattice.Adj x y) :
    y ≠ shellGhostSite V := by
  intro hghost
  have hxbox := shellSupport_subset_baseBox V hx
  rw [mem_latticeBox] at hxbox
  dsimp [shellBaseRadius] at hxbox
  have hadj := (PottsContinuity.PD.FK.squareLattice_adj_iff x y).mp hxy
  rw [hghost] at hadj
  dsimp [shellGhostSite, shellBaseRadius] at hadj
  rcases hadj with ⟨hcoord, hother⟩ | ⟨hcoord, hother⟩
  · rcases hcoord with hcoord | hcoord <;> omega
  · omega

private theorem shellInterior_neighbor_closed_outerBox (V : Finset (ℤ × ℤ))
    {x : PottsESVertex V} (hx : x ∉ pottsESBoundary V)
    {y : BoxVertex (0, 0) (pottsESShellComparisonRadius V)}
    (hxy : (boxGraph (0, 0) (pottsESShellComparisonRadius V)).Adj
      (pottsESShellToBoxEmbedding V x) y) :
    ∃ z : PottsESVertex V, pottsESShellToBoxEmbedding V z = y ∧
      (pottsESGraph V).Adj x z := by
  cases x with
  | none =>
    have hmem : (none : PottsESVertex V) ∈ pottsESBoundary V := by
      simp [pottsESBoundary]
    exact False.elim (hx hmem)
  | some a =>
    have haV : a.val ∈ V := by
      by_contra haV
      apply hx
      change some a = none ∨ ∃ y, some a = some y ∧ y.val ∉ V
      exact Or.inr ⟨a, rfl, haV⟩
    have hlat : PottsContinuity.PD.FK.squareLattice.Adj
        a.val y.val := by
      exact (boxGraph_adj_iff (0, 0) (pottsESShellComparisonRadius V)
        (pottsESShellToBoxEmbedding V (some a)) y).mp hxy
    have hyNotGhost : y.val ≠ shellGhostSite V :=
      shellGhost_not_neighbor_supported a.property hlat
    have hySupport : y.val ∈ pottsESSupport V :=
      shellSupport_neighbor_of_adjacent haV hlat
    let b : PottsESSite V := ⟨y.val, hySupport⟩
    refine ⟨some b, ?_, ?_⟩
    · apply Subtype.ext
      rfl
    · exact pottsESGraph_adj_of_sites V a b haV hlat

private theorem shellInterior_avoids_outerBoxBoundary (V : Finset (ℤ × ℤ))
    {x : PottsESVertex V} (hx : x ∉ pottsESBoundary V) :
    pottsESShellToBoxEmbedding V x ∉
      boxVertexBoundary (0, 0) (pottsESShellComparisonRadius V) := by
  cases x with
  | none =>
    have hmem : (none : PottsESVertex V) ∈ pottsESBoundary V := by
      simp [pottsESBoundary]
    exact False.elim (hx hmem)
  | some a =>
    have haV : a.val ∈ V := by
      by_contra haV
      apply hx
      change some a = none ∨ ∃ y, some a = some y ∧ y.val ∉ V
      exact Or.inr ⟨a, rfl, haV⟩
    intro hboundary
    change (pottsESShellToBoxEmbedding V (some a)).val ∈
      PottsContinuity.PD.vertexBoundary
        (latticeBox (0, 0) (pottsESShellComparisonRadius V)) at hboundary
    obtain ⟨_, z, haz, hzout⟩ := hboundary
    have haBox := shellSupport_subset_baseBox V a.property
    have hzBox : z ∈ latticeBox (0, 0) (pottsESShellComparisonRadius V) :=
      latticeBox_neighbor_inside_larger (by
        dsimp [pottsESShellComparisonRadius, shellBaseRadius]
        omega) haBox haz
    exact hzout hzBox

theorem wiredBox_restriction_le_pottsESWiredShell
    (V : Finset (ℤ × ℤ)) (θ : Parameters)
    (S : Set (Configuration (pottsESGraph V))) (hS : IsUpperSet S) :
    (measure (boxGraph (0, 0) (pottsESShellComparisonRadius V)) θ
      (BoundaryCondition.wired
        (boxVertexBoundary (0, 0) (pottsESShellComparisonRadius V)))
      {A | embeddedConfigurationRestriction (pottsESGraph V)
        (boxGraph (0, 0) (pottsESShellComparisonRadius V))
        (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) A ∈ S}).toReal ≤
    (measure (pottsESGraph V) θ (pottsESBoundaryCondition V) S).toReal := by
  exact embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    (pottsESShellToBoxEmbedding V) (pottsESShellToBoxEmbedding_map_le V) θ
    (BoundaryCondition.wired (boxVertexBoundary (0, 0) (pottsESShellComparisonRadius V)))
    (pottsESBoundary V)
    (fun {x} hx {y} hxy => shellInterior_neighbor_closed_outerBox V hx hxy)
    (fun {x} hx => shellInterior_avoids_outerBoxBoundary V hx)
    S hS
  
end

end PottsContinuity.Thm1
