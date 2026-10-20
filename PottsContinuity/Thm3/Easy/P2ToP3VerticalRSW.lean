module

public import Mathlib
public import PottsContinuity.BD12.WiredSquare
public import PottsContinuity.Foundations.EveryExhaustion
public import PottsContinuity.Infinite.Symmetry
public import PottsContinuity.PlanarTopology.SubpathExtraction

@[expose] public section

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD.FK

namespace PottsContinuity.Thm3.Easy

def weakRSWMapIso : PottsContinuity.PD.FK.squareLattice ≃g
    PottsContinuity.PD.FK.squareLattice where
  toFun v := (v.2 - 1, v.1)
  invFun v := (v.2, v.1 + 1)
  left_inv v := by ext <;> dsimp; omega
  right_inv v := by ext <;> dsimp; omega
  map_rel_iff' := by
    intro u v
    change PottsContinuity.PD.FK.squareLattice.Adj
        (u.2 - 1, u.1) (v.2 - 1, v.1) ↔
      PottsContinuity.PD.FK.squareLattice.Adj u v
    rw [PottsContinuity.PD.FK.squareLattice_adj_iff,
      PottsContinuity.PD.FK.squareLattice_adj_iff]
    omega

private theorem weakRSWMapIso_mem_latticeBox
    (c v : PottsContinuity.PD.FK.LatticeVertex) (r : ℕ) :
    weakRSWMapIso v ∈ PottsContinuity.PD.FK.latticeBox
      (weakRSWMapIso c) r ↔ v ∈ PottsContinuity.PD.FK.latticeBox c r := by
  rw [PottsContinuity.PD.FK.mem_latticeBox,
    PottsContinuity.PD.FK.mem_latticeBox]
  change ((c.2 - 1 - (r : ℤ) ≤ v.2 - 1 ∧
      v.2 - 1 ≤ c.2 - 1 + (r : ℤ)) ∧
    (c.1 - (r : ℤ) ≤ v.1 ∧ v.1 ≤ c.1 + (r : ℤ))) ↔
    ((c.1 - (r : ℤ) ≤ v.1 ∧ v.1 ≤ c.1 + (r : ℤ)) ∧
      (c.2 - (r : ℤ) ≤ v.2 ∧ v.2 ≤ c.2 + (r : ℤ)))
  omega

/-- A crossing of the `(n+1)`-by-`n` rectangle becomes a vertical crossing
of `[0,n] × [0,n+1]` after the transpose and translation. -/
private theorem horizontalRectangle_subset_preimage_verticalRectangle (n : ℕ) :
    BD12.horizontalRectangle ((0 : ℤ), 1) (n + 1) n ⊆
      (latticeConfigurationIsoHomeomorph weakRSWMapIso) ⁻¹'
        BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1) := by
  intro ω hω
  change ∃ u v : PottsContinuity.PD.FK.RectangleVertex ((0 : ℤ), 1) (n + 1) n,
    u.val ∈ PottsContinuity.PD.FK.rectangleLeftSide ((0 : ℤ), 1) (n + 1) n ∧
      v.val ∈ PottsContinuity.PD.FK.rectangleRightSide ((0 : ℤ), 1) (n + 1) n ∧
      PottsContinuity.PD.FK.ActualConnected
        (PottsContinuity.PD.FK.rectangleGraph ((0 : ℤ), 1) (n + 1) n)
        (BD12.embeddedRestriction
          (PottsContinuity.PD.FK.rectangleGraph ((0 : ℤ), 1) (n + 1) n)
          (PottsContinuity.PD.FK.frozenEdgeEmbedding
            (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 1) (n + 1) n)) ω)
        u v at hω
  rcases hω with ⟨u, v, hu, hv, huv⟩
  have hucoord : u.val.1 = 0 := by
    have hh := (Finset.mem_filter.mp hu).2
    simpa [PottsContinuity.PD.FK.rectangleLeftSide] using hh
  have hvcoord : v.val.1 = (n + 1 : ℤ) := by
    have hh := (Finset.mem_filter.mp hv).2
    simpa [PottsContinuity.PD.FK.rectangleRightSide] using hh
  have hreach := huv
  change (PottsContinuity.PD.FK.openGraph
      (PottsContinuity.PD.FK.rectangleGraph ((0 : ℤ), 1) (n + 1) n)
      (BD12.embeddedRestriction
        (PottsContinuity.PD.FK.rectangleGraph ((0 : ℤ), 1) (n + 1) n)
        (PottsContinuity.PD.FK.frozenEdgeEmbedding
          (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 1) (n + 1) n)) ω)).Reachable u v at hreach
  change (PottsContinuity.PD.FK.openGraph
      (PottsContinuity.PD.squareLattice.induce
        (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 1) (n + 1) n :
          Set PottsContinuity.PD.FK.LatticeVertex))
      (BD12.embeddedRestriction
        (PottsContinuity.PD.squareLattice.induce
          (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 1) (n + 1) n :
            Set PottsContinuity.PD.FK.LatticeVertex))
        (PottsContinuity.PD.FK.frozenEdgeEmbedding
          (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 1) (n + 1) n)) ω)).Reachable u v at hreach
  rw [BD12.embeddedRestriction_domainGraph] at hreach
  rw [← PottsContinuity.PD.Duality.wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph ω]
    at hreach
  obtain ⟨p⟩ := hreach
  let p0 : (PottsContinuity.PD.FK.Medial.wholePlaneOpenPrimalGraph ω).Walk
      u.val v.val :=
    p.map (SimpleGraph.Embedding.induce _).toHom
  let p1 : (PottsContinuity.PD.FK.Medial.wholePlaneOpenPrimalGraph
      (latticeConfigurationIsoHomeomorph weakRSWMapIso ω)).Walk
      (weakRSWMapIso u.val) (weakRSWMapIso v.val) :=
    p0.map (PottsContinuity.PD.Duality.wholePlaneOpenGraphIso
      weakRSWMapIso ω).toHom
  have hp0support : p0.support = p.support.map
      (fun z => (SimpleGraph.Embedding.induce
        (G := PottsContinuity.PD.FK.Medial.wholePlaneOpenPrimalGraph ω)
        (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 1) (n + 1) n :
          Set PottsContinuity.PD.FK.LatticeVertex)).toHom z) := by
    exact SimpleGraph.Walk.support_map
      (f := (SimpleGraph.Embedding.induce
        (G := PottsContinuity.PD.FK.Medial.wholePlaneOpenPrimalGraph ω)
        (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 1) (n + 1) n :
          Set PottsContinuity.PD.FK.LatticeVertex)).toHom) p
  have hp1support : p1.support = p0.support.map
      (fun z => (PottsContinuity.PD.Duality.wholePlaneOpenGraphIso
        weakRSWMapIso ω).toHom z) := by
    exact SimpleGraph.Walk.support_map
      (f := (PottsContinuity.PD.Duality.wholePlaneOpenGraphIso
        weakRSWMapIso ω).toHom) p0
  have hp1bound : ∀ x ∈ p1.support,
      x ∈ PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 0) n (n + 1) := by
    intro x hx
    have hx1 : x ∈ p0.support.map
        (fun y => (PottsContinuity.PD.Duality.wholePlaneOpenGraphIso
          weakRSWMapIso ω).toHom y) := by
      rw [hp1support] at hx
      exact hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx1
    have hy1 : y ∈ p.support.map
        (fun z => (SimpleGraph.Embedding.induce
          (G := PottsContinuity.PD.FK.Medial.wholePlaneOpenPrimalGraph ω)
          (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 1) (n + 1) n :
            Set PottsContinuity.PD.FK.LatticeVertex)).toHom z) := by
      rw [hp0support] at hy
      exact hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy1
    change weakRSWMapIso z.val ∈
      PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 0) n (n + 1)
    have hs := (PottsContinuity.PD.FK.mem_latticeRectangle
      ((0 : ℤ), 1) z.val (n + 1) n).mp z.property
    apply (PottsContinuity.PD.FK.mem_latticeRectangle
      ((0 : ℤ), 0) (weakRSWMapIso z.val) n (n + 1)).mpr
    dsimp [weakRSWMapIso]
    omega
  let x : PottsContinuity.PD.FK.RectangleVertex ((0 : ℤ), 0) n (n + 1) :=
    ⟨weakRSWMapIso u.val,
      hp1bound (weakRSWMapIso u.val) p1.start_mem_support⟩
  let y : PottsContinuity.PD.FK.RectangleVertex ((0 : ℤ), 0) n (n + 1) :=
    ⟨weakRSWMapIso v.val,
      hp1bound (weakRSWMapIso v.val) p1.end_mem_support⟩
  let p2 : ((PottsContinuity.PD.FK.Medial.wholePlaneOpenPrimalGraph
      (latticeConfigurationIsoHomeomorph weakRSWMapIso ω)).induce
        (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 0) n (n + 1) :
          Set PottsContinuity.PD.FK.LatticeVertex)).Walk x y :=
    p1.induce (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 0) n (n + 1) :
      Set PottsContinuity.PD.FK.LatticeVertex) hp1bound
  have hxbot : x.val.2 = 0 := by
    change (weakRSWMapIso u.val).2 = 0
    simpa [weakRSWMapIso] using hucoord
  have hytop : y.val.2 = (n + 1 : ℤ) := by
    change (weakRSWMapIso v.val).2 = (n + 1 : ℤ)
    simpa [weakRSWMapIso] using hvcoord
  have hp2 : ((PottsContinuity.PD.rcInfiniteOpenGraph (latticeConfigurationIsoHomeomorph
      weakRSWMapIso ω)).induce
        (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 0) n (n + 1) :
          Set PottsContinuity.PD.FK.LatticeVertex)).Reachable x y := by
    rw [← PottsContinuity.PD.Duality.wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph
      (latticeConfigurationIsoHomeomorph weakRSWMapIso ω)]
    exact p2.reachable
  change latticeConfigurationIsoHomeomorph weakRSWMapIso ω ∈
    BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1)
  change ∃ x y : PottsContinuity.PD.FK.RectangleVertex
      ((0 : ℤ), 0) n (n + 1),
    x.val.2 = 0 ∧ y.val.2 = (0 : ℤ) + (n + 1 : ℤ) ∧
      ((PottsContinuity.PD.rcInfiniteOpenGraph
        (latticeConfigurationIsoHomeomorph weakRSWMapIso ω)).induce
        (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 0) n (n + 1) :
          Set PottsContinuity.PD.FK.LatticeVertex)).Reachable x y
  exact ⟨x, y, hxbot, by simpa using hytop, hp2⟩

/-- A vertical crossing of `[0,n] × [0,n+1]` contains a bottom-to-top
crossing of `[0,n] × [0,n]`, by stopping at the first visit to height `n`. -/
private theorem verticalRectangle_tall_subset_target (n : ℕ) :
    BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1) ⊆
      BD12.verticalRectangle (-(n : ℤ), 0) (2 * n) n := by
  intro ω hω
  rcases hω with ⟨u, v, hu, hv, huv⟩
  obtain ⟨p⟩ := huv
  let G := PottsContinuity.PD.rcInfiniteOpenGraph ω
  let p0 : G.Walk u.val v.val :=
    p.map (SimpleGraph.Embedding.induce _).toHom
  have hstep : ∀ x y, G.Adj x y → |x.2 - y.2| ≤ 1 := by
    intro x y hxy
    have hadj := (PottsContinuity.PD.RCInfinite.rcInfiniteOpenGraph_adj ω x y).mp hxy
    have hcoords := (PottsContinuity.PD.FK.squareLattice_adj_iff x y).mp hadj.1
    rcases hcoords with ⟨_, heq⟩ | ⟨_, hvert⟩
    · simp [heq]
    · rcases hvert with h | h
      · have hxy' : x.2 - y.2 = -1 := by omega
        rw [hxy']
        norm_num
      · have hxy' : x.2 - y.2 = 1 := by omega
        rw [hxy']
        norm_num
  have hstartle : u.val.2 ≤ (n : ℤ) := by
    rw [hu]
    omega
  have hendge : (n : ℤ) ≤ v.val.2 := by
    rw [hv]
    omega
  obtain ⟨z, r, s, hz, hsplit, hrupper⟩ :=
    PlanarTopology.walk_prefix_at_level (fun x : LatticeVertex => x.2)
      hstep p0 (n : ℤ) hstartle hendge
  have hp0_support : p0.support = p.support.map
      (fun y => (SimpleGraph.Embedding.induce
        (G := PottsContinuity.PD.rcInfiniteOpenGraph ω)
        (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 0) n (n + 1) :
          Set PottsContinuity.PD.FK.LatticeVertex)).toHom y) := by
    exact SimpleGraph.Walk.support_map
      (f := (SimpleGraph.Embedding.induce
        (G := PottsContinuity.PD.rcInfiniteOpenGraph ω)
        (PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 0) n (n + 1) :
          Set PottsContinuity.PD.FK.LatticeVertex)).toHom) p
  have hsource : ∀ x ∈ p0.support,
      x ∈ PottsContinuity.PD.FK.latticeRectangle ((0 : ℤ), 0) n (n + 1) := by
    intro x hx
    rw [hp0_support] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    simp
  have hrsub : ∀ x ∈ r.support, x ∈ p0.support := by
    intro x hx
    rw [hsplit, SimpleGraph.Walk.support_append]
    exact List.mem_append.mpr (Or.inl hx)
  have hbound : ∀ x ∈ r.support,
      x ∈ PottsContinuity.PD.FK.latticeRectangle
        (-(n : ℤ), (0 : ℤ)) (2 * n) n := by
    intro x hx
    have hs := (PottsContinuity.PD.FK.mem_latticeRectangle
      ((0 : ℤ), 0) x n (n + 1)).mp
      (hsource x (hrsub x hx))
    have hy := hrupper x hx
    apply (PottsContinuity.PD.FK.mem_latticeRectangle
      (-(n : ℤ), (0 : ℤ)) x (2 * n) n).mpr
    omega
  let x : PottsContinuity.PD.FK.RectangleVertex
      (-(n : ℤ), (0 : ℤ)) (2 * n) n :=
    ⟨u.val, hbound u.val r.start_mem_support⟩
  let y : PottsContinuity.PD.FK.RectangleVertex
      (-(n : ℤ), (0 : ℤ)) (2 * n) n :=
    ⟨z, hbound z r.end_mem_support⟩
  let q : (G.induce (PottsContinuity.PD.FK.latticeRectangle
      (-(n : ℤ), (0 : ℤ)) (2 * n) n :
        Set PottsContinuity.PD.FK.LatticeVertex)).Walk x y :=
    r.induce (PottsContinuity.PD.FK.latticeRectangle
      (-(n : ℤ), (0 : ℤ)) (2 * n) n :
        Set PottsContinuity.PD.FK.LatticeVertex) hbound
  have hxbot : x.val.2 = 0 := by
    change u.val.2 = 0
    exact hu
  have hytop : y.val.2 = (n : ℤ) := by
    change z.2 = (n : ℤ)
    exact hz
  change ∃ x y : PottsContinuity.PD.FK.RectangleVertex
      (-(n : ℤ), (0 : ℤ)) (2 * n) n,
    x.val.2 = 0 ∧ y.val.2 = (0 : ℤ) + (n : ℤ) ∧
      ((PottsContinuity.PD.rcInfiniteOpenGraph ω).induce
        (PottsContinuity.PD.FK.latticeRectangle
          (-(n : ℤ), (0 : ℤ)) (2 * n) n :
          Set PottsContinuity.PD.FK.LatticeVertex)).Reachable x y
  exact ⟨x, y, hxbot, by simpa using hytop, q.reachable⟩

/-- The half-square estimate of `BD12.WiredSquare`, transported by the wired-limit lattice
symmetry `Infinite.wired_limit_map_latticeIso` and clipped to the wider rectangle used by the
P2⇒P3 link. -/
theorem wired_weakRSW_from_square (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 1 μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ μ.real (BD12.verticalRectangle (-(n : ℤ), 0) (2 * n) n) := by
  let θ := PottsContinuity.PD.FK.criticalParameters q
  let : IsProbabilityMeasure μ := hμ.1
  have hinv := Infinite.wired_limit_map_latticeIso θ μ hμ
    weakRSWMapIso weakRSWMapIso_mem_latticeBox
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro n hn
  obtain ⟨μf, hμf⟩ := Foundations.exists_isRCInfiniteVolumeLimit
    θ.toP θ.toQ θ.property 1
  have hμfPD := Infinite.isRCInfiniteVolumeLimit_to_PD_box
    θ.toP θ.toQ 1 μf hμf
  have hμeq : μ = μf := PottsContinuity.PD.rc_limit_unique
    θ.toP θ.toQ 1 μ μf hμ hμfPD
  have hsquareF := BD12.wired_square_crossing_ge_half q μf hμf ((0 : ℤ), 1) n
  have hsquare : (1 / 2 : ℝ) ≤ μ.real
      (BD12.horizontalRectangle ((0 : ℤ), 1) (n + 1) n) := by
    rw [hμeq]
    exact hsquareF
  have htransport : μ (BD12.horizontalRectangle ((0 : ℤ), 1) (n + 1) n) ≤
      μ ((latticeConfigurationIsoHomeomorph weakRSWMapIso) ⁻¹'
        BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1)) :=
    measure_mono (horizontalRectangle_subset_preimage_verticalRectangle n)
  have hmapprob : μ ((latticeConfigurationIsoHomeomorph weakRSWMapIso) ⁻¹'
      BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1)) =
      μ (BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1)) := by
    have h := congrArg (fun ν : Measure LatticeConfiguration =>
      ν (BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1))) hinv
    rw [Measure.map_apply (latticeConfigurationIsoHomeomorph_measurable weakRSWMapIso)
      (BD12.verticalRectangle_isCylinder ((0 : ℤ), 0) n (n + 1)).measurableSet] at h
    exact h
  have htransportR : μ.real (BD12.horizontalRectangle ((0 : ℤ), 1) (n + 1) n) ≤
      μ.real ((latticeConfigurationIsoHomeomorph weakRSWMapIso) ⁻¹'
        BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1)) :=
    ENNReal.toReal_mono (measure_ne_top μ _) htransport
  have hmapR : μ.real ((latticeConfigurationIsoHomeomorph weakRSWMapIso) ⁻¹'
      BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1)) =
      μ.real (BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1)) :=
    congrArg ENNReal.toReal hmapprob
  have hclip : μ.real (BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1)) ≤
      μ.real (BD12.verticalRectangle (-(n : ℤ), 0) (2 * n) n) :=
    measureReal_mono (verticalRectangle_tall_subset_target n) (measure_ne_top μ _)
  calc
    (1 / 2 : ℝ) ≤ μ.real (BD12.horizontalRectangle ((0 : ℤ), 1) (n + 1) n) := hsquare
    _ ≤ μ.real ((latticeConfigurationIsoHomeomorph weakRSWMapIso) ⁻¹'
        BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1)) := htransportR
    _ = μ.real (BD12.verticalRectangle ((0 : ℤ), 0) n (n + 1)) := hmapR
    _ ≤ μ.real (BD12.verticalRectangle (-(n : ℤ), 0) (2 * n) n) := hclip

end PottsContinuity.Thm3.Easy
