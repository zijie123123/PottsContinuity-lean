-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/BoundarySeedComplementConnectivity.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.BoundarySeedComplementFreeLaw
public import PottsContinuity.FKC.FiniteFK.WiredAvoidingConnectionRestriction
public import PottsContinuity.FKC.FiniteFK.WiredAvoidingRecordConnection
public import PottsContinuity.FKC.FiniteFK.Isomorphism
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance boundarySeedConnectivityVertexFintype : Fintype V := Fintype.ofFinite V

/-- With the empty forbidden set, every actual open connection between
vertices outside the explored boundary-seed cluster is already a connection
in the induced complement with the restricted configuration. -/
theorem boundarySeedComplement_actualConnected_iff
    (ξ : BoundaryCondition V) (A : Configuration G)
    {x y : wiredAvoidingComplementSet G (∅ : Set V) ξ.boundary.toFinset A} :
    ActualConnected G A x.val y.val ↔
      ActualConnected (G.induce
        (wiredAvoidingComplementSet G (∅ : Set V) ξ.boundary.toFinset A))
        (embeddedConfigurationRestriction
          (G.induce (wiredAvoidingComplementSet G (∅ : Set V) ξ.boundary.toFinset A)) G
          (wiredAvoidingComplementEmbedding G (∅ : Set V) ξ.boundary.toFinset A)
          (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V)
            ξ.boundary.toFinset A) A) x y := by
  let S : Finset V := ξ.boundary.toFinset
  let C := wiredAvoidingClusterSet G (∅ : Set V) S A
  let H := G.induce (wiredAvoidingComplementSet G (∅ : Set V) S A)
  let R := embeddedConfigurationRestriction H G
    (wiredAvoidingComplementEmbedding G (∅ : Set V) S A)
    (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S A) A
  constructor
  · intro hxy
    change (openGraph G A).Reachable x.val y.val at hxy
    have havoid : ∀ {v : V}, Relation.ReflTransGen (openGraph G A).Adj x.val v → v ∉ C := by
      intro v hpath
      induction hpath with
      | refl => exact x.property
      | @tail z v hprefix hedge ih =>
          intro hvC
          have hzC : z ∈ C :=
            wiredAvoidingClusterSet_openEdge_closed (W := (∅ : Set V)) S A
              hvC (by simp) hedge.symm
          exact ih hzC
    have hrestricted : Relation.ReflTransGen (openGraph H R).Adj x y := by
      have hpath : Relation.ReflTransGen (openGraph G A).Adj x.val y.val :=
        (SimpleGraph.reachable_iff_reflTransGen _ _).mp hxy
      have hmap : ∀ {v : V}, (hpath : Relation.ReflTransGen
          (openGraph G A).Adj x.val v) →
          Relation.ReflTransGen (openGraph H R).Adj x ⟨v, havoid hpath⟩ := by
        intro v hpath
        induction hpath with
        | refl => exact Relation.ReflTransGen.refl
        | @tail z v hprefix hedge ih =>
            have hadj : (openGraph H R).Adj ⟨z, havoid hprefix⟩
                ⟨v, havoid (hprefix.tail hedge)⟩ :=
              (wiredAvoidingComplement_openAdj_iff (W := (∅ : Set V)) S A
                ⟨z, havoid hprefix⟩ ⟨v, havoid (hprefix.tail hedge)⟩).2 hedge
            exact ih.tail hadj
      have hresult := hmap hpath
      have hendpoint : (⟨y.val, havoid hpath⟩ :
          wiredAvoidingComplementSet G (∅ : Set V) S A) = y :=
        Subtype.ext rfl
      rw [hendpoint] at hresult
      exact hresult
    change (openGraph H R).Reachable x y
    exact (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hrestricted
  · intro hxy
    change (openGraph H R).Reachable x y at hxy
    change (openGraph G A).Reachable x.val y.val
    exact SimpleGraph.Reachable.map
      (show openGraph H R →g openGraph G A from
        { toFun := Subtype.val
          map_rel' := by
            intro u v huv
            exact (wiredAvoidingComplement_openAdj_iff (W := (∅ : Set V)) S A u v).mp huv })
      hxy


/-- On a fixed attained all-boundary-seed record, the same connectivity
criterion holds on the complement carrier selected by the record's reference
configuration. -/
theorem boundarySeedComplement_actualConnected_iff_of_record
    (ξ : BoundaryCondition V) (A₀ B : Configuration G)
    (hrecord : B ∈ revealRecordEvent G
      (wiredAvoidingClusterReveal G (∅ : Set V) ξ.boundary.toFinset) A₀)
    {x y : wiredAvoidingComplementSet G (∅ : Set V) ξ.boundary.toFinset A₀} :
    ActualConnected G B x.val y.val ↔
      ActualConnected (G.induce
        (wiredAvoidingComplementSet G (∅ : Set V) ξ.boundary.toFinset A₀))
        (embeddedConfigurationRestriction
          (G.induce (wiredAvoidingComplementSet G (∅ : Set V) ξ.boundary.toFinset A₀)) G
          (wiredAvoidingComplementEmbedding G (∅ : Set V) ξ.boundary.toFinset A₀)
          (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V)
            ξ.boundary.toFinset A₀) B) x y := by
  let S : Finset V := ξ.boundary.toFinset
  let C0 := wiredAvoidingComplementSet G (∅ : Set V) S A₀
  let CB := wiredAvoidingComplementSet G (∅ : Set V) S B
  let H0 := G.induce C0
  let HB := G.induce CB
  let R0 := embeddedConfigurationRestriction H0 G
    (wiredAvoidingComplementEmbedding G (∅ : Set V) S A₀)
    (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S A₀) B
  let RB := embeddedConfigurationRestriction HB G
    (wiredAvoidingComplementEmbedding G (∅ : Set V) S B)
    (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S B) B
  have hclusters := wiredAvoidingClusterSet_eq_of_record
    (W := (∅ : Set V)) S A₀ B hrecord
  have hcomp : C0 = CB := by
    dsimp [C0, CB, wiredAvoidingComplementSet]
    rw [hclusters]
  have hxB : x.val ∉ wiredAvoidingClusterSet G (∅ : Set V) S B := by
    rw [hclusters]
    exact x.property
  have hyB : y.val ∉ wiredAvoidingClusterSet G (∅ : Set V) S B := by
    rw [hclusters]
    exact y.property
  let xB : CB := ⟨x.val, hxB⟩
  let yB : CB := ⟨y.val, hyB⟩
  have hlocal := boundarySeedComplement_actualConnected_iff (G := G) ξ B
    (x := xB) (y := yB)
  let eSet : C0 ≃ CB := Set.equivOfEq hcomp
  let e : H0 ≃g HB := {
    toEquiv := eSet
    map_rel_iff' := by
      intro u v
      rfl
  }
  have heval (u : C0) : (e u).val = u.val := rfl
  have hevalSymm (u : CB) : (e.symm u).val = u.val := rfl
  have hOuter (a : H0.edgeSet) :
      embeddedEdgeEmbedding H0 G (wiredAvoidingComplementEmbedding G (∅ : Set V) S A₀)
          (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S A₀) a =
        embeddedEdgeEmbedding HB G (wiredAvoidingComplementEmbedding G (∅ : Set V) S B)
          (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S B)
          (configurationIsoEdgeEquiv e a) := by
    apply Subtype.ext
    change Sym2.map (fun u : C0 => u.val) a.val =
      Sym2.map (fun u : CB => u.val) (Sym2.map (fun u : C0 => e u) a.val)
    rw [Sym2.map_map]
    congr 1
  have hR : configurationIso e R0 = RB := by
    ext eb
    change eb ∈ (configurationIso e R0).val ↔ eb ∈ RB.val
    change eb ∈ R0.val.map (configurationIsoEdgeEquiv e).toEmbedding ↔ eb ∈ RB.val
    constructor
    · intro hmem
      rcases Finset.mem_map.mp hmem with ⟨a, ha, hmap⟩
      have haB : embeddedEdgeEmbedding H0 G
          (wiredAvoidingComplementEmbedding G (∅ : Set V) S A₀)
          (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S A₀) a ∈ B :=
        (mem_embeddedConfigurationRestriction H0 G
          (wiredAvoidingComplementEmbedding G (∅ : Set V) S A₀)
          (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S A₀) B a).mp ha
      have hEdge : configurationIsoEdgeEquiv e a = eb := hmap
      have hEq := hOuter a
      rw [hEdge] at hEq
      exact (mem_embeddedConfigurationRestriction HB G
        (wiredAvoidingComplementEmbedding G (∅ : Set V) S B)
        (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S B) B eb).2
          (by rw [← hEq]; exact haB)
    · intro heb
      let a : H0.edgeSet := (configurationIsoEdgeEquiv e).symm eb
      have hEdge : configurationIsoEdgeEquiv e a = eb := Equiv.apply_symm_apply _ _
      apply Finset.mem_map.mpr
      refine ⟨a, ?_, hEdge⟩
      have hbB : embeddedEdgeEmbedding HB G
          (wiredAvoidingComplementEmbedding G (∅ : Set V) S B)
          (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S B) eb ∈ B :=
        (mem_embeddedConfigurationRestriction HB G
          (wiredAvoidingComplementEmbedding G (∅ : Set V) S B)
          (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S B) B eb).mp heb
      have hEq := hOuter a
      rw [hEdge] at hEq
      exact (mem_embeddedConfigurationRestriction H0 G
        (wiredAvoidingComplementEmbedding G (∅ : Set V) S A₀)
        (wiredAvoidingComplementGraph_le (G := G) (∅ : Set V) S A₀) B a).2
          (by rw [hEq]; exact hbB)
  have hex : e x = xB := by
    apply Subtype.ext
    exact heval x
  have hey : e y = yB := by
    apply Subtype.ext
    exact heval y
  have htransport := actualConnected_configurationIso e R0 x y
  have htransport' : ActualConnected HB RB xB yB ↔ ActualConnected H0 R0 x y := by
    simpa [hR, hex, hey] using htransport
  have hlocal' : ActualConnected G B x.val y.val ↔ ActualConnected HB RB xB yB := by
    simpa [xB, yB, RB, HB, CB] using hlocal
  have hresult := hlocal'.trans htransport'
  simpa [R0, H0, C0, S] using hresult

end
end PottsContinuity.FKC.FiniteFK
