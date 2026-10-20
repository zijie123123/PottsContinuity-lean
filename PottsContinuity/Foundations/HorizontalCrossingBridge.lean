module

public import PottsContinuity.Frozen.Defs
public import PottsContinuity.PD.Duality.RectangleEvents
public import PottsContinuity.PD.FK.ConfigurationBridge

@[expose] public section

namespace PottsContinuity.Foundations

open PottsContinuity.PD.FK

/-- Restrict a Boolean state on a larger induced domain to the bonds of a
closed rectangle contained in that domain. -/
noncomputable def rectangleRestriction
    (a : LatticeVertex) (w h : ℕ) (V : Finset LatticeVertex)
    (hV : PottsContinuity.PD.FK.latticeRectangle a w h ⊆ V)
    (ω : (PottsContinuity.PD.FK.squareLattice.induce
      (V : Set LatticeVertex)).edgeSet → Bool) :
    (PottsContinuity.PD.FK.rectangleGraph a w h).edgeSet → Bool := by
  let hsets : (PottsContinuity.PD.FK.latticeRectangle a w h :
      Set LatticeVertex) ⊆ (V : Set LatticeVertex) :=
    fun x hx => hV hx
  exact fun e => ω
    ((PottsContinuity.PD.FK.squareLattice.induceHomOfLE hsets).mapEdgeSet e)

private theorem openGraphAdj_restriction {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (j : G ↪g H)
    (ωR : G.edgeSet → Bool) (ω : H.edgeSet → Bool)
    (hstate : ∀ e, ωR e = ω (j.mapEdgeSet e)) (u v : X) :
    (openGraph G (boolConfigurationEquiv G ωR)).Adj u v ↔
      (openGraph H (boolConfigurationEquiv H ω)).Adj (j u) (j v) := by
  rw [openGraph_adj, openGraph_adj,
    openEdges_boolConfigurationEquiv, openEdges_boolConfigurationEquiv]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨he, hopen⟩
    have hadj : G.Adj u v := G.mem_edgeSet.mp he
    have htarget : H.Adj (j u) (j v) := j.map_rel_iff'.2 hadj
    have hetarget : s(j u, j v) ∈ H.edgeSet := H.mem_edgeSet.mpr htarget
    let e : G.edgeSet := ⟨s(u, v), he⟩
    refine ⟨hetarget, ?_⟩
    have heq : j.mapEdgeSet e = ⟨s(j u, j v), hetarget⟩ := by
      apply Subtype.ext
      change Sym2.map j (s(u, v)) = s(j u, j v)
      simp
    rw [← heq, ← hstate e]
    exact hopen
  · rintro ⟨he, hopen⟩
    have hadj : H.Adj (j u) (j v) := H.mem_edgeSet.mp he
    have hsource : G.Adj u v := j.map_rel_iff'.1 hadj
    have hesource : s(u, v) ∈ G.edgeSet := G.mem_edgeSet.mpr hsource
    let e : G.edgeSet := ⟨s(u, v), hesource⟩
    refine ⟨hesource, ?_⟩
    have heq : j.mapEdgeSet e = ⟨s(j u, j v), he⟩ := by
      apply Subtype.ext
      change Sym2.map j (s(u, v)) = s(j u, j v)
      simp
    rw [hstate e, heq]
    exact hopen

/-- A crossing witnessed in a larger induced domain is exactly the PD
rectangle crossing of the state restricted to the rectangle's bonds. -/
theorem horizontalCrossing_iff_PD_rectangleHorizontalCrossingEvent_of_restriction
    (a : LatticeVertex) (w h : ℕ) (V : Finset LatticeVertex)
    (hV : PottsContinuity.PD.FK.latticeRectangle a w h ⊆ V)
    (ω : (PottsContinuity.PD.FK.squareLattice.induce
      (V : Set LatticeVertex)).edgeSet → Bool) :
    PottsContinuity.horizontalCrossing V a.1 (a.1 + (w : ℤ))
      a.2 (a.2 + (h : ℤ)) ω ↔
      boolConfigurationEquiv (rectangleGraph a w h)
        (rectangleRestriction a w h V hV ω) ∈ rectangleHorizontalCrossingEvent a w h := by
  classical
  let hsets : (PottsContinuity.PD.FK.latticeRectangle a w h :
      Set LatticeVertex) ⊆ (V : Set LatticeVertex) := fun x hx => hV hx
  let j : rectangleGraph a w h ↪g
      (PottsContinuity.PD.FK.squareLattice.induce (V : Set LatticeVertex)) :=
    PottsContinuity.PD.FK.squareLattice.induceHomOfLE hsets
  let ωR := rectangleRestriction a w h V hV ω
  let AR := boolConfigurationEquiv (rectangleGraph a w h) ωR
  let AV := boolConfigurationEquiv
    (PottsContinuity.PD.FK.squareLattice.induce (V : Set LatticeVertex)) ω
  let KR := openGraph (rectangleGraph a w h) AR
  let HV := openGraph
    (PottsContinuity.PD.FK.squareLattice.induce (V : Set LatticeVertex)) AV
  have hstate (e : (rectangleGraph a w h).edgeSet) :
      ωR e = ω (j.mapEdgeSet e) := by
    rfl
  have hAdj (u v : RectangleVertex a w h) :
      HV.Adj (j u) (j v) ↔ KR.Adj u v := by
    exact (openGraphAdj_restriction j ωR ω hstate u v).symm
  let jOpen : KR ↪g HV := {
    toFun := j
    inj' := j.injective
    map_rel_iff' := by
      intro u v
      exact hAdj u v
  }
  let isoRange := jOpen.isoInduceRange
  have hHV : HV = PottsContinuity.rcOpenGraph V ω :=
    PottsContinuity.PD.FK.rcOpenGraph_eq V ω
  have hHVle : HV ≤ PottsContinuity.rcOpenGraph V ω := by
    rw [hHV]
  have hRcToHV : PottsContinuity.rcOpenGraph V ω ≤ HV := by
    rw [hHV]
  have hrect_coords (z : LatticeVertex)
      (hz : z ∈ Set.Icc a.1 (a.1 + (w : ℤ)) ×ˢ
        Set.Icc a.2 (a.2 + (h : ℤ))) :
      z ∈ PottsContinuity.PD.FK.latticeRectangle a w h := by
    rw [PottsContinuity.PD.FK.mem_latticeRectangle]
    simpa only [Set.mem_prod, Set.mem_Icc] using hz
  have hleft (x : RectangleVertex a w h) :
      x.val ∈ rectangleLeftSide a w h ↔ x.val.1 = a.1 := by
    simp [rectangleLeftSide, x.property]
  have hright (x : RectangleVertex a w h) :
      x.val ∈ rectangleRightSide a w h ↔ x.val.1 = a.1 + (w : ℤ) := by
    simp [rectangleRightSide, x.property]
  constructor
  · rintro ⟨x, y, walk, hx, hy, hsupport⟩
    have hx' : x.val.1 = a.1 ∧ a.2 ≤ x.val.2 ∧ x.val.2 ≤ a.2 + (h : ℤ) := by
      simpa only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] using hx
    have hy' : y.val.1 = a.1 + (w : ℤ) ∧
        a.2 ≤ y.val.2 ∧ y.val.2 ≤ a.2 + (h : ℤ) := by
      simpa only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] using hy
    have hxrect : x.val ∈ PottsContinuity.PD.FK.latticeRectangle a w h := by
      rw [PottsContinuity.PD.FK.mem_latticeRectangle]
      constructor
      · constructor <;> omega
      · exact ⟨hx'.2.1, hx'.2.2⟩
    have hyrect : y.val ∈ PottsContinuity.PD.FK.latticeRectangle a w h := by
      rw [PottsContinuity.PD.FK.mem_latticeRectangle]
      constructor
      · constructor <;> omega
      · exact ⟨hy'.2.1, hy'.2.2⟩
    let u : RectangleVertex a w h := ⟨x.val, hxrect⟩
    let v : RectangleVertex a w h := ⟨y.val, hyrect⟩
    have hju : j u = x := by
      apply Subtype.ext
      rfl
    have hjv : j v = y := by
      apply Subtype.ext
      rfl
    let walkHV : HV.Walk x y := walk.mapLe hRcToHV
    have hsupportHV : ∀ z ∈ walkHV.support, z ∈ Set.range jOpen := by
      intro z hz
      have hzold : z ∈ walk.support := by
        simpa only [walkHV, SimpleGraph.Walk.support_mapLe_eq_support] using hz
      have hzrect := hrect_coords z.val (hsupport z hzold)
      refine ⟨⟨z.val, hzrect⟩, ?_⟩
      apply Subtype.ext
      change (j ⟨z.val, hzrect⟩).val = z.val
      rfl
    let walkInd := walkHV.induce (Set.range jOpen) hsupportHV
    have hxrange :
        (⟨x, hsupportHV x walkHV.start_mem_support⟩ : Set.range jOpen) = isoRange u := by
      apply Subtype.ext
      change x = jOpen u
      exact hju.symm
    have hyrange :
        (⟨y, hsupportHV y walkHV.end_mem_support⟩ : Set.range jOpen) = isoRange v := by
      apply Subtype.ext
      change y = jOpen v
      exact hjv.symm
    have walkR : KR.Walk u v := by
      have hw := walkInd.map isoRange.symm.toHom
      have huInv : isoRange.symm.toHom (isoRange u) = u := by
        change isoRange.symm (isoRange u) = u
        exact RelIso.symm_apply_apply _ _
      have hvInv : isoRange.symm.toHom (isoRange v) = v := by
        change isoRange.symm (isoRange v) = v
        exact RelIso.symm_apply_apply _ _
      simpa only [hxrange, hyrange, huInv, hvInv] using hw
    refine ⟨u, v, ?_, ?_, ?_⟩
    · exact (hleft u).mpr hx'.1
    · exact (hright v).mpr hy'.1
    · exact (PD.FK.actualConnected_iff_walk _ _ _ _).2 ⟨walkR⟩
  · rintro ⟨u, v, hu, hv, hconn⟩
    obtain ⟨walkR⟩ := (PD.FK.actualConnected_iff_walk _ _ _ _).1 hconn
    let walkHV := walkR.map jOpen.toHom
    have hcoordU := (hleft u).mp hu
    have hcoordV := (hright v).mp hv
    have huY : a.2 ≤ u.val.2 ∧ u.val.2 ≤ a.2 + (h : ℤ) := by
      have huProp := u.property
      simp only [PottsContinuity.PD.FK.latticeRectangle,
        Finset.mem_product, Finset.mem_Icc] at huProp
      exact huProp.2
    have hvY : a.2 ≤ v.val.2 ∧ v.val.2 ≤ a.2 + (h : ℤ) := by
      have hvProp := v.property
      simp only [PottsContinuity.PD.FK.latticeRectangle,
        Finset.mem_product, Finset.mem_Icc] at hvProp
      exact hvProp.2
    have hjvalU : (jOpen u).val = u.val := by
      rfl
    have hjvalV : (jOpen v).val = v.val := by
      rfl
    refine ⟨jOpen u, jOpen v, walkHV.mapLe hHVle, ?_, ?_, ?_⟩
    · change (jOpen u).val ∈ ({a.1} : Set ℤ) ×ˢ
        Set.Icc a.2 (a.2 + (h : ℤ))
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc]
      rw [hjvalU]
      exact ⟨hcoordU, huY.1, huY.2⟩
    · change (jOpen v).val ∈ ({a.1 + (w : ℤ)} : Set ℤ) ×ˢ
        Set.Icc a.2 (a.2 + (h : ℤ))
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc]
      rw [hjvalV]
      exact ⟨hcoordV, hvY.1, hvY.2⟩
    · intro z hz
      have hz₁ : z ∈ walkHV.support := by
        simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hz
      have hz' : z ∈ walkR.support.map jOpen.toHom := by
        simpa only [walkHV, SimpleGraph.Walk.support_map] using hz₁
      rcases List.mem_map.mp hz' with ⟨z', hz'', rfl⟩
      have hzRectSet : z'.val ∈ Set.Icc a.1 (a.1 + (w : ℤ)) ×ˢ
          Set.Icc a.2 (a.2 + (h : ℤ)) := by
        have hzProp := z'.property
        simp only [PottsContinuity.PD.FK.latticeRectangle,
          Finset.mem_product, Finset.mem_Icc] at hzProp
        simp only [Set.mem_prod, Set.mem_Icc]
        exact hzProp
      change (jOpen.toHom z').val ∈ Set.Icc a.1 (a.1 + (w : ℤ)) ×ˢ
        Set.Icc a.2 (a.2 + (h : ℤ))
      have hzVal : (jOpen z').val = z'.val := by rfl
      change (jOpen z').val ∈ Set.Icc a.1 (a.1 + (w : ℤ)) ×ˢ
        Set.Icc a.2 (a.2 + (h : ℤ))
      rw [hzVal]
      exact hzRectSet

/-- Integer-corner form of the restriction bridge. The inequalities ensure the
rectangle is represented by natural side lengths in the PD rectangle carrier.
-/
theorem pdRectangle_eq_frozenRectangle_of_corners
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d) :
    PottsContinuity.PD.FK.latticeRectangle
        (a, c) (b - a).toNat (d - c).toNat =
      PottsContinuity.latticeRectangle a b c d := by
  have hwidth : ((b - a).toNat : ℤ) = b - a :=
    Int.toNat_of_nonneg (by omega)
  have hheight : ((d - c).toNat : ℤ) = d - c :=
    Int.toNat_of_nonneg (by omega)
  ext z
  simp only [PottsContinuity.PD.FK.latticeRectangle,
    PottsContinuity.latticeRectangle, Finset.mem_product, Finset.mem_Icc]
  rw [hwidth, hheight]
  omega

theorem horizontalCrossing_iff_PD_rectangleHorizontalCrossingEvent_of_corners
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (V : Finset (ℤ × ℤ))
    (hV : PottsContinuity.PD.FK.latticeRectangle
      (a, c) (b - a).toNat (d - c).toNat ⊆ V)
    (ω : (PottsContinuity.squareLattice.induce
      (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    PottsContinuity.horizontalCrossing V a b c d ω ↔
      boolConfigurationEquiv
        (rectangleGraph (a, c) (b - a).toNat (d - c).toNat)
        (rectangleRestriction (a, c) (b - a).toNat (d - c).toNat V
          hV ω) ∈
        rectangleHorizontalCrossingEvent (a, c) (b - a).toNat (d - c).toNat := by
  classical
  have hb : a + ((b - a).toNat : ℤ) = b := by
    have hwidth : ((b - a).toNat : ℤ) = b - a :=
      Int.toNat_of_nonneg (by omega)
    rw [hwidth]
    omega
  have hd : c + ((d - c).toNat : ℤ) = d := by
    have hheight : ((d - c).toNat : ℤ) = d - c :=
      Int.toNat_of_nonneg (by omega)
    rw [hheight]
    omega
  simpa only [hb, hd] using
    (horizontalCrossing_iff_PD_rectangleHorizontalCrossingEvent_of_restriction
      (a, c) (b - a).toNat (d - c).toNat V hV ω)

end PottsContinuity.Foundations
