module

public import PottsContinuity.Thm3.Push.AllHeightTipRecordSelector
public import PottsContinuity.Thm3.Push.NativeCompletionFreeSlitPrefix

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance confinedStoppedPrefixEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Physical stopped slit bonds, confined to the original precursor rectangle
0≤x≤9s, with every selected tip vertex isolated. -/
def caseTwoConfinedPrefixGraph (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) : SimpleGraph (RectangleVertex (0,0) (2*n) (2*n)) where
  Adj u v := (sourceSlitPrefixGraph (2*n) (2*n) (4*(s:ℤ)) b.2.val.2
    {z | z ∈ caseTwoTipOriginalTrace n s hfit b.1}).Adj u v ∧
    u.val.1 ≤ 9*(s:ℤ) ∧ v.val.1 ≤ 9*(s:ℤ)
  symm := by constructor; rintro u v ⟨h,hu,hv⟩; exact ⟨h.symm,hv,hu⟩
  loopless := by constructor; intro u hloop; exact
    (sourceSlitPrefixGraph (2*n) (2*n) (4*(s:ℤ)) b.2.val.2
      {z | z ∈ caseTwoTipOriginalTrace n s hfit b.1}).loopless.irrefl u hloop.1

/-- Every confined stopped bond is its exact original source bond. -/
theorem caseTwoConfinedPrefixGraph_map_le (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) :
    (caseTwoConfinedPrefixGraph n s hfit b).map (Function.Embedding.refl _) ≤
      rectangleGraph (0,0) (2*n) (2*n) := by
  change (caseTwoConfinedPrefixGraph n s hfit b).map id ≤ _
  rw [SimpleGraph.map_id]
  intro u v huv
  have hbase := sourceSlitPrefixGraph_map_le (2*n) (2*n) (4*(s:ℤ)) b.2.val.2
    {z | z ∈ caseTwoTipOriginalTrace n s hfit b.1}
  change (sourceSlitPrefixGraph _ _ _ _ _).map id ≤ _ at hbase
  rw [SimpleGraph.map_id] at hbase
  exact hbase huv.1

/-- The literal sampled configuration on the confined stopped graph. -/
def caseTwoConfinedPrefixConfiguration (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Configuration (caseTwoConfinedPrefixGraph n s hfit b) :=
  embeddedConfigurationRestriction _ _ (Function.Embedding.refl _)
    (caseTwoConfinedPrefixGraph_map_le n s hfit b) C

/-- The original native prefix remains sampled and confined in every
agreeing fiber, with no post-contact completion in the other sample. -/
theorem native_confined_prefix_openWalk_on_augmented_fiber
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C C' : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (I J : Set (RectangleVertex (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s) (D : NativeSourceArms n C I J)
    (hcol : D.column = 4*(s:ℤ)) (hright : D.rightColumn = 9*(s:ℤ))
    (hend : D.paths.secondEnd = b.2)
    (htrace : D.paths.second.support = caseTwoTipOriginalTrace n s hfit b.1)
    (hstates : C' ∩ pocketAugmentedSourceReveal (2*n) (2*n) D.column D.paths.secondEnd.val.2 D.croppedTrace D.tipTrace =
      C ∩ pocketAugmentedSourceReveal (2*n) (2*n) D.column D.paths.secondEnd.val.2 D.croppedTrace D.tipTrace) :
    ∃ p : (openGraph (caseTwoConfinedPrefixGraph n s hfit b)
      (caseTwoConfinedPrefixConfiguration n s hfit b C')).Walk
      D.paths.firstStart (D.paths.first.getVert D.cropIndex),
      p.support = (D.paths.first.take D.cropIndex).support := by
  obtain ⟨p,_,hp,_⟩ := native_retained_paths_open_on_augmented_fiber n C C' I J D hstates
  have hE : p.edges = (D.paths.first.take D.cropIndex).edges := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support,SimpleGraph.Walk.edges_eq_zipWith_support,hp]
  have hret {u v} (he : s(u,v) ∈ p.edges) :
      (openGraph (caseTwoConfinedPrefixGraph n s hfit b)
        (caseTwoConfinedPrefixConfiguration n s hfit b C')).Adj u v := by
    apply (embeddedRestriction_openGraph_adj_iff _ _ (Function.Embedding.refl _)
      (caseTwoConfinedPrefixGraph_map_le n s hfit b) C' u v).mpr
    refine ⟨⟨?_,?_,?_⟩,p.adj_of_mem_edges he⟩
    · have hslit := native_prefix_bonds_in_stopped_slit n C I J D (hE ▸ he)
      simpa only [hcol,hend,htrace] using hslit
    · rw [← hright]
      apply D.first_bounds
      apply (D.paths.first.isSubwalk_take D.cropIndex).support_subset
      rw [← hp]
      exact p.fst_mem_support_of_mem_edges he
    · rw [← hright]
      apply D.first_bounds
      apply (D.paths.first.isSubwalk_take D.cropIndex).support_subset
      rw [← hp]
      exact p.snd_mem_support_of_mem_edges he
  let P := retainedWalk _ (Function.Embedding.refl _) p hret
  refine ⟨P,?_⟩
  calc
    P.support = p.support.map (Function.Embedding.refl _) := retainedWalk_support _ _ _ _
    _ = p.support := List.map_id _
    _ = _ := hp

/-- Native base geometry gives the exact seed-to-ray connection in the
confined stopped graph throughout the fiber. It gives no selector locality. -/
theorem native_confined_prefix_connection_on_augmented_fiber
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C C' : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (I J : Set (RectangleVertex (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s) (D : NativeSourceArms n C I J)
    (hcol : D.column = 4*(s:ℤ)) (hright : D.rightColumn = 9*(s:ℤ))
    (hend : D.paths.secondEnd = b.2)
    (htrace : D.paths.second.support = caseTwoTipOriginalTrace n s hfit b.1)
    (hstates : C' ∩ pocketAugmentedSourceReveal (2*n) (2*n) D.column D.paths.secondEnd.val.2 D.croppedTrace D.tipTrace =
      C ∩ pocketAugmentedSourceReveal (2*n) (2*n) D.column D.paths.secondEnd.val.2 D.croppedTrace D.tipTrace) :
    caseTwoConfinedPrefixConfiguration n s hfit b C' ∈
      arcsConnectionEvent (caseTwoConfinedPrefixGraph n s hfit b) I
        {z | z.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.val.2} := by
  obtain ⟨p,_⟩ := native_confined_prefix_openWalk_on_augmented_fiber n s hfit C C' I J b D
    hcol hright hend htrace hstates
  refine ⟨D.paths.firstStart,D.first_in,D.paths.first.getVert D.cropIndex,?_,p.reachable⟩
  simpa only [hcol,hend] using D.first_contact.2.1

end
end PottsContinuity.Push
