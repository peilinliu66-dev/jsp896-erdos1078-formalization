import JSP896.FeasibleGrowth

/-! Exact support, freshness and separation facts for a new feasible star. -/

namespace JSP896.FeasiblePair

open FiniteTransversal

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

theorem Feasible.star_subset {G : SimpleGraph V} {label : V → ι} {I T : Finset V}
    (hF : Feasible G label I T) {z : V} (hz : z ∈ I \ T) : star G T z ⊆ I := by
  intro v hv
  rcases (mem_star G T z v).mp hv with rfl | hv
  · exact (Finset.mem_sdiff.mp hz).1
  · exact hF.centersSaturated z hz v hv.1 hv.2

theorem compatible_inter_eq {G : SimpleGraph V} {label : V → ι}
    {I T U : Finset V} (hF : Feasible G label I T) (hU : Compatible G label I T U) :
    I ∩ U = I ∩ T := by
  ext v
  constructor
  · intro hv
    have h := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr ⟨h.1,
      compatible_vertex_on_active_mem_T hF hU h.2
        (Finset.mem_image.mpr ⟨v, h.1, rfl⟩)⟩
  · intro hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
      leaf_mem_of_compatible hF hU hv⟩

theorem compatible_center_neighbors_mem_I {G : SimpleGraph V} {label : V → ι}
    {I T U : Finset V} (hF : Feasible G label I T) (hU : Compatible G label I T U)
    {z v : V} (hz : z ∈ I \ T) (hv : v ∈ U) (hzv : G.Adj z v) : v ∈ I := by
  have hmem : v ∈ star G U z := (mem_star G U z v).mpr (Or.inr ⟨hv, hzv⟩)
  rw [hU.stars z hz] at hmem
  exact hF.star_subset hz hmem

theorem new_center_not_mem_compatible {G : SimpleGraph V} {label : V → ι}
    {I T U : Finset V} (hF : Feasible G label I T) (hU : Compatible G label I T U)
    (w : V) (havoid : ∀ v ∈ I, ¬ G.Adj w v)
    (hclass : label w ∈ I.image label ∨ label w ∉ T.image label) : w ∉ U := by
  intro hw
  rcases hclass with ha | hm
  · have hwT := compatible_vertex_on_active_mem_T hF hU hw ha
    exact hF.undominated_not_mem havoid (active_T_vertex_mem_I hF hwT ha)
  · apply hm
    rw [← hU.colors]
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

theorem new_leaf_inactive {G : SimpleGraph V} {label : V → ι}
    {I T U : Finset V} (hF : Feasible G label I T) (hU : Compatible G label I T U)
    (w : V) (havoid : ∀ v ∈ I, ¬ G.Adj w v)
    {v : V} (hv : v ∈ leaves G U w) : label v ∉ I.image label := by
  intro ha
  have hleaf := (mem_leaves G U w v).mp hv
  have hvT := compatible_vertex_on_active_mem_T hF hU hleaf.1 ha
  have hvI := active_T_vertex_mem_I hF hvT ha
  exact havoid v hvI hleaf.2

theorem new_star_disjoint {G : SimpleGraph V} {label : V → ι}
    {I T U : Finset V} (hF : Feasible G label I T)
    (w : V) (havoid : ∀ v ∈ I, ¬ G.Adj w v) : Disjoint I (star G U w) := by
  apply Finset.disjoint_left.mpr
  intro v hvI hvStar
  rcases (mem_star G U w v).mp hvStar with rfl | hv
  · exact hF.undominated_not_mem havoid hvI
  · exact havoid v hvI hv.2

theorem old_avoids_new_star {G : SimpleGraph V} {label : V → ι}
    {I T U : Finset V} (hF : Feasible G label I T) (hU : Compatible G label I T U)
    (w : V) (havoid : ∀ v ∈ I, ¬ G.Adj w v)
    {v x : V} (hv : v ∈ I) (hx : x ∈ star G U w) : ¬ G.Adj v x := by
  intro hvx
  rcases (mem_star G U w x).mp hx with rfl | hx'
  · exact havoid v hv (G.adj_symm hvx)
  · by_cases hvT : v ∈ T
    · have hvU := active_T_vertex_mem_compatible hF hU hvT
        (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      exact hU.partial.1 v hvU x hx'.1 hvx
    · have hxI := compatible_center_neighbors_mem_I hF hU
        (Finset.mem_sdiff.mpr ⟨hv, hvT⟩) hx'.1 hvx
      exact (Finset.disjoint_left.mp (new_star_disjoint hF w havoid)) hxI hx

theorem extended_centers {G : SimpleGraph V} {label : V → ι}
    {I T U : Finset V} (hF : Feasible G label I T) (hU : Compatible G label I T U)
    (w : V) (havoid : ∀ v ∈ I, ¬ G.Adj w v)
    (hclass : label w ∈ I.image label ∨ label w ∉ T.image label) :
    (I ∪ star G U w) \ U = insert w (I \ T) := by
  have hwU := new_center_not_mem_compatible hF hU w havoid hclass
  ext v
  constructor
  · intro hv
    rcases Finset.mem_sdiff.mp hv with ⟨hv, hvU⟩
    rcases Finset.mem_union.mp hv with hvI | hvStar
    · apply Finset.mem_insert_of_mem
      refine Finset.mem_sdiff.mpr ⟨hvI, ?_⟩
      intro hvT
      exact hvU (active_T_vertex_mem_compatible hF hU hvT
        (Finset.mem_image.mpr ⟨v, hvI, rfl⟩))
    · rcases (mem_star G U w v).mp hvStar with rfl | hvLeaf
      · exact Finset.mem_insert_self _ _
      · exact False.elim (hvU hvLeaf.1)
  · intro hv
    rcases Finset.mem_insert.mp hv with hvw | hvC
    · subst v
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _
        ((mem_star G U w w).mpr (Or.inl rfl)), hwU⟩
    · have hvI := (Finset.mem_sdiff.mp hvC).1
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hvI, ?_⟩
      intro hvU
      exact (Finset.mem_sdiff.mp hvC).2
        (compatible_vertex_on_active_mem_T hF hU hvU
          (Finset.mem_image.mpr ⟨v, hvI, rfl⟩))

end JSP896.FeasiblePair
