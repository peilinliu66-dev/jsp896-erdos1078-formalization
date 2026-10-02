import JSP896.FeasiblePair

/-! Local switching lemmas for extending an actual feasible pair. -/

namespace JSP896.FeasiblePair

open FiniteTransversal

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

theorem leaves_swap_of_nonadjacent (G : SimpleGraph V) (T : Finset V)
    (u x z : V) (hzx : ¬ G.Adj z x) :
    leaves G (insert x (T.erase u)) z = (leaves G T z).erase u := by
  classical
  ext y
  simp only [mem_leaves, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨hy, hzy⟩
    rcases hy with rfl | hy
    · exact False.elim (hzx hzy)
    · exact ⟨hy.1, hy.2, hzy⟩
  · rintro ⟨hyu, hyT, hzy⟩
    exact ⟨Or.inr ⟨hyu, hyT⟩, hzy⟩

theorem star_swap_of_nonadjacent (G : SimpleGraph V) (T : Finset V)
    (u x z : V) (huz : u ≠ z) (hzx : ¬ G.Adj z x) :
    star G (insert x (T.erase u)) z = (star G T z).erase u := by
  classical
  rw [star, leaves_swap_of_nonadjacent G T u x z hzx]
  ext y
  simp only [star, Finset.mem_insert, Finset.mem_erase]
  aesop

theorem active_T_vertex_mem_I {G : SimpleGraph V} {label : V → ι}
    {I T : Finset V} (hF : Feasible G label I T) {v : V} (hv : v ∈ T)
    (hactive : label v ∈ I.image label) : v ∈ I := by
  have hcolor : label v ∈ (I ∩ T).image label := by
    rw [hF.agreement]
    exact Finset.mem_inter.mpr ⟨hactive, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  obtain ⟨u, hu, hlabel⟩ := Finset.mem_image.mp hcolor
  have huv : u = v := hF.maximum.1.2 u (Finset.mem_inter.mp hu).2 v hv hlabel
  exact huv ▸ (Finset.mem_inter.mp hu).1

/-- A newly selected undominated centre has a genuine leaf. This is the
nontrivial local-switching step, not an assumed augmenting-path oracle. -/
theorem undominated_extension_has_leaf {G : SimpleGraph V} {label : V → ι}
    {I T U : Finset V} (hF : Feasible G label I T) (hU : Compatible G label I T U)
    (w : V) (havoid : ∀ v ∈ I, ¬ G.Adj w v)
    (hclass : label w ∈ I.image label ∨ label w ∉ T.image label) :
    ∃ u ∈ U, G.Adj w u := by
  classical
  by_contra hno
  have hwU : ∀ u ∈ U, ¬ G.Adj w u := by
    intro u hu hwu
    exact hno ⟨u, hu, hwu⟩
  by_cases hcolor : label w ∈ T.image label
  · have hactive : label w ∈ I.image label := hclass.resolve_right (not_not.mpr hcolor)
    obtain ⟨u, huT, hulabel⟩ := Finset.mem_image.mp hcolor
    have huactive : label u ∈ I.image label := by
      rw [hulabel]
      exact hactive
    have huI := active_T_vertex_mem_I hF huT huactive
    have huU := active_T_vertex_mem_compatible hF hU huT huactive
    obtain ⟨z₀, hz₀, huniq⟩ := hF.leavesUnique u (Finset.mem_inter.mpr ⟨huI, huT⟩)
    let U' := insert w (U.erase u)
    have hnew : Partial G label U' := partial_swap hU.partial huU hulabel.symm
      (fun v hv => hwU v (Finset.mem_erase.mp hv).2)
    have hcolors : U'.image label = T.image label :=
      (swap_colors huU hulabel.symm).trans hU.colors
    have hwI : w ∉ I := hF.undominated_not_mem havoid
    have hdis : Disjoint U' (I \ T) := by
      apply Finset.disjoint_left.mpr
      intro v hv hvC
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hwI (Finset.mem_sdiff.mp hvC).1
      · exact (Finset.disjoint_left.mp hU.avoidsCenters)
          (Finset.mem_erase.mp hv).2 hvC
    have huz (z : V) (hz : z ∈ I \ T) : u ≠ z := by
      intro h
      exact (Finset.mem_sdiff.mp hz).2 (h ▸ huT)
    have hzw (z : V) (hz : z ∈ I \ T) : ¬ G.Adj z w := by
      intro h
      exact havoid z (Finset.mem_sdiff.mp hz).1 (G.adj_symm h)
    have hsame : ∀ z ∈ I \ T, z ≠ z₀ → star G U' z = star G T z := by
      intro z hz hne
      have hzu : ¬ G.Adj z u := by
        intro h
        exact hne (huniq z ⟨hz, h⟩)
      have hunot : u ∉ star G U z := by
        simp only [mem_star]
        exact not_or_intro (huz z hz) (fun h => hzu h.2)
      rw [show U' = insert w (U.erase u) from rfl,
        star_swap_of_nonadjacent G U u w z (huz z hz) (hzw z hz),
        Finset.erase_eq_of_notMem hunot, hU.stars z hz]
    have hminimal := hF.locallyMinimal z₀ hz₀.1 U' hnew hcolors hdis hsame
    have hmem : u ∈ star G U z₀ := (mem_star G U z₀ u).mpr (Or.inr ⟨huU, hz₀.2⟩)
    have hsmall : (star G U' z₀).card < (star G U z₀).card := by
      rw [show U' = insert w (U.erase u) from rfl,
        star_swap_of_nonadjacent G U u w z₀ (huz z₀ hz₀.1) (hzw z₀ hz₀.1),
        Finset.card_erase_of_mem hmem]
      have hpos := Finset.card_pos.mpr ⟨u, hmem⟩
      omega
    rw [hU.stars z₀ hz₀.1] at hsmall
    omega
  · have hmissing : label w ∉ U.image label := by rwa [hU.colors]
    obtain ⟨u, hu, hwu⟩ := (Compatible.maximum hF hU).missing_vertex_has_neighbour w hmissing
    exact hwU u hu hwu

end JSP896.FeasiblePair
