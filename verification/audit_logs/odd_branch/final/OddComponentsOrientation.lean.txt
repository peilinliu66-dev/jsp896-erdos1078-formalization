import JSP896.MatchingFacts
import JSP896.MatchingOrientationCentroid
import JSP896.OddComponentsReachability

/-! A total choice of black endpoints, constructed from distance to the root.
The value at the root is a harmless duplicate and is never counted. -/

namespace JSP896.MatchingConfiguration

open FiniteTransversal

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

structure RootOrientation {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} (M : Tree G label I Finset.univ) (root : ι) where
  black : ι → IVertex I
  color : ∀ c, c ≠ root → label (black c).1 = c
  downhill : ∀ c, c ≠ root →
    (FeasiblePair.classGraph G label I).dist (label (M.partner (black c)).1) root <
      (FeasiblePair.classGraph G label I).dist c root
  independent : ∀ c, c ≠ root → ∀ d, d ≠ root →
    ¬ G.Adj (black c).1 (black d).1
  cover : ∀ i : IVertex I, ∃ c, c ≠ root ∧
    (i = black c ∨ i = M.partner (black c))

theorem Tree.exists_rootOrientation {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} (M : Tree G label I Finset.univ) (root : ι)
    (hne : ∃ c, c ≠ root) : Nonempty (RootOrientation M root) := by
  classical
  letI : Nonempty ι := ⟨root⟩
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨v₀, hv₀, hd₀⟩ := M.exists_downhill_vertex
    (Finset.mem_univ root) (Finset.mem_univ c₀) hc₀
  have hex : ∀ c, ∃ v : IVertex I, c ≠ root →
      label v.1 = c ∧
      (FeasiblePair.classGraph G label I).dist (label (M.partner v).1) root <
        (FeasiblePair.classGraph G label I).dist c root := by
    intro c
    by_cases hc : c = root
    · exact ⟨v₀, fun h => (h hc).elim⟩
    · obtain ⟨v, hv, hd⟩ := M.exists_downhill_vertex
        (Finset.mem_univ root) (Finset.mem_univ c) hc
      exact ⟨v, fun _ => ⟨hv, hd⟩⟩
  let b : ι → IVertex I := fun c => Classical.choose (hex c)
  have hb (c) (hc : c ≠ root) := Classical.choose_spec (hex c) hc
  have hind : ∀ c, c ≠ root → ∀ d, d ≠ root → ¬ G.Adj (b c).1 (b d).1 := by
    intro c hc d hd hadj
    have hp : M.partner (b c) = b d := (M.adj_iff_partner _ _).mp hadj
    have hp' : M.partner (b d) = b c := by rw [← hp, M.partner_involutive]
    have hc' := (hb c hc).2
    have hd' := (hb d hd).2
    rw [hp, (hb d hd).1] at hc'
    rw [hp', (hb c hc).1] at hd'
    omega
  let C : Finset ι := Finset.univ.erase root
  let T : Finset V := C.image (fun c => (b c).1)
  let W : Finset V := C.image (fun c => (M.partner (b c)).1)
  have hTcard : T.card = C.card := by
    apply Finset.card_image_iff.mpr
    intro c hc d hd h
    have hc' := (Finset.mem_erase.mp hc).1
    have hd' := (Finset.mem_erase.mp hd).1
    exact (hb c hc').1.symm.trans ((congrArg label h).trans (hb d hd').1)
  have hWcard : W.card = C.card := by
    apply Finset.card_image_iff.mpr
    intro c hc d hd h
    have hp : M.partner (b c) = M.partner (b d) := Subtype.ext h
    have heq : b c = b d := by
      have h' := congrArg M.partner hp
      simpa only [M.partner_involutive] using h'
    exact (hb c (Finset.mem_erase.mp hc).1).1.symm.trans
      ((congrArg (fun i : IVertex I => label i.1) heq).trans
        (hb d (Finset.mem_erase.mp hd).1).1)
  have hdisjoint : Disjoint T W := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hw
    have hadj := M.partner_adj (b d)
    rw [heq] at hadj
    exact hind d (Finset.mem_erase.mp hd).1 c (Finset.mem_erase.mp hc).1 hadj
  have hsub : T ∪ W ⊆ I := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hv; exact (b c).2
    · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hv; exact (M.partner (b c)).2
  have hCcard : C.card + 1 = Fintype.card ι := by
    simp only [C, Finset.card_erase_of_mem (Finset.mem_univ root), Finset.card_univ]
    have hpos := Fintype.card_pos_iff.mpr (show Nonempty ι from ⟨root⟩)
    omega
  have hfull : T ∪ W = I := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_union_of_disjoint hdisjoint, hTcard, hWcard]
    have hI := M.full_card
    omega
  refine ⟨⟨b, fun c hc => (hb c hc).1, fun c hc => (hb c hc).2, hind, ?_⟩⟩
  intro i
  have hi : i.1 ∈ T ∪ W := hfull.symm ▸ i.2
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨c, hc, hci⟩ := Finset.mem_image.mp hi
    exact ⟨c, (Finset.mem_erase.mp hc).1, Or.inl (Subtype.ext hci.symm)⟩
  · obtain ⟨c, hc, hci⟩ := Finset.mem_image.mp hi
    exact ⟨c, (Finset.mem_erase.mp hc).1, Or.inr (Subtype.ext hci.symm)⟩

namespace RootOrientation

variable {G : SimpleGraph V} {label : V → ι} {I : Finset V}
    {M : Tree G label I Finset.univ} {root : ι} (O : RootOrientation M root)

noncomputable def white (c : ι) : IVertex I := M.partner (O.black c)

theorem black_ne_white {c d : ι} (hc : c ≠ root) (hd : d ≠ root) :
    O.black c ≠ O.white d := by
  intro h
  have hadj := M.partner_adj (O.black d)
  change G.Adj (O.black d).1 (O.white d).1 at hadj
  rw [← h] at hadj
  exact O.independent d hd c hc hadj

theorem black_injective {c d : ι} (hc : c ≠ root) (hd : d ≠ root)
    (h : O.black c = O.black d) : c = d :=
  (O.color c hc).symm.trans
    ((congrArg (fun i : IVertex I => label i.1) h).trans (O.color d hd))

theorem white_injective {c d : ι} (hc : c ≠ root) (hd : d ≠ root)
    (h : O.white c = O.white d) : c = d := by
  apply O.black_injective hc hd
  have h' := congrArg M.partner h
  simpa only [white, M.partner_involutive] using h'

theorem partner_white (c : ι) : M.partner (O.white c) = O.black c :=
  M.partner_involutive _

/-- The oriented class-tree edge from a parent class to its child. -/
def Parent (a b : ι) : Prop := b ≠ root ∧ label (O.white b).1 = a

theorem parent_reachable (c : ι) :
    OddComponents.Directed.Reach O.Parent root c := by
  let K := FeasiblePair.classGraph G label I
  have haux : ∀ k, ∀ c : ι, K.dist c root = k →
      OddComponents.Directed.Reach O.Parent root c := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro c hck
      by_cases hc : c = root
      · subst c; exact .refl root
      · let p := label (O.white c).1
        have hp : K.dist p root < k := by
          rw [← hck]
          exact O.downhill c hc
        exact (ih (K.dist p root) hp p rfl).trans
          (.single (show O.Parent p c from ⟨hc, rfl⟩))
  exact haux (K.dist c root) c rfl

end RootOrientation

/-- Selecting one vertex per class from an independent covering set produces
an actual full transversal.  The switch lemmas may therefore keep duplicates
of a class in their intermediate finite sets. -/
theorem hasFull_of_independent_cover {G : SimpleGraph V} {label : V → ι}
    (U : Finset V) (hind : ∀ v ∈ U, ∀ w ∈ U, ¬ G.Adj v w)
    (hcover : ∀ c, ∃ v ∈ U, label v = c) : HasFull G label := by
  classical
  let f : ι → V := fun c => Classical.choose (hcover c)
  have hf (c) : f c ∈ U ∧ label (f c) = c := Classical.choose_spec (hcover c)
  refine ⟨Finset.univ.image f, ⟨?_, ?_⟩, ?_⟩
  · intro v hv w hw
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hw
    exact hind _ (hf c).1 _ (hf d).1
  · intro v hv w hw h
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hw
    have hcd : c = d := (hf c).2.symm.trans (h.trans (hf d).2)
    rw [hcd]
  · apply Finset.eq_univ_of_forall
    intro c
    exact Finset.mem_image.mpr ⟨f c,
      Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, (hf c).2⟩

end JSP896.MatchingConfiguration
