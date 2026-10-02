import JSP896.OddComponentsSwitching
import JSP896.OddComponentsCounting

/-!
# A terminal dominator block has one missing dominating endpoint

The two switches force an acyclic transition relation.  Its terminal
root-dominator block lies in an original rooted subtree.  Both possible
colours of distinguished neighbour stay in that block, while its first black
endpoint cannot be a neighbour.  This proves the literal 2|L|−1 domination
bound used by Fact 3, without assuming a certificate exists.
-/

namespace JSP896.OddComponents

open MatchingConfiguration FiniteTransversal Directed

attribute [local instance] Classical.propDecidable

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
variable {G : SimpleGraph V} {label : V → ι} {I : Finset V}
    {M : Tree G label I Finset.univ} {root : ι}

theorem dominates_parent_descendant
    (O : RootOrientation M root) (B : BipartiteModel M)
    {c x : ι} (h : Dominates (Arc O B) root c x) : Reach O.Parent c x := by
  rcases reach_avoid_or_suffix (O.parent_reachable x) c with hav | hdesc
  · apply False.elim
    apply h
    apply hav.mono
    intro a b hab
    rw [← hab.2]
    exact parent_arc O B hab.1
  · exact hdesc

/-- The finite obstruction extracted from the two switches.  The only size
input is a bound on genuine descendants in the original rooted class tree. -/
theorem exists_terminal_dominating_set
    (O : RootOrientation M root) (B : BipartiteModel M)
    (hno : ¬ HasFull G label) (hne : ∃ x, x ≠ root) (t : ℕ)
    (hsize : ∀ c, c ≠ root →
      (Finset.univ.filter (fun x => Reach O.Parent c x)).card ≤ t) :
    ∃ (L : Finset ι) (D : Finset V), L.Nonempty ∧ L.card ≤ t ∧
      D.card < 2 * L.card ∧
      (∀ v : V, label v ∈ L → ∃ w ∈ D, G.Adj v w) := by
  classical
  have hroot := root_arc_reachable O B
  have hanti := arc_reach_antisymm O B hno hroot
  obtain ⟨c, hc, hout, hdom⟩ := exists_terminal_block hroot hanti hne
  let L := Finset.univ.filter (Dominates (Arc O B) root c)
  have hLmem (x : ι) : x ∈ L ↔ Dominates (Arc O B) root c x := by simp [L]
  have hcL : c ∈ L := (hLmem c).mpr (dominates_self _ _ _)
  have hLne : L.Nonempty := ⟨c, hcL⟩
  have hLroot : root ∉ L := by
    intro h
    exact not_dominates_root hc.1 ((hLmem root).mp h)
  have hLsmall : L.card ≤ t := by
    apply (Finset.card_le_card (show L ⊆
      Finset.univ.filter (fun x => Reach O.Parent c x) from ?_)).trans (hsize c hc.1)
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      dominates_parent_descendant O B ((hLmem x).mp hx)⟩
  let E := L.image (fun d => (O.black d).1) ∪ L.image (fun d => (O.white d).1)
  let D := E.erase (O.black c).1
  have hcE : (O.black c).1 ∈ E :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c, hcL, rfl⟩)
  have hEcard : E.card ≤ 2 * L.card := by
    calc
      E.card ≤ (L.image (fun d => (O.black d).1)).card +
          (L.image (fun d => (O.white d).1)).card := Finset.card_union_le _ _
      _ ≤ L.card + L.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ = 2 * L.card := by omega
  have hDcard : D.card < 2 * L.card := by
    have hEpos : 0 < E.card := Finset.card_pos.mpr ⟨_, hcE⟩
    have hD : D.card = E.card - 1 := Finset.card_erase_of_mem hcE
    omega
  refine ⟨L, D, hLne, hLsmall, hDcard, ?_⟩
  intro v hvL
  have hcv : Dominates (Arc O B) root c (label v) := (hLmem _).mp hvL
  obtain ⟨d, hd, hi⟩ := O.cover (B.index v)
  have hindexD : (B.index v).1 ∈ D := by
    rcases hi with hi | hi
    · have harc : Arc O B (label v) d := ⟨hd, v, rfl, hi⟩
      have hdL : d ∈ L := (hLmem d).mpr (hout _ _ hcv harc)
      have hdc : d ≠ c := by
        intro heq
        subst d
        exact hno (cycle_switch O B (hroot (label v)) harc (hcv.reach (hroot _)))
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        have hbc : O.black d = O.black c := Subtype.ext (by simpa only [hi] using heq)
        exact hdc (O.black_injective hd hc.1 hbc)
      · rw [hi]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d, hdL, rfl⟩)
    · have hi' : B.index v = O.white d := hi
      have hdv := white_index_dominates O B hno hd v hi'
      have hdL : d ∈ L := (hLmem d).mpr (hdom _ _ hcv hd hdv)
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        have hwb : O.white d = O.black c := Subtype.ext (by simpa only [hi'] using heq)
        exact O.black_ne_white hc.1 hd hwb.symm
      · rw [hi']
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, hdL, rfl⟩)
  exact ⟨(B.index v).1, hindexD, (B.uniqueNeighbour v (B.index v)).mpr rfl⟩

/-- The numerical contradiction once the centroid supplies its descendant
bound.  Both alternating switches and the dominating set are constructed. -/
theorem hasFull_of_centroid_orientation
    {t n d : ℕ} (ht : 0 < t) (hn : 0 < n)
    (G : SimpleGraph (Vertex (2 * t + 1) n))
    {I : Finset (Vertex (2 * t + 1) n)}
    (M : Tree G Prod.fst I Finset.univ) (B : BipartiteModel M)
    (root : Fin (2 * t + 1)) (O : RootOrientation M root)
    (hdegree : ∀ v, degree G v ≤ d)
    (hthreshold : (2 * t - 1) * d < t * n)
    (hsize : ∀ c, c ≠ root →
      (Finset.univ.filter (fun x => Reach O.Parent c x)).card ≤ t) :
    HasFull G Prod.fst := by
  classical
  by_contra hno
  have hCcard : (Finset.univ.erase root).card = 2 * t := by simp
  have hCpos : 0 < (Finset.univ.erase root).card := by rw [hCcard]; omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hCpos
  have hne : ∃ x, x ≠ root := ⟨c, (Finset.mem_erase.mp hc).1⟩
  obtain ⟨L, D, hL, hLt, hD, hdom⟩ :=
    exists_terminal_dominating_set O B hno hne t hsize
  obtain ⟨v, hvL, havoid⟩ := exists_undominated_in_small_classes
    ht hn hthreshold G hdegree L hL hLt D hD
  obtain ⟨w, hw, hvw⟩ := hdom v hvL
  exact havoid w hw hvw

end JSP896.OddComponents
