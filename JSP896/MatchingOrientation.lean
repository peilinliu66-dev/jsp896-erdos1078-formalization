import JSP896.MatchingTree
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

/-!
# Root-oriented partial transversals in an induced matching configuration

For every non-root class choose an endpoint of a class edge going strictly
downhill in distance to the root.  Two chosen endpoints cannot be partners:
that would make both of their distances strictly smaller than the other.
This constructs the requested partial transversal directly from the actual
matching and connected class graph.  No orientation-existence premise is
introduced.  Pinned execution records are in VERIFICATION.md.
-/

namespace JSP896.MatchingConfiguration

open FiniteTransversal

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

theorem exists_downhill_neighbor (K : SimpleGraph ι) {c root : ι}
    (hreach : K.Reachable c root) (hne : c ≠ root) :
    ∃ j, K.Adj c j ∧ K.dist j root < K.dist c root := by
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  obtain ⟨j, hj, tail, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne p
  have hdist := K.dist_le tail
  simp only [SimpleGraph.Walk.length_cons] at hp
  exact ⟨j, hj, by omega⟩

theorem Tree.exists_downhill_vertex {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S)
    {root c : ι} (hroot : root ∈ S) (hc : c ∈ S) (hne : c ≠ root) :
    ∃ v : IVertex I, label v.1 = c ∧
      (FeasiblePair.classGraph G label I).dist (label (M.partner v).1) root <
        (FeasiblePair.classGraph G label I).dist c root := by
  let K := FeasiblePair.classGraph G label I
  obtain ⟨j, hj, hdist⟩ := exists_downhill_neighbor K
    (M.connected c hc root hroot) hne
  obtain ⟨_hne, v, hv, w, hw, hadj, hvc, hwj⟩ := hj
  refine ⟨⟨v, hv⟩, hvc, ?_⟩
  have hpartner : w = (M.partner ⟨v, hv⟩).1 := M.partner_unique ⟨v, hv⟩ hw hadj
  rw [← hpartner, hwj]
  exact hdist

/-- Generic root-oriented partial transversal, contained in I and covering
exactly all classes of S except the chosen root. -/
theorem Tree.exists_rooted_partial {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S)
    (root : ι) (hroot : root ∈ S) :
    ∃ T : Finset V, T ⊆ I ∧ Partial G label T ∧ T.image label = S.erase root := by
  classical
  let C := {c // c ∈ S.erase root}
  have hex : ∀ c : C, ∃ v : IVertex I, label v.1 = c.1 ∧
      (FeasiblePair.classGraph G label I).dist (label (M.partner v).1) root <
        (FeasiblePair.classGraph G label I).dist c.1 root := by
    intro c
    have hc := Finset.mem_erase.mp c.2
    exact M.exists_downhill_vertex hroot hc.2 hc.1
  let choose : C → IVertex I := fun c => Classical.choose (hex c)
  have hchoose (c : C) : label (choose c).1 = c.1 ∧
      (FeasiblePair.classGraph G label I).dist (label (M.partner (choose c)).1) root <
        (FeasiblePair.classGraph G label I).dist c.1 root :=
    Classical.choose_spec (hex c)
  let T : Finset V := Finset.univ.image (fun c : C => (choose c).1)
  have hmem (v : V) : v ∈ T ↔ ∃ c : C, (choose c).1 = v := by
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and]
  have hTI : T ⊆ I := by
    intro v hv
    obtain ⟨c, rfl⟩ := (hmem v).mp hv
    exact (choose c).2
  have hpartial : Partial G label T := by
    constructor
    · intro v hv w hw hadj
      obtain ⟨c, rfl⟩ := (hmem v).mp hv
      obtain ⟨e, rfl⟩ := (hmem w).mp hw
      have hpartner : M.partner (choose c) = choose e :=
        (M.adj_iff_partner (choose c) (choose e)).mp hadj
      have hpartner' : M.partner (choose e) = choose c := by
        rw [← hpartner, M.partner_involutive]
      have hc := (hchoose c).2
      have he := (hchoose e).2
      rw [hpartner, (hchoose e).1] at hc
      rw [hpartner', (hchoose c).1] at he
      omega
    · intro v hv w hw hlabel
      obtain ⟨c, rfl⟩ := (hmem v).mp hv
      obtain ⟨e, rfl⟩ := (hmem w).mp hw
      have hce : c = e := by
        apply Subtype.ext
        exact (hchoose c).1.symm.trans (hlabel.trans (hchoose e).1)
      rw [hce]
  refine ⟨T, hTI, hpartial, ?_⟩
  ext c
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, hvc⟩
    obtain ⟨e, rfl⟩ := (hmem v).mp hv
    have hec : e.1 = c := (hchoose e).1.symm.trans hvc
    exact hec ▸ e.2
  · intro hc
    let e : C := ⟨c, hc⟩
    refine ⟨(choose e).1, (hmem _).mpr ⟨e, rfl⟩, ?_⟩
    exact (hchoose e).1

/-- The cardinality is part of the root-orientation conclusion, not an
additional requirement on a supplied partial transversal. -/
theorem Tree.exists_rooted_partial_card {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S)
    (root : ι) (hroot : root ∈ S) :
    ∃ T : Finset V, T ⊆ I ∧ Partial G label T ∧
      T.image label = S.erase root ∧ T.card + 1 = S.card := by
  obtain ⟨T, hTI, hT, hcolors⟩ := M.exists_rooted_partial root hroot
  refine ⟨T, hTI, hT, hcolors, ?_⟩
  have hcard := congrArg Finset.card hcolors
  rw [hT.card_image, Finset.card_erase_of_mem hroot] at hcard
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨root, hroot⟩
  omega

/-- An undominated vertex in the missing class completes the constructed
root-oriented transversal on a full class set. -/
theorem full_of_rooted_partial_and_undominated {G : SimpleGraph V} {label : V → ι}
    {T : Finset V} {root : ι} (hT : Partial G label T)
    (hcolors : T.image label = Finset.univ.erase root)
    (v : V) (hv : label v = root) (havoid : ∀ w ∈ T, ¬ G.Adj v w) :
    HasFull G label := by
  classical
  have hmissing : label v ∉ T.image label := by rw [hcolors, hv]; simp
  refine ⟨insert v T, partial_insert hT v hmissing havoid, ?_⟩
  rw [Finset.image_insert, hcolors, hv]
  exact Finset.insert_erase (Finset.mem_univ root)

/-- Exact domination formulation of Fact 2.  In the absence of a full
transversal, the unique distinguished neighbor of v belongs to every
I-contained partial transversal rooted at the class of v. -/
theorem BipartiteModel.index_mem_rooted_partial {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {M : Tree G label I Finset.univ} (B : BipartiteModel M)
    (hno : ¬ HasFull G label) {T : Finset V} (hTI : T ⊆ I)
    (hT : Partial G label T) (v : V)
    (hcolors : T.image label = Finset.univ.erase (label v)) : (B.index v).1 ∈ T := by
  by_contra hnot
  apply hno
  apply full_of_rooted_partial_and_undominated hT hcolors v rfl
  intro w hw hadj
  have hindex := (B.uniqueNeighbour v ⟨w, hTI hw⟩).mp hadj
  have hwIndex : w = (B.index v).1 := congrArg Subtype.val hindex
  exact hnot (hwIndex ▸ hw)

end JSP896.MatchingConfiguration
