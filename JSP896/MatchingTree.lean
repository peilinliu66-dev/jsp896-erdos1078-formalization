import JSP896.FeasiblePair

/-! Stable literal interface for induced matching configurations and the
disjoint-bipartite-component switching argument. -/

namespace JSP896.MatchingConfiguration

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]

abbrev IVertex (I : Finset V) := {v // v ∈ I}

/-- A perfect induced matching whose faithful class graph is a tree on S.
The singleton-class/empty-matching case is allowed for tree-cut arguments. -/
structure Tree (G : SimpleGraph V) (label : V → ι) (I : Finset V) (S : Finset ι) : Prop where
  partite : ∀ ⦃v w⦄, G.Adj v w → label v ≠ label w
  within : ∀ v ∈ I, label v ∈ S
  matched : ∀ v ∈ I, ∃! w, w ∈ I ∧ G.Adj v w
  acyclic : (FeasiblePair.classGraph G label I).IsAcyclic
  connected : ∀ i ∈ S, ∀ j ∈ S, (FeasiblePair.classGraph G label I).Reachable i j
  faithful : PairedDeficit.FaithfulClassEdges G I label

noncomputable def Tree.partner {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S) (v : IVertex I) : IVertex I :=
  ⟨Classical.choose (M.matched v.1 v.2), (Classical.choose_spec (M.matched v.1 v.2)).1.1⟩

theorem Tree.partner_adj {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S) (v : IVertex I) :
    G.Adj v.1 (M.partner v).1 :=
  (Classical.choose_spec (M.matched v.1 v.2)).1.2

theorem Tree.partner_unique {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S) (v : IVertex I)
    {w : V} (hw : w ∈ I) (hvw : G.Adj v.1 w) : w = (M.partner v).1 :=
  (Classical.choose_spec (M.matched v.1 v.2)).2 w ⟨hw, hvw⟩

theorem Tree.partner_involutive {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S) (v : IVertex I) :
    M.partner (M.partner v) = v := by
  apply Subtype.ext
  exact (M.partner_unique (M.partner v) v.2 (G.adj_symm (M.partner_adj v))).symm

theorem Tree.partner_ne {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S) (v : IVertex I) :
    M.partner v ≠ v := by
  intro h
  have hadj := M.partner_adj v
  rw [h] at hadj
  exact G.loopless.irrefl v.1 hadj

noncomputable def Tree.pairing {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S) :
    PairedDeficit.Pairing (IVertex I) where
  partner := ⟨M.partner, M.partner, M.partner_involutive, M.partner_involutive⟩
  involutive := M.partner_involutive
  fixedPointFree := M.partner_ne

theorem Tree.adj_iff_partner {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S) (v w : IVertex I) :
    G.Adj v.1 w.1 ↔ M.partner v = w := by
  constructor
  · intro h
    apply Subtype.ext
    exact (M.partner_unique v w.2 h).symm
  · intro h
    simpa only [h] using M.partner_adj v

/-- A literal disjoint complete-bipartite component representation, indexed
by the unique distinguished matching neighbour of every graph vertex.
The structure theorem must construct all three fields from the host graph. -/
structure BipartiteModel {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} (M : Tree G label I S) where
  index : V → IVertex I
  uniqueNeighbour : ∀ v (i : IVertex I), G.Adj v i.1 ↔ i = index v
  edge_iff : ∀ v w, G.Adj v w ↔ M.partner (index v) = index w

theorem BipartiteModel.index_on_matching {G : SimpleGraph V} {label : V → ι}
    {I : Finset V} {S : Finset ι} {M : Tree G label I S}
    (B : BipartiteModel M) (v : IVertex I) : B.index v.1 = M.partner v := by
  exact ((B.uniqueNeighbour v.1 (M.partner v)).mp (M.partner_adj v)).symm

end JSP896.MatchingConfiguration
