import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Lattice.Fold

/-! Adding genuine new leaf classes preserves the class-tree invariant.
Parallel-edge faithfulness in the original vertex graph remains a separate
invariant; this module concerns only the simple class graph. -/

namespace JSP896.ClassTreeGrowth

variable {ι : Type*} [DecidableEq ι]

structure TreeOn (G : SimpleGraph ι) (S : Finset ι) : Prop where
  acyclic : G.IsAcyclic
  supported : ∀ ⦃i j⦄, G.Adj i j → i ∈ S ∧ j ∈ S
  connected : ∀ i ∈ S, ∀ j ∈ S, G.Reachable i j

theorem singleton_tree (a : ι) : TreeOn (⊥ : SimpleGraph ι) {a} := by
  refine ⟨SimpleGraph.isAcyclic_bot, ?_, ?_⟩
  · intro i j h
    exact False.elim h
  · intro i hi j hj
    have hi' : i = a := Finset.mem_singleton.mp hi
    have hj' : j = a := Finset.mem_singleton.mp hj
    subst i
    subst j
    exact SimpleGraph.Reachable.rfl

theorem TreeOn.add_leaf {G : SimpleGraph ι} {S : Finset ι}
    (hT : TreeOn G S) (a b : ι) (ha : a ∈ S) (hb : b ∉ S) :
    TreeOn (G ⊔ SimpleGraph.edge a b) (insert b S) := by
  have hab : a ≠ b := by
    intro h
    exact hb (h ▸ ha)
  have hzero : G.neighborSet b = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hb (hT.supported hv).1
  have hnr : ¬ G.Reachable a b :=
    SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hab hzero
  refine ⟨SimpleGraph.IsAcyclic.sup_edge_of_not_reachable hnr hT.acyclic, ?_, ?_⟩
  · intro i j h
    rcases (SimpleGraph.sup_adj _ _ _ _).mp h with h | h
    · exact ⟨Finset.mem_insert_of_mem (hT.supported h).1,
        Finset.mem_insert_of_mem (hT.supported h).2⟩
    · rcases (SimpleGraph.edge_adj a b i j).mp h with ⟨h | h, _⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_self _ _⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ha⟩
  · have hedge : (G ⊔ SimpleGraph.edge a b).Adj a b := by
      apply (SimpleGraph.sup_adj _ _ _ _).mpr
      right
      exact (SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, hab⟩
    have hroot : ∀ i ∈ insert b S, (G ⊔ SimpleGraph.edge a b).Reachable i a := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hedge.symm.reachable
      · exact (hT.connected i hi a ha).mono le_sup_left
    intro i hi j hj
    exact (hroot i hi).trans (hroot j hj).symm

def attachStar (G : SimpleGraph ι) (a : ι) (L : Finset ι) : SimpleGraph ι :=
  G ⊔ L.sup (fun b => SimpleGraph.edge a b)

@[simp] theorem attachStar_empty (G : SimpleGraph ι) (a : ι) :
    attachStar G a ∅ = G := by
  simp [attachStar]

theorem attachStar_insert (G : SimpleGraph ι) (a b : ι) (L : Finset ι) :
    attachStar G a (insert b L) = attachStar G a L ⊔ SimpleGraph.edge a b := by
  simp only [attachStar, Finset.sup_insert]
  ac_rfl

theorem attachStar_adj (G : SimpleGraph ι) (a : ι) (L : Finset ι) (i j : ι) :
    (attachStar G a L).Adj i j ↔ G.Adj i j ∨
      (i = a ∧ j ∈ L ∧ i ≠ j) ∨ (j = a ∧ i ∈ L ∧ i ≠ j) := by
  induction L using Finset.induction_on with
  | empty => simp
  | @insert b L hb ih =>
    rw [attachStar_insert, SimpleGraph.sup_adj, ih, SimpleGraph.edge_adj]
    simp only [Finset.mem_insert]
    aesop

theorem TreeOn.attach_star {G : SimpleGraph ι} {S : Finset ι}
    (hT : TreeOn G S) (a : ι) (ha : a ∈ S) (L : Finset ι)
    (hdis : Disjoint S L) : TreeOn (attachStar G a L) (S ∪ L) := by
  induction L using Finset.induction_on with
  | empty => simpa using hT
  | @insert b L hb ih =>
    have hbS : b ∉ S := by
      intro h
      exact (Finset.disjoint_left.mp hdis) h (Finset.mem_insert_self _ _)
    have hdisL : Disjoint S L := hdis.mono_right (Finset.subset_insert _ _)
    have hbase := ih hdisL
    have hbnew : b ∉ S ∪ L := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hbS, hb⟩
    have hresult := hbase.add_leaf a b (Finset.mem_union_left _ ha) hbnew
    rw [attachStar_insert]
    simpa only [Finset.union_insert] using hresult

end JSP896.ClassTreeGrowth
