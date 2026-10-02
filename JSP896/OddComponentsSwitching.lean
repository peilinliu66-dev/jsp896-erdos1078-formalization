import JSP896.OddComponentsOrientation

/-!
# The two finite alternating switches

An arc x → y means that class x has a vertex whose distinguished neighbour
is black y.  A finite root-containing set closed under such transitions gives
the all-white switch (the repeated-black case).  If all transitions except a
last class stay in a set avoiding c, a last vertex with white neighbour c gives
the terminal switch.  The sets are finite backward reachability sets, so no
unproved sequence-existence or termination premise is needed.
-/

namespace JSP896.OddComponents

open MatchingConfiguration FiniteTransversal Directed

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
variable {G : SimpleGraph V} {label : V → ι} {I : Finset V}
    {M : Tree G label I Finset.univ} {root : ι}

def Arc (O : RootOrientation M root) (B : BipartiteModel M) (x y : ι) : Prop :=
  y ≠ root ∧ ∃ v : V, label v = x ∧ B.index v = O.black y

theorem parent_arc (O : RootOrientation M root) (B : BipartiteModel M)
    {c : ι} (hc : c ≠ root) : Arc O B (label (O.white c).1) c := by
  refine ⟨hc, (O.white c).1, rfl, ?_⟩
  rw [B.index_on_matching, O.partner_white]

theorem root_arc_reachable (O : RootOrientation M root) (B : BipartiteModel M)
    (c : ι) : Reach (Arc O B) root c := by
  apply (O.parent_reachable c).mono
  intro a b hab
  rw [← hab.2]
  exact parent_arc O B hab.1

noncomputable def switchSet (O : RootOrientation M root) (B : BipartiteModel M)
    (S : Finset ι) : Finset V := by
  classical
  exact Finset.univ.filter (fun v =>
    (∃ c ∈ S, c ≠ root ∧ B.index v = O.black c) ∨
    (∃ c, c ∉ S ∧ c ≠ root ∧ v = (O.black c).1))

@[simp] theorem mem_switchSet (O : RootOrientation M root) (B : BipartiteModel M)
    (S : Finset ι) (v : V) : v ∈ switchSet O B S ↔
      (∃ c ∈ S, c ≠ root ∧ B.index v = O.black c) ∨
      (∃ c, c ∉ S ∧ c ≠ root ∧ v = (O.black c).1) := by
  classical
  simp [switchSet]

theorem switchSet_independent (O : RootOrientation M root) (B : BipartiteModel M)
    (S : Finset ι) :
    ∀ v ∈ switchSet O B S, ∀ w ∈ switchSet O B S, ¬ G.Adj v w := by
  intro v hv w hw hadj
  have he := (B.edge_iff v w).mp hadj
  rcases (mem_switchSet O B S v).mp hv with ⟨c, hcS, hc, hv⟩ | ⟨c, hcS, hc, rfl⟩ <;>
    rcases (mem_switchSet O B S w).mp hw with ⟨d, hdS, hd, hw⟩ | ⟨d, hdS, hd, rfl⟩
  · rw [hv, hw] at he
    exact O.black_ne_white hd hc he.symm
  · rw [hv, B.index_on_matching] at he
    have hcd : c = d := O.white_injective hc hd he
    exact hdS (hcd ▸ hcS)
  · rw [B.index_on_matching, M.partner_involutive, hw] at he
    have hcd := O.black_injective hc hd he
    exact hcS (hcd.symm ▸ hdS)
  · exact O.independent c hc d hd hadj

theorem arc_representative_mem_switchSet
    (O : RootOrientation M root) (B : BipartiteModel M) (S : Finset ι)
    {x y : ι} (hxy : Arc O B x y) (hy : y ∈ S) :
    ∃ v ∈ switchSet O B S, label v = x := by
  obtain ⟨hyroot, v, hvx, hv⟩ := hxy
  exact ⟨v, (mem_switchSet O B S v).mpr (Or.inl ⟨y, hy, hyroot, hv⟩), hvx⟩

/-- Case 1. Every class in a root-containing set has a white-type
replacement pointing back into that finite set. -/
theorem closed_switch (O : RootOrientation M root) (B : BipartiteModel M)
    (S : Finset ι) (hroot : root ∈ S)
    (hstep : ∀ x ∈ S, ∃ y ∈ S, Arc O B x y) : HasFull G label := by
  apply hasFull_of_independent_cover (switchSet O B S) (switchSet_independent O B S)
  intro x
  by_cases hx : x ∈ S
  · obtain ⟨y, hy, hxy⟩ := hstep x hx
    exact arc_representative_mem_switchSet O B S hxy hy
  · have hxr : x ≠ root := fun h => hx (h.symm ▸ hroot)
    exact ⟨(O.black x).1,
      (mem_switchSet O B S _).mpr (Or.inr ⟨x, hx, hxr, rfl⟩), O.color x hxr⟩

theorem white_type_avoids_switchSet
    (O : RootOrientation M root) (B : BipartiteModel M) (S : Finset ι)
    {c : ι} (hc : c ≠ root) (hcS : c ∉ S)
    {v : V} (hv : B.index v = O.white c) :
    ∀ w ∈ switchSet O B S, ¬ G.Adj v w := by
  intro w hw hadj
  have he := (B.edge_iff v w).mp hadj
  rw [hv, O.partner_white] at he
  rcases (mem_switchSet O B S w).mp hw with ⟨d, hdS, hd, hw⟩ | ⟨d, _, hd, rfl⟩
  · rw [hw] at he
    have hcd := O.black_injective hc hd he
    exact hcS (hcd.symm ▸ hdS)
  · rw [B.index_on_matching] at he
    exact O.black_ne_white hc hd he

/-- Case 2. The final vertex has white distinguished neighbour c, while the
transition set avoids the black endpoint c of that component. -/
theorem terminal_switch (O : RootOrientation M root) (B : BipartiteModel M)
    (S : Finset ι) (hroot : root ∈ S) (last c : ι)
    (hc : c ≠ root) (hcS : c ∉ S)
    (hstep : ∀ x ∈ S, x ≠ last → ∃ y ∈ S, Arc O B x y)
    (v : V) (hvl : label v = last) (hvi : B.index v = O.white c) :
    HasFull G label := by
  have havoid := white_type_avoids_switchSet O B S hc hcS hvi
  apply hasFull_of_independent_cover (insert v (switchSet O B S))
  · intro x hx y hy hadj
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx] at hadj
      rcases Finset.mem_insert.mp hy with hy | hy
      · rw [hy] at hadj
        exact G.loopless.irrefl v hadj
      · exact havoid y hy hadj
    · rcases Finset.mem_insert.mp hy with hy | hy
      · rw [hy] at hadj
        exact havoid x hx (G.adj_symm hadj)
      · exact switchSet_independent O B S x hx y hy hadj
  · intro x
    by_cases hxl : x = last
    · exact ⟨v, Finset.mem_insert_self _ _, hvl.trans hxl.symm⟩
    · by_cases hx : x ∈ S
      · obtain ⟨y, hy, hxy⟩ := hstep x hx hxl
        obtain ⟨w, hw, hwx⟩ := arc_representative_mem_switchSet O B S hxy hy
        exact ⟨w, Finset.mem_insert_of_mem hw, hwx⟩
      · have hxr : x ≠ root := fun h => hx (h.symm ▸ hroot)
        exact ⟨(O.black x).1,
          Finset.mem_insert_of_mem ((mem_switchSet O B S _).mpr
            (Or.inr ⟨x, hx, hxr, rfl⟩)), O.color x hxr⟩

/-- A reachable directed cycle triggers Case 1.  The finite set consists of
all classes that can reach the initial vertex of the cycle. -/
theorem cycle_switch (O : RootOrientation M root) (B : BipartiteModel M)
    {x y : ι} (hroot : Reach (Arc O B) root x)
    (hxy : Arc O B x y) (hyx : Reach (Arc O B) y x) : HasFull G label := by
  classical
  let S := Finset.univ.filter (fun z => Reach (Arc O B) z x)
  have hrootS : root ∈ S := by simp [S, hroot]
  apply closed_switch O B S hrootS
  intro z hz
  have hzx : Reach (Arc O B) z x := (Finset.mem_filter.mp hz).2
  by_cases hzeq : z = x
  · subst z
    exact ⟨y, by simp [S, hyx], hxy⟩
  · obtain ⟨w, hzw, hwx⟩ := hzx.first hzeq
    exact ⟨w, by simp [S, hwx], hzw⟩

theorem arc_reach_antisymm (O : RootOrientation M root) (B : BipartiteModel M)
    (hno : ¬ HasFull G label) (hroot : ∀ x, Reach (Arc O B) root x) :
    ∀ x y, Reach (Arc O B) x y → Reach (Arc O B) y x → x = y := by
  intro x y hxy hyx
  by_contra hne
  obtain ⟨z, hxz, hzy⟩ := hxy.first hne
  exact hno (cycle_switch O B (hroot x) hxz (hzy.trans hyx))

/-- A root-to-last route avoiding c triggers Case 2.  No simple-path
existence assertion is needed: the finite avoidance basin supplies every
transition used by terminal_switch. -/
theorem avoiding_path_switch (O : RootOrientation M root) (B : BipartiteModel M)
    {c : ι} (hc : c ≠ root) (v : V) (hvi : B.index v = O.white c)
    (hpath : Avoid (Arc O B) c root (label v)) : HasFull G label := by
  classical
  let S := Finset.univ.filter (fun x => Avoid (Arc O B) c x (label v))
  have hrootS : root ∈ S := by simp [S, hpath]
  have hcS : c ∉ S := by
    intro h
    exact (Finset.mem_filter.mp h).2.1 rfl
  apply terminal_switch O B S hrootS (label v) c hc hcS ?_ v rfl hvi
  intro x hx hxl
  have hx' : Avoid (Arc O B) c x (label v) := (Finset.mem_filter.mp hx).2
  obtain ⟨y, hxy, hy⟩ := hx'.first hxl
  exact ⟨y, by simp [S, hy], hxy⟩

theorem white_index_dominates (O : RootOrientation M root) (B : BipartiteModel M)
    (hno : ¬ HasFull G label) {c : ι} (hc : c ≠ root)
    (v : V) (hvi : B.index v = O.white c) :
    Dominates (Arc O B) root c (label v) :=
  fun hpath => hno (avoiding_path_switch O B hc v hvi hpath)

end JSP896.OddComponents
