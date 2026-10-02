import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Finite directed reachability and terminal dominator blocks

This module is independent of the transversal problem.  It uses explicit
finite reachability, not a supplied termination or switching certificate.
The root-dominator blocks of an acyclic rooted digraph partition its non-root
vertices.  A terminal block has no outgoing edge and has no strict non-root
dominator outside the block.  Source only; no compiler has been run.
-/

namespace JSP896.OddComponents.Directed

variable {α : Type*}

inductive Reach (R : α → α → Prop) : α → α → Prop
  | refl (a) : Reach R a a
  | head {a b c} : R a b → Reach R b c → Reach R a c

namespace Reach

theorem single {R : α → α → Prop} {a b : α} (h : R a b) : Reach R a b :=
  .head h (.refl b)

theorem trans {R : α → α → Prop} {a b c : α}
    (hab : Reach R a b) (hbc : Reach R b c) : Reach R a c := by
  induction hab generalizing c with
  | refl => exact hbc
  | head h _ ih => exact .head h (ih (c := c) hbc)

theorem mono {R Q : α → α → Prop} (hRQ : ∀ a b, R a b → Q a b)
    {a b : α} (h : Reach R a b) : Reach Q a b := by
  induction h with
  | refl a => exact .refl a
  | head h _ ih => exact .head (hRQ _ _ h) ih

theorem first {R : α → α → Prop} {a b : α} (h : Reach R a b) (hne : a ≠ b) :
    ∃ c, R a c ∧ Reach R c b := by
  cases h with
  | refl => exact (hne rfl).elim
  | @head a c b hac hcb => exact ⟨c, hac, hcb⟩

theorem last {R : α → α → Prop} {a b : α} (h : Reach R a b) :
    a = b ∨ ∃ c, Reach R a c ∧ R c b := by
  induction h with
  | refl => exact Or.inl rfl
  | @head a c b hac hcb ih =>
    rcases ih with rfl | ⟨d, hcd, hdb⟩
    · exact Or.inr ⟨a, .refl a, hac⟩
    · exact Or.inr ⟨d, .head hac hcd, hdb⟩

end Reach

def Avoid (R : α → α → Prop) (c a b : α) : Prop :=
  a ≠ c ∧ Reach (fun x y => R x y ∧ x ≠ c ∧ y ≠ c) a b

theorem Avoid.reach {R : α → α → Prop} {c a b : α} (h : Avoid R c a b) :
    Reach R a b := h.2.mono (fun _ _ h => h.1)

theorem Avoid.mono {R Q : α → α → Prop} (hRQ : ∀ a b, R a b → Q a b)
    {c a b : α} (h : Avoid R c a b) : Avoid Q c a b :=
  ⟨h.1, h.2.mono (fun x y h => ⟨hRQ x y h.1, h.2⟩)⟩

theorem Avoid.end_ne {R : α → α → Prop} {c a b : α} (h : Avoid R c a b) : b ≠ c := by
  rcases h.2.last with heq | ⟨d, _, hdb⟩
  · exact heq ▸ h.1
  · exact hdb.2.2

theorem Avoid.refl {R : α → α → Prop} {c a : α} (h : a ≠ c) : Avoid R c a a :=
  ⟨h, .refl a⟩

theorem Avoid.trans {R : α → α → Prop} {c a b d : α}
    (hab : Avoid R c a b) (hbd : Avoid R c b d) : Avoid R c a d :=
  ⟨hab.1, hab.2.trans hbd.2⟩

theorem Avoid.head {R : α → α → Prop} {c a b d : α}
    (hab : R a b) (ha : a ≠ c) (hbd : Avoid R c b d) : Avoid R c a d :=
  ⟨ha, .head ⟨hab, ha, hbd.1⟩ hbd.2⟩

theorem Avoid.tail {R : α → α → Prop} {c a b d : α}
    (hab : Avoid R c a b) (hbd : R b d) (hd : d ≠ c) : Avoid R c a d :=
  hab.trans ⟨hab.end_ne, .single ⟨hbd, hab.end_ne, hd⟩⟩

theorem Avoid.first {R : α → α → Prop} {c a b : α}
    (h : Avoid R c a b) (hne : a ≠ b) :
    ∃ d, R a d ∧ Avoid R c d b := by
  obtain ⟨d, had, hdb⟩ := h.2.first hne
  exact ⟨d, had.1, had.2.2, hdb⟩

/-- A walk either avoids c or contains a suffix starting at c. -/
theorem reach_avoid_or_suffix {R : α → α → Prop} {a b : α}
    (h : Reach R a b) (c : α) : Avoid R c a b ∨ Reach R c b := by
  induction h with
  | refl a =>
    by_cases h : a = c
    · subst a; exact Or.inr (.refl c)
    · exact Or.inl (.refl h)
  | @head a d b had hdb ih =>
    by_cases ha : a = c
    · subst a; exact Or.inr (.head had hdb)
    · rcases ih with h | h
      · exact Or.inl (h.head had ha)
      · exact Or.inr h

/-- If c cannot be reached from the initial point, the whole walk avoids c. -/
theorem avoid_of_not_reach {R : α → α → Prop} {a b c : α}
    (h : Reach R a b) (hn : ¬ Reach R a c) : Avoid R c a b := by
  revert hn
  induction h with
  | refl a =>
    intro hn
    apply Avoid.refl
    intro heq
    subst c
    exact hn (.refl a)
  | @head a d b had hdb ih =>
    intro hn
    have ha : a ≠ c := by
      intro heq
      subst c
      exact hn (.refl a)
    have hd : ¬ Reach R d c := fun h => hn (.head had h)
    exact (ih hd).head had ha

def Dominates (R : α → α → Prop) (root c x : α) : Prop := ¬ Avoid R c root x

theorem dominates_self (R : α → α → Prop) (root c : α) : Dominates R root c c :=
  fun h => h.end_ne rfl

theorem not_dominates_root {R : α → α → Prop} {root c : α} (hc : c ≠ root) :
    ¬ Dominates R root c root := fun h => h (.refl hc.symm)

theorem Dominates.reach {R : α → α → Prop} {root c x : α}
    (hroot : Reach R root x) (h : Dominates R root c x) : Reach R c x := by
  rcases reach_avoid_or_suffix hroot c with h' | h'
  · exact (h h').elim
  · exact h'

theorem Dominates.trans {R : α → α → Prop} {root c d x : α}
    (hcd : Dominates R root c d) (hdx : Dominates R root d x) :
    Dominates R root c x := by
  intro hav
  have hsplit : ∀ {a b}, Reach (fun x y => R x y ∧ x ≠ c ∧ y ≠ c) a b →
      a ≠ c → Avoid R d a b ∨ Avoid R c a d := by
    intro a b h
    induction h with
    | refl a =>
      intro hac
      by_cases had : a = d
      · subst a
        exact Or.inr (.refl hac)
      · exact Or.inl (.refl had)
    | @head a e b hae heb ih =>
      intro hac
      by_cases had : a = d
      · subst a; exact Or.inr (.refl hae.2.1)
      · rcases ih hae.2.2 with h | h
        · exact Or.inl (h.head hae.1 had)
        · exact Or.inr (h.head hae.1 hae.2.1)
  rcases hsplit hav.2 hav.1 with h | h
  · exact hdx h
  · exact hcd h

theorem Dominates.of_edge {R : α → α → Prop} {root c x y : α}
    (h : Dominates R root c y) (hxy : R x y) (hy : y ≠ c) :
    Dominates R root c x := fun hav => h (hav.tail hxy hy)

theorem Dominates.backward {R : α → α → Prop} {root c x y : α}
    (h : Dominates R root c x) (hyx : Reach R y x) (hnyc : ¬ Reach R y c) :
    Dominates R root c y := fun hav => h (hav.trans (avoid_of_not_reach hyx hnyc))

section Finite

variable [Fintype α] [DecidableEq α]

noncomputable def future (R : α → α → Prop) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (Reach R x)

@[simp] theorem mem_future (R : α → α → Prop) (x y : α) :
    y ∈ future R x ↔ Reach R x y := by
  classical
  simp [future]

noncomputable def rank (R : α → α → Prop) (x : α) : ℕ := (future R x).card

theorem rank_lt_of_reach {R : α → α → Prop}
    (hantisymm : ∀ a b, Reach R a b → Reach R b a → a = b)
    {a b : α} (hab : Reach R a b) (hne : a ≠ b) : rank R b < rank R a := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    exact (mem_future _ _ _).mpr (hab.trans ((mem_future _ _ _).mp hx))
  · intro heq
    have ha : a ∈ future R a := (mem_future _ _ _).mpr (.refl a)
    rw [← heq] at ha
    exact hne (hantisymm a b hab ((mem_future _ _ _).mp ha))

theorem Dominates.comparable {R : α → α → Prop} {root c d x : α}
    (hroot : ∀ y, Reach R root y)
    (hantisymm : ∀ a b, Reach R a b → Reach R b a → a = b)
    (hc : Dominates R root c x) (hd : Dominates R root d x) :
    Dominates R root c d ∨ Dominates R root d c := by
  classical
  by_cases hcd : Dominates R root c d
  · exact Or.inl hcd
  · right
    have hav : Avoid R c root d := not_not.mp hcd
    have hdx := hd.reach (hroot x)
    have hdc : Reach R d c := by
      by_contra h
      exact hc (hav.trans (avoid_of_not_reach hdx h))
    by_cases heq : c = d
    · subst d; exact dominates_self _ _ _
    · apply hd.backward (hc.reach (hroot x))
      intro h
      exact heq (hantisymm c d h hdc)

def RootDominator (R : α → α → Prop) (root c : α) : Prop :=
  c ≠ root ∧ ∀ d, d ≠ root → Dominates R root d c → d = c

theorem exists_rootDominator {R : α → α → Prop} {root x : α}
    (hroot : ∀ y, Reach R root y)
    (hantisymm : ∀ a b, Reach R a b → Reach R b a → a = b)
    (hx : x ≠ root) :
    ∃ c, RootDominator R root c ∧ Dominates R root c x := by
  classical
  let C := Finset.univ.filter (fun c => c ≠ root ∧ Dominates R root c x)
  have hC : C.Nonempty := ⟨x, by simp [C, hx, dominates_self]⟩
  obtain ⟨c, hc, hmax⟩ := C.exists_max_image (rank R) hC
  have hc' : c ≠ root ∧ Dominates R root c x := (Finset.mem_filter.mp hc).2
  refine ⟨c, ⟨hc'.1, ?_⟩, hc'.2⟩
  intro d hd hdc
  by_contra hne
  have hdx := hdc.trans hc'.2
  have hdC : d ∈ C := by simp [C, hd, hdx]
  have hle := hmax d hdC
  have hlt := rank_lt_of_reach hantisymm (hdc.reach (hroot c)) hne
  omega

theorem rootDominator_unique {R : α → α → Prop} {root c d x : α}
    (hroot : ∀ y, Reach R root y)
    (hantisymm : ∀ a b, Reach R a b → Reach R b a → a = b)
    (hc : RootDominator R root c) (hd : RootDominator R root d)
    (hcx : Dominates R root c x) (hdx : Dominates R root d x) : c = d := by
  rcases hcx.comparable hroot hantisymm hdx with h | h
  · exact hd.2 c hc.1 h
  · exact (hc.2 d hd.1 h).symm

/-- The terminal root-dominator block used in the odd-component proof.
Both closure assertions are proved here from finite minimality. -/
theorem exists_terminal_block {R : α → α → Prop} {root : α}
    (hroot : ∀ y, Reach R root y)
    (hantisymm : ∀ a b, Reach R a b → Reach R b a → a = b)
    (hne : ∃ x, x ≠ root) :
    ∃ c, RootDominator R root c ∧
      (∀ x y, Dominates R root c x → R x y → Dominates R root c y) ∧
      (∀ x d, Dominates R root c x → d ≠ root → Dominates R root d x →
        Dominates R root c d) := by
  classical
  let C := Finset.univ.filter (RootDominator R root)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨d, hd, _⟩ := exists_rootDominator hroot hantisymm hx
  have hC : C.Nonempty := ⟨d, by simp [C, hd]⟩
  obtain ⟨c, hc, hmin⟩ := C.exists_min_image (rank R) hC
  have hc' : RootDominator R root c := (Finset.mem_filter.mp hc).2
  refine ⟨c, hc', ?_, ?_⟩
  · intro x y hcx hxy
    by_contra hcy
    have hy : y ≠ root := by
      intro heq
      subst y
      have hcr := (hcx.reach (hroot x)).trans (.single hxy)
      exact hc'.1 (hantisymm c root hcr (hroot c))
    obtain ⟨e, he, hey⟩ := exists_rootDominator hroot hantisymm hy
    have hye : y = e := by
      by_contra h
      have hex := hey.of_edge hxy h
      have hce := rootDominator_unique hroot hantisymm hc' he hcx hex
      exact hcy (hce.symm ▸ hey)
    subst y
    have hce : c ≠ e := by
      intro heq
      subst e
      exact hcy (dominates_self _ _ _)
    have hreach := (hcx.reach (hroot x)).trans (.single hxy)
    have hlt := rank_lt_of_reach hantisymm hreach hce
    have hle := hmin e (by simp [C, he])
    omega
  · intro x d hcx hd hdx
    rcases hcx.comparable hroot hantisymm hdx with h | h
    · exact h
    · have heq := hc'.2 d hd h
      subst d
      exact dominates_self _ _ _

end Finite

end JSP896.OddComponents.Directed
