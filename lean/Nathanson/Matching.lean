module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Countable.Defs
public import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-!
# Matchings for countable relations with infinite fibers

Greedy injections are combined using the relation-preserving
Schröder--Bernstein theorem. A second construction reserves one prescribed
edge before applying that theorem.

These are classical existence theorems: no computability assertion is made.
-/

public section

namespace Nathanson

universe u v

variable {α : Type u} {β : Type v}

/-- Choose distinct values along natural-number-indexed infinite fibers. -/
theorem exists_injective_nat_of_infinite_fibers
    (R : ℕ → β → Prop)
    (hR : ∀ n, Set.Infinite {b | R n b}) :
    ∃ f : ℕ → β, Function.Injective f ∧ ∀ n, R n (f n) := by
  classical
  have hex (n : ℕ) (l : List β) : ∃ b, R n b ∧ b ∉ l :=
    (hR n).exists_notMem_finite l.finite_toSet
  let next (n : ℕ) (l : List β) : β := Classical.choose (hex n l)
  have hnext (n : ℕ) (l : List β) : R n (next n l) ∧ next n l ∉ l :=
    Classical.choose_spec (hex n l)
  let past : ℕ → List β := Nat.rec [] (fun n l => next n l :: l)
  let f (n : ℕ) : β := next n (past n)
  have hpast (n : ℕ) : past (n + 1) = f n :: past n := rfl
  have hmem : ∀ n k : ℕ, k < n → f k ∈ past n := by
    intro n
    induction n with
    | zero =>
        intro k hk
        exact (Nat.not_lt_zero k hk).elim
    | succ n ih =>
        intro k hk
        rw [hpast]
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · exact List.mem_cons_of_mem _ (ih k hlt)
        · exact List.mem_cons_self
  refine ⟨f, ?_, fun n => (hnext n (past n)).1⟩
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hbad : f j ∈ past j := by
      rw [← hij]
      exact hmem j i hlt
    exact False.elim ((hnext j (past j)).2 hbad)
  · exact heq
  · have hbad : f i ∈ past i := by
      rw [hij]
      exact hmem i j hgt
    exact False.elim ((hnext i (past i)).2 hbad)

/-- A countable family of infinite sets has a system of distinct representatives. -/
theorem exists_injective_of_infinite_fibers [Countable α]
    (R : α → β → Prop)
    (hR : ∀ a, Set.Infinite {b | R a b}) :
    ∃ f : α → β, Function.Injective f ∧ ∀ a, R a (f a) := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · letI : IsEmpty α := hα
    exact ⟨isEmptyElim, fun a => isEmptyElim a, fun a => isEmptyElim a⟩
  · letI : Nonempty α := hα
    obtain ⟨c, hc⟩ := exists_injective_nat α
    obtain ⟨f, hf, hfR⟩ := exists_injective_nat_of_infinite_fibers
      (fun n b => R (Function.invFun c n) b)
      (fun n => hR (Function.invFun c n))
    refine ⟨fun a => f (c a), hf.comp hc, ?_⟩
    intro a
    have hinv : Function.invFun c (c a) = a :=
      Function.leftInverse_invFun hc a
    simpa only [hinv] using hfR (c a)

/-- Countable infinite-neighbor relations admit a relation-preserving equivalence. -/
theorem exists_equiv_of_infinite_fibers [Countable α] [Countable β]
    (R : α → β → Prop)
    (hleft : ∀ a, Set.Infinite {b | R a b})
    (hright : ∀ b, Set.Infinite {a | R a b}) :
    ∃ e : α ≃ β, ∀ a, R a (e a) := by
  obtain ⟨f, hf, hfR⟩ := exists_injective_of_infinite_fibers R hleft
  obtain ⟨g, hg, hgR⟩ :=
    exists_injective_of_infinite_fibers (fun b a => R a b) hright
  obtain ⟨h, hh, hhR⟩ :=
    Function.Embedding.schroeder_bernstein_of_rel hf hg R hfR hgR
  exact ⟨Equiv.ofBijective h hh, hhR⟩

/-- A prescribed allowed edge can be reserved in an injective choice function. -/
theorem exists_injective_of_infinite_fibers_fix [Countable α]
    (R : α → β → Prop)
    (hR : ∀ a, Set.Infinite {b | R a b})
    (a₀ : α) (b₀ : β) (h₀ : R a₀ b₀) :
    ∃ f : α → β, Function.Injective f ∧ (∀ a, R a (f a)) ∧ f a₀ = b₀ := by
  classical
  have hdelete (a : {a : α // a ≠ a₀}) :
      Set.Infinite {b | R a.1 b ∧ b ≠ b₀} := by
    have hset : {b | R a.1 b ∧ b ≠ b₀} = {b | R a.1 b} \ {b₀} := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    rw [hset]
    exact (hR a.1).sdiff (Set.finite_singleton b₀)
  obtain ⟨g, hg, hgR⟩ := exists_injective_of_infinite_fibers
    (fun a : {a : α // a ≠ a₀} => fun b => R a.1 b ∧ b ≠ b₀) hdelete
  let f (a : α) : β := if ha : a = a₀ then b₀ else g ⟨a, ha⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a a' haa'
    by_cases ha : a = a₀
    · subst a
      by_cases ha' : a' = a₀
      · exact ha'.symm
      · have heq : b₀ = g ⟨a', ha'⟩ := by
          simpa only [f, dif_pos rfl, dif_neg ha'] using haa'
        exact False.elim ((hgR ⟨a', ha'⟩).2 heq.symm)
    · by_cases ha' : a' = a₀
      · subst a'
        have heq : g ⟨a, ha⟩ = b₀ := by
          simpa only [f, dif_neg ha, dif_pos rfl] using haa'
        exact False.elim ((hgR ⟨a, ha⟩).2 heq)
      · have heq : g ⟨a, ha⟩ = g ⟨a', ha'⟩ := by
          simpa only [f, dif_neg ha, dif_neg ha'] using haa'
        exact congrArg Subtype.val (hg heq)
  · intro a
    by_cases ha : a = a₀
    · subst a
      simpa only [f, dif_pos rfl] using h₀
    · simpa only [f, dif_neg ha] using (hgR ⟨a, ha⟩).1
  · simp only [f, dif_pos rfl]

/-- A relation-preserving equivalence can be required to contain one allowed edge. -/
theorem exists_equiv_of_infinite_fibers_fix [Countable α] [Countable β]
    (R : α → β → Prop)
    (hleft : ∀ a, Set.Infinite {b | R a b})
    (hright : ∀ b, Set.Infinite {a | R a b})
    (a₀ : α) (b₀ : β) (h₀ : R a₀ b₀) :
    ∃ e : α ≃ β, (∀ a, R a (e a)) ∧ e a₀ = b₀ := by
  obtain ⟨f, hf, hfR, hfix⟩ :=
    exists_injective_of_infinite_fibers_fix R hleft a₀ b₀ h₀
  obtain ⟨g, hg, hgR, hgfix⟩ :=
    exists_injective_of_infinite_fibers_fix (fun b a => R a b) hright b₀ a₀ h₀
  let Q (a : α) (b : β) : Prop := R a b ∧ (a = a₀ → b = b₀)
  have hfQ (a : α) : Q a (f a) := by
    refine ⟨hfR a, ?_⟩
    intro ha
    simpa only [ha] using hfix
  have hgQ (b : β) : Q (g b) b := by
    refine ⟨hgR b, ?_⟩
    intro hga
    exact hg (hga.trans hgfix.symm)
  obtain ⟨h, hh, hhQ⟩ :=
    Function.Embedding.schroeder_bernstein_of_rel hf hg Q hfQ hgQ
  exact ⟨Equiv.ofBijective h hh, fun a => (hhQ a).1, (hhQ a₀).2 rfl⟩

#print axioms exists_injective_nat_of_infinite_fibers
#print axioms exists_injective_of_infinite_fibers
#print axioms exists_equiv_of_infinite_fibers
#print axioms exists_injective_of_infinite_fibers_fix
#print axioms exists_equiv_of_infinite_fibers_fix

end Nathanson
