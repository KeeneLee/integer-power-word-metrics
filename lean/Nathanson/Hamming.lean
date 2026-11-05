import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Nat
import Mathlib.Tactic

noncomputable section
open Function Set
namespace Nathanson

variable {α β : Type*}

def hdiff [Zero α] (x y : ℕ →₀ α) : Finset ℕ := by
  classical
  exact (x.support ∪ y.support).filter (fun i => x i ≠ y i)

def hDist [Zero α] (x y : ℕ →₀ α) : ℕ := (hdiff x y).card

@[simp] theorem mem_hdiff [Zero α] (x y : ℕ →₀ α) (i : ℕ) :
    i ∈ hdiff x y ↔ x i ≠ y i := by
  classical
  simp only [hdiff, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff]
  constructor
  · exact And.right
  · intro h
    exact ⟨by by_cases hx : x i = 0 <;> by_cases hy : y i = 0 <;> aesop, h⟩

theorem hdiff_comm [Zero α] (x y : ℕ →₀ α) : hdiff x y = hdiff y x := by
  ext i
  simp [ne_comm]

theorem hDist_comm [Zero α] (x y : ℕ →₀ α) : hDist x y = hDist y x := by
  simp [hDist, hdiff_comm x y]

@[simp] theorem hDist_self [Zero α] (x : ℕ →₀ α) : hDist x x = 0 := by
  classical
  simp [hDist, hdiff]

theorem hDist_triangle [Zero α] (x y z : ℕ →₀ α) :
    hDist x z ≤ hDist x y + hDist y z := by
  classical
  have h : hdiff x z ⊆ hdiff x y ∪ hdiff y z := by
    intro i hi
    simp only [mem_hdiff, Finset.mem_union] at *
    by_cases hxy : x i = y i
    · exact Or.inr (by intro hyz; exact hi (hxy.trans hyz))
    · exact Or.inl hxy
  exact (Finset.card_le_card h).trans (Finset.card_union_le _ _)

theorem hDist_le_of_agree_off [Zero α] (x y : ℕ →₀ α) (s : Finset ℕ)
    (h : ∀ i, i ∉ s → x i = y i) : hDist x y ≤ s.card := by
  classical
  apply Finset.card_le_card
  intro i hi
  by_contra hn
  exact (mem_hdiff x y i).mp hi (h i hn)

theorem agree_off_hdiff [Zero α] (x y : ℕ →₀ α) :
    ∀ i, i ∉ hdiff x y → x i = y i := by
  intro i hi
  simpa using hi

theorem hDist_mapRange_le [Zero α] [Zero β] (f : α → β) (hf : f 0 = 0)
    (x y : ℕ →₀ α) :
    hDist (x.mapRange f hf) (y.mapRange f hf) ≤ hDist x y := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [mem_hdiff, Finsupp.mapRange_apply] at *
  exact fun h => hi (congrArg f h)

inductive Letter (α : Type*) where
  | edit : α → Letter α
  | high : Letter α
  | low : Letter α
  deriving DecidableEq

namespace Letter
instance [Zero α] : Zero (Letter α) := ⟨edit 0⟩

def ordinary [Zero α] : Letter α → α
  | edit a => a
  | high => 0
  | low => 0

def frozen : Letter α → Option Bool
  | edit _ => none
  | high => some true
  | low => some false

def flip : Letter α → Letter α
  | edit a => edit a
  | high => low
  | low => high

@[simp] theorem ordinary_zero [Zero α] : ordinary (0 : Letter α) = 0 := rfl
@[simp] theorem frozen_zero [Zero α] : frozen (0 : Letter α) = none := rfl
@[simp] theorem flip_zero [Zero α] : flip (0 : Letter α) = 0 := rfl
@[simp] theorem flip_flip (a : Letter α) : flip (flip a) = a := by cases a <;> rfl
@[simp] theorem frozen_edit (a : α) : frozen (edit a) = none := rfl

def encode : Letter α → Option (Option α)
  | edit a => some (some a)
  | high => none
  | low => some none

instance [Countable α] : Countable (Letter α) :=
  Function.Injective.countable (f := encode) (by intro x y h; cases x <;> cases y <;> simpa [encode] using h)
end Letter

abbrev RWord (α : Type*) [Zero α] := ℕ →₀ Letter α

def edits [Zero α] (x : RWord α) : ℕ →₀ α := x.mapRange Letter.ordinary rfl

def frozenSet [Zero α] (x : RWord α) : Finset ℕ := by
  classical
  exact x.support.filter (fun i => (x i).frozen ≠ none)

@[simp] theorem mem_frozenSet [Zero α] (x : RWord α) (i : ℕ) :
    i ∈ frozenSet x ↔ (x i).frozen ≠ none := by
  classical
  simp only [frozenSet, Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    intro hz
    exact h (by rw [hz]; rfl)

def flipAt [Zero α] (s : Finset ℕ) (x : RWord α) : RWord α :=
  Finsupp.onFinset x.support (fun i => if i ∈ s then (x i).flip else x i) (by
    classical
    intro i hi
    by_contra hn
    have hz : x i = 0 := Finsupp.notMem_support_iff.mp hn
    simp [hz] at hi)

@[simp] theorem flipAt_apply [Zero α] (s : Finset ℕ) (x : RWord α) (i : ℕ) :
    flipAt s x i = if i ∈ s then (x i).flip else x i := rfl

def RelativeEquiv (α β : Type*) [Zero α] [Zero β] (K : ℕ) :=
  {e : RWord α ≃ RWord β //
    (∀ x y, hDist (e x) (e y) ≤ K * hDist x y) ∧
    (∀ x y, hDist (e.symm x) (e.symm y) ≤ K * hDist x y) ∧
    (∀ x i, (e x i).frozen = (x i).frozen) ∧
    (∀ s x, e (flipAt s x) = flipAt s (e x))}

end Nathanson
