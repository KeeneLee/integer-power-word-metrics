import Nathanson.AbstractControl

noncomputable section
namespace Nathanson
variable {α β γ : Type*} [Zero α] [Zero β] [Zero γ]

def letterCongr (e : α ≃ β) : Letter α ≃ Letter β where
  toFun
    | .edit a => .edit (e a)
    | .high => .high
    | .low => .low
  invFun
    | .edit b => .edit (e.symm b)
    | .high => .high
    | .low => .low
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

def wordCongr (e : α ≃ β) (he : e 0 = 0) : RWord α ≃ RWord β :=
  Finsupp.mapRange.equiv (letterCongr e) (by simp [letterCongr, he]; rfl)

@[simp] theorem wordCongr_apply (e : α ≃ β) (he : e 0 = 0) (x : RWord α) (i : ℕ) :
    wordCongr e he x i = letterCongr e (x i) := rfl

theorem wordCongr_dist (e : α ≃ β) (he : e 0 = 0) (x y : RWord α) :
    hDist (wordCongr e he x) (wordCongr e he y) = hDist x y := by
  classical
  unfold hDist
  congr 1
  ext i
  simp only [mem_hdiff, wordCongr_apply, ne_eq, Equiv.apply_eq_iff_eq]

theorem wordCongr_frozen (e : α ≃ β) (he : e 0 = 0) (x : RWord α) (i : ℕ) :
    (wordCongr e he x i).frozen = (x i).frozen := by
  rw [wordCongr_apply]
  cases x i <;> rfl

theorem wordCongr_flip (e : α ≃ β) (he : e 0 = 0) (s : Finset ℕ) (x : RWord α) :
    wordCongr e he (flipAt s x) = flipAt s (wordCongr e he x) := by
  classical
  ext i
  simp only [wordCongr_apply, flipAt_apply]
  split_ifs <;> cases x i <;> rfl

theorem equiv_symm_frozen (e : RWord α ≃ RWord β)
    (he : ∀ x i, (e x i).frozen = (x i).frozen) (x : RWord β) (i : ℕ) :
    (e.symm x i).frozen = (x i).frozen := by
  simpa using (he (e.symm x) i).symm

theorem equiv_symm_flip (e : RWord α ≃ RWord β)
    (he : ∀ s x, e (flipAt s x) = flipAt s (e x)) (s : Finset ℕ) (x : RWord β) :
    e.symm (flipAt s x) = flipAt s (e.symm x) := by
  apply e.injective
  simp [he]

structure RelativeAbsorption (α β : Type*) [Zero α] [Zero β] where
  equiv : RWord α ≃ RWord (α × β)
  forward : ∀ x y, hDist (equiv x) (equiv y) ≤ 7 * hDist x y
  backward : ∀ x y, hDist (equiv.symm x) (equiv.symm y) ≤ 5 * hDist x y
  frozen : ∀ x i, (equiv x i).frozen = (x i).frozen
  flip : ∀ s x, equiv (flipAt s x) = flipAt s (equiv x)

def relativeFromAbsorptions (a : RelativeAbsorption α β) (b : RelativeAbsorption β α) :
    RelativeEquiv α β 35 := by
  let w : RWord (α × β) ≃ RWord (β × α) := wordCongr (Equiv.prodComm α β) rfl
  let e := (a.equiv.trans w).trans b.equiv.symm
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro x y
    change hDist (b.equiv.symm (w (a.equiv x))) (b.equiv.symm (w (a.equiv y))) ≤ _
    calc
      _ ≤ 5 * hDist (w (a.equiv x)) (w (a.equiv y)) := b.backward _ _
      _ = 5 * hDist (a.equiv x) (a.equiv y) :=
        congrArg (5 * ·) (wordCongr_dist (Equiv.prodComm α β) rfl _ _)
      _ ≤ 5 * (7 * hDist x y) := Nat.mul_le_mul_left _ (a.forward x y)
      _ = 35 * hDist x y := by omega
  · intro x y
    change hDist (a.equiv.symm (w.symm (b.equiv x))) (a.equiv.symm (w.symm (b.equiv y))) ≤ _
    have hw (u v : RWord (β × α)) : hDist (w.symm u) (w.symm v) = hDist u v := by
      have h := wordCongr_dist (Equiv.prodComm α β) rfl (w.symm u) (w.symm v)
      simpa only [← show wordCongr (Equiv.prodComm α β) rfl = w from rfl,
        Equiv.apply_symm_apply] using h.symm
    calc
      _ ≤ 5 * hDist (w.symm (b.equiv x)) (w.symm (b.equiv y)) := a.backward _ _
      _ = 5 * hDist (b.equiv x) (b.equiv y) := by rw [hw]
      _ ≤ 5 * (7 * hDist x y) := Nat.mul_le_mul_left _ (b.forward x y)
      _ = 35 * hDist x y := by omega
  · intro x i
    change (b.equiv.symm (w (a.equiv x)) i).frozen = _
    rw [equiv_symm_frozen b.equiv b.frozen]
    exact (wordCongr_frozen (Equiv.prodComm α β) rfl _ _).trans (a.frozen x i)
  · intro s x
    change b.equiv.symm (w (a.equiv (flipAt s x))) = _
    rw [a.flip]
    exact (congrArg b.equiv.symm (wordCongr_flip (Equiv.prodComm α β) rfl s _)).trans
      (equiv_symm_flip b.equiv b.flip s (w (a.equiv x)))

#print axioms relativeFromAbsorptions
end Nathanson
