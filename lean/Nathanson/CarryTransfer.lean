import Nathanson.Digits
import Nathanson.Hamming
import Nathanson.WordMetric

/-! Conditional transfer from relative Hamming equivalences to integer word metrics. -/

namespace Nathanson
noncomputable section
open scoped BigOperators

def letterValue (a : ℕ) : Letter (Fin (a - 2)) → ℤ
  | .edit i => i.val
  | .high => (a : ℤ) - 2
  | .low => -1

@[simp] theorem letterValue_zero (a : ℕ) [NeZero (a - 2)] :
    letterValue a 0 = 0 := rfl

theorem letterValue_bounds (a : ℕ) (ha : 4 ≤ a) (l : Letter (Fin (a - 2))) :
    -1 ≤ letterValue a l ∧ letterValue a l ≤ (a : ℤ) - 2 := by
  cases l with
  | edit i => have := i.isLt; simp only [letterValue]; constructor <;> omega
  | high => simp only [letterValue]; constructor <;> omega
  | low => simp only [letterValue]; constructor <;> omega

theorem letterValue_injective (a : ℕ) (ha : 4 ≤ a) :
    Function.Injective (letterValue a) := by
  intro l m h
  cases l with
  | edit i =>
    cases m with
    | edit j =>
      have hij : i = j := by apply Fin.ext; simpa [letterValue] using h
      simp [hij]
    | high => have := i.isLt; simp only [letterValue] at h; omega
    | low => simp only [letterValue] at h; omega
  | high =>
    cases m with
    | edit j => have := j.isLt; simp only [letterValue] at h; omega
    | high => rfl
    | low => simp only [letterValue] at h; omega
  | low =>
    cases m with
    | edit j => simp only [letterValue] at h; omega
    | high => simp only [letterValue] at h; omega
    | low => rfl

def letterEncode (a : ℕ) [NeZero (a - 2)] (z : ℤ) : Letter (Fin (a - 2)) :=
  if z = -1 then .low else
  if z = (a : ℤ) - 2 then .high else
  .edit ⟨z.toNat % (a - 2), Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩

theorem letterValue_encode (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a) (z : ℤ)
    (hz : -1 ≤ z ∧ z ≤ (a : ℤ) - 2) :
    letterValue a (letterEncode a z) = z := by
  by_cases hlow : z = -1
  · simp [letterEncode, hlow, letterValue]
  by_cases hhigh : z = (a : ℤ) - 2
  · have hn : (a : ℤ) - 2 ≠ -1 := by omega
    simp [letterEncode, hhigh, hn, letterValue]
  have hn : z.toNat < a - 2 := by omega
  simp only [letterEncode, if_neg hlow, if_neg hhigh, letterValue, Nat.mod_eq_of_lt hn]
  omega

@[simp] theorem letterEncode_value (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (l : Letter (Fin (a - 2))) : letterEncode a (letterValue a l) = l := by
  apply letterValue_injective a ha
  exact letterValue_encode a ha _ (letterValue_bounds a ha l)

@[simp] theorem letterEncode_zero (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a) :
    letterEncode a 0 = 0 := by
  simpa only [letterValue_zero] using letterEncode_value a ha 0

def wordToDigits (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x : RWord (Fin (a - 2))) : DigitWord a :=
  ⟨x.mapRange (letterValue a) (letterValue_zero a),
    fun i => letterValue_bounds a ha (x i)⟩

def digitsToWord (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x : DigitWord a) : RWord (Fin (a - 2)) :=
  x.val.mapRange (letterEncode a) (letterEncode_zero a ha)

@[simp] theorem wordToDigits_apply (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x : RWord (Fin (a - 2))) (i : ℕ) :
    (wordToDigits a ha x).val i = letterValue a (x i) := rfl

@[simp] theorem digitsToWord_apply (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x : DigitWord a) (i : ℕ) :
    digitsToWord a ha x i = letterEncode a (x.val i) := rfl

@[simp] theorem wordToDigits_toWord (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x : DigitWord a) : wordToDigits a ha (digitsToWord a ha x) = x := by
  apply Subtype.ext
  ext i
  exact letterValue_encode a ha _ (x.property i)

@[simp] theorem digitsToWord_toDigits (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x : RWord (Fin (a - 2))) : digitsToWord a ha (wordToDigits a ha x) = x := by
  ext i
  exact letterEncode_value a ha (x i)

def digitWordEquivR (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a) :
    DigitWord a ≃ RWord (Fin (a - 2)) where
  toFun := digitsToWord a ha
  invFun := wordToDigits a ha
  left_inv := wordToDigits_toWord a ha
  right_inv := digitsToWord_toDigits a ha

def wordIntegerEquiv (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a) :
    RWord (Fin (a - 2)) ≃ ℤ :=
  (digitWordEquivR a ha).symm.trans (digitEquiv a ha)

@[simp] theorem wordIntegerEquiv_apply (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x : RWord (Fin (a - 2))) :
    wordIntegerEquiv a ha x = decode (wordToDigits a ha x) := rfl

theorem letter_diff_bound (a : ℕ) (ha : 4 ≤ a) (l m : Letter (Fin (a - 2))) :
    (letterValue a l - letterValue a m).natAbs ≤ a - 1 := by
  have hl := letterValue_bounds a ha l
  have hm := letterValue_bounds a ha m
  by_cases hp : 0 ≤ letterValue a l - letterValue a m
  · have h := Int.natAbs_of_nonneg hp
    omega
  · have h := Int.natAbs_of_nonneg (show 0 ≤ -(letterValue a l - letterValue a m) by omega)
    rw [Int.natAbs_neg] at h
    omega

theorem wordInteger_hamming_bound (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x y : RWord (Fin (a - 2))) :
    wordDist a (wordIntegerEquiv a ha x) (wordIntegerEquiv a ha y) ≤
      (a - 1) * hDist x y := by
  classical
  let c := (wordToDigits a ha y).val - (wordToDigits a ha x).val
  have hc : c.support ⊆ hdiff x y := by
    intro i hi
    rw [mem_hdiff]
    intro he
    have hn := Finsupp.mem_support_iff.mp hi
    apply hn
    simp [c, he]
  have he : wordIntegerEquiv a ha y - wordIntegerEquiv a ha x = digitEval a c := by
    exact (digitEval_sub a _ _).symm
  unfold wordDist
  rw [he]
  apply (wordLength_finsupp_sum_le a c).trans
  change (∑ i ∈ c.support, (c i).natAbs) ≤ _
  calc
    (∑ i ∈ c.support, (c i).natAbs) ≤ ∑ _i ∈ c.support, (a - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact letter_diff_bound a ha (y i) (x i)
    _ = (a - 1) * c.support.card := by simp [Nat.mul_comm]
    _ ≤ (a - 1) * hDist x y := Nat.mul_le_mul_left _ (Finset.card_le_card hc)

@[simp] theorem letterValue_digitsToWord (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x : DigitWord a) (i : ℕ) :
    letterValue a (digitsToWord a ha x i) = x.val i :=
  letterValue_encode a ha _ (x.property i)

theorem wordInteger_flip_run (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x : RWord (Fin (a - 2))) (k c : ℕ)
    (hrun : ∀ j, j < c → x (k + j) = .high) :
    wordIntegerEquiv a ha (flipAt (Finset.Ico k (k + c)) x) =
      wordIntegerEquiv a ha x + (a : ℤ) ^ k - (a : ℤ) ^ (k + c) := by
  have he : (wordToDigits a ha (flipAt (Finset.Ico k (k + c)) x)).val =
      digitFlip (wordToDigits a ha x).val k c := by
    ext i
    rw [wordToDigits_apply, flipAt_apply, digitFlip_apply]
    by_cases hi : k ≤ i ∧ i < k + c
    · have hir : i = k + (i - k) := by omega
      have hxi : x i = .high := by
        rw [hir]
        exact hrun (i - k) (by omega)
      simp [Finset.mem_Ico, hi, hxi, Letter.flip, letterValue]
    · simp [Finset.mem_Ico, hi]
  change digitEval a (wordToDigits a ha (flipAt (Finset.Ico k (k + c)) x)).val =
    digitEval a (wordToDigits a ha x).val + (a : ℤ) ^ k - (a : ℤ) ^ (k + c)
  rw [he]
  apply digitEval_flip
  intro j hj
  simp [hrun j hj, letterValue]

theorem word_carry (a : ℕ) [NeZero (a - 2)] (ha : 4 ≤ a)
    (x : RWord (Fin (a - 2))) (k : ℕ) :
    ∃ (c : ℕ) (u v : RWord (Fin (a - 2))),
      (∀ j, j < c → x (k + j) = .high) ∧
      u = flipAt (Finset.Ico k (k + c)) x ∧
      hDist u v ≤ 1 ∧
      wordIntegerEquiv a ha v = wordIntegerEquiv a ha x + (a : ℤ) ^ k := by
  obtain ⟨c, ud, vd, hrun, hstop, hu, hv, hval⟩ :=
    digit_carry a ha (wordToDigits a ha x) k
  let u := digitsToWord a ha ud
  let v := digitsToWord a ha vd
  have hhigh : ∀ j, j < c → x (k + j) = .high := by
    intro j hj
    apply letterValue_injective a ha
    exact hrun j hj
  refine ⟨c, u, v, hhigh, ?_, ?_, ?_⟩
  · ext i
    apply letterValue_injective a ha
    change letterValue a (digitsToWord a ha ud i) =
      letterValue a (flipAt (Finset.Ico k (k + c)) x i)
    rw [letterValue_digitsToWord, hu, flipAt_apply]
    by_cases hi : k ≤ i ∧ i < k + c
    · have hir : i = k + (i - k) := by omega
      have hxi : x i = .high := by
        rw [hir]
        exact hhigh (i - k) (by omega)
      simp [Finset.mem_Ico, hi, hxi, Letter.flip, letterValue]
    · simp [Finset.mem_Ico, hi]
  · apply hDist_le_of_agree_off u v {k + c}
    intro i hi
    have hn : i ≠ k + c := by simpa using hi
    change letterEncode a (ud.val i) = letterEncode a (vd.val i)
    rw [hv]
    simp [Finsupp.update_apply, hn]
  · simpa only [v, wordIntegerEquiv_apply, wordToDigits_toWord] using hval

def transferRelativeSymm {α β : Type*} [Zero α] [Zero β] {K : ℕ}
    (e : RelativeEquiv α β K) : RelativeEquiv β α K :=
  ⟨e.val.symm, e.property.2.1, e.property.1, by
    intro x i
    have h := e.property.2.2.1 (e.val.symm x) i
    simpa using h.symm, by
    intro s x
    apply e.val.injective
    rw [e.val.apply_symm_apply, e.property.2.2.2, e.val.apply_symm_apply]⟩

def relativeIntegerEquiv (a b : ℕ) [NeZero (a - 2)] [NeZero (b - 2)]
    (ha : 4 ≤ a) (hb : 4 ≤ b) {K : ℕ}
    (e : RelativeEquiv (Fin (a - 2)) (Fin (b - 2)) K) : ℤ ≃ ℤ :=
  (wordIntegerEquiv a ha).symm.trans (e.val.trans (wordIntegerEquiv b hb))

@[simp] theorem relativeIntegerEquiv_word (a b : ℕ) [NeZero (a - 2)] [NeZero (b - 2)]
    (ha : 4 ≤ a) (hb : 4 ≤ b) {K : ℕ}
    (e : RelativeEquiv (Fin (a - 2)) (Fin (b - 2)) K)
    (x : RWord (Fin (a - 2))) :
    relativeIntegerEquiv a b ha hb e (wordIntegerEquiv a ha x) =
      wordIntegerEquiv b hb (e.val x) := by
  change wordIntegerEquiv b hb
    (e.val ((wordIntegerEquiv a ha).symm (wordIntegerEquiv a ha x))) = _
  rw [(wordIntegerEquiv a ha).symm_apply_apply]

theorem high_of_frozen {α : Type*} (l : Letter α)
    (h : l.frozen = some true) : l = .high := by
  cases l <;> simp_all [Letter.frozen]

theorem relativeIntegerEquiv_forward (a b : ℕ) [NeZero (a - 2)] [NeZero (b - 2)]
    (ha : 4 ≤ a) (hb : 4 ≤ b) {K : ℕ}
    (e : RelativeEquiv (Fin (a - 2)) (Fin (b - 2)) K) (z t : ℤ) :
    wordDist b (relativeIntegerEquiv a b ha hb e z)
      (relativeIntegerEquiv a b ha hb e t) ≤
      (2 + K * (b - 1)) * wordDist a z t := by
  apply wordDist_le_of_pow_bound
  intro z k
  let x := (wordIntegerEquiv a ha).symm z
  obtain ⟨c, u, v, hrun, hu, huv, hval⟩ := word_carry a ha x k
  have hx : wordIntegerEquiv a ha x = z := (wordIntegerEquiv a ha).apply_symm_apply z
  have hv : wordIntegerEquiv a ha v = z + (a : ℤ) ^ k := by simpa [hx] using hval
  have hehigh : ∀ j, j < c → e.val x (k + j) = .high := by
    intro j hj
    apply high_of_frozen
    rw [e.property.2.2.1, hrun j hj]
    rfl
  have hflip : e.val u = flipAt (Finset.Ico k (k + c)) (e.val x) := by
    rw [hu, e.property.2.2.2]
  have hlong : wordDist b (wordIntegerEquiv b hb (e.val x))
      (wordIntegerEquiv b hb (e.val u)) ≤ 2 := by
    rw [hflip, wordInteger_flip_run b hb _ k c hehigh]
    unfold wordDist
    have he : wordIntegerEquiv b hb (e.val x) + (b : ℤ) ^ k -
        (b : ℤ) ^ (k + c) - wordIntegerEquiv b hb (e.val x) =
        (b : ℤ) ^ k - (b : ℤ) ^ (k + c) := by ring
    rw [he]
    exact wordLength_sub_pow_le b k (k + c)
  have hshort : wordDist b (wordIntegerEquiv b hb (e.val u))
      (wordIntegerEquiv b hb (e.val v)) ≤ K * (b - 1) := by
    have hd : hDist (e.val u) (e.val v) ≤ K := by
      have h := (e.property.1 u v).trans (Nat.mul_le_mul_left K huv)
      simpa using h
    exact (wordInteger_hamming_bound b hb _ _).trans
      (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (b - 1) hd)
  have hbound := (wordDist_triangle b
    (wordIntegerEquiv b hb (e.val x))
    (wordIntegerEquiv b hb (e.val u))
    (wordIntegerEquiv b hb (e.val v))).trans (Nat.add_le_add hlong hshort)
  rw [← relativeIntegerEquiv_word a b ha hb e x,
    ← relativeIntegerEquiv_word a b ha hb e v, hx, hv] at hbound
  exact hbound

theorem relativeIntegerEquiv_symm (a b : ℕ) [NeZero (a - 2)] [NeZero (b - 2)]
    (ha : 4 ≤ a) (hb : 4 ≤ b) {K : ℕ}
    (e : RelativeEquiv (Fin (a - 2)) (Fin (b - 2)) K) :
    (relativeIntegerEquiv a b ha hb e).symm =
      relativeIntegerEquiv b a hb ha (transferRelativeSymm e) := by
  rfl

theorem relativeIntegerEquiv_reverse (a b : ℕ) [NeZero (a - 2)] [NeZero (b - 2)]
    (ha : 4 ≤ a) (hb : 4 ≤ b) {K : ℕ}
    (e : RelativeEquiv (Fin (a - 2)) (Fin (b - 2)) K) (z t : ℤ) :
    wordDist a z t ≤ (2 + K * (a - 1)) *
      wordDist b (relativeIntegerEquiv a b ha hb e z)
        (relativeIntegerEquiv a b ha hb e t) := by
  have h := relativeIntegerEquiv_forward b a hb ha (transferRelativeSymm e)
    (relativeIntegerEquiv a b ha hb e z) (relativeIntegerEquiv a b ha hb e t)
  rw [← relativeIntegerEquiv_symm a b ha hb e] at h
  simpa using h

theorem relative_integer_transfer (a b : ℕ) [NeZero (a - 2)] [NeZero (b - 2)]
    (ha : 4 ≤ a) (hb : 4 ≤ b) {K : ℕ}
    (e : RelativeEquiv (Fin (a - 2)) (Fin (b - 2)) K) :
    ∃ f : ℤ ≃ ℤ,
      (∀ z t, wordDist b (f z) (f t) ≤ (2 + K * (b - 1)) * wordDist a z t) ∧
      (∀ z t, wordDist a z t ≤ (2 + K * (a - 1)) * wordDist b (f z) (f t)) :=
  ⟨relativeIntegerEquiv a b ha hb e,
    relativeIntegerEquiv_forward a b ha hb e,
    relativeIntegerEquiv_reverse a b ha hb e⟩

end
end Nathanson

#print axioms Nathanson.digitWordEquivR
#print axioms Nathanson.word_carry
#print axioms Nathanson.relative_integer_transfer
