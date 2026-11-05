import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Finite signed digit expansions

Digits for base a lie in the complete residue interval [-1, a - 2].
This file concerns ordinary integer values, not the Hamming or word metrics.
-/

namespace Nathanson

noncomputable section

def DigitWord (a : ℕ) :=
  {x : ℕ →₀ ℤ // ∀ i, -1 ≤ x i ∧ x i ≤ (a : ℤ) - 2}

def digitEval (a : ℕ) (x : ℕ →₀ ℤ) : ℤ :=
  x.sum fun i z => z * (a : ℤ) ^ i

def decode {a : ℕ} (x : DigitWord a) : ℤ := digitEval a x.val

def digitShift (x : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  x.mapDomain Nat.succ

def digitTail (x : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  x.comapDomain Nat.succ Nat.succ_injective.injOn

@[simp] theorem digitShift_zero (x : ℕ →₀ ℤ) : digitShift x 0 = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  simp

@[simp] theorem digitShift_succ (x : ℕ →₀ ℤ) (i : ℕ) :
    digitShift x (i + 1) = x i := by
  exact Finsupp.mapDomain_apply Nat.succ_injective x i

@[simp] theorem digitTail_apply (x : ℕ →₀ ℤ) (i : ℕ) :
    digitTail x i = x (i + 1) := by
  rfl

@[simp] theorem digitEval_zero (a : ℕ) : digitEval a 0 = 0 := by
  simp [digitEval]

theorem digitEval_add (a : ℕ) (x y : ℕ →₀ ℤ) :
    digitEval a (x + y) = digitEval a x + digitEval a y := by
  apply Finsupp.sum_add_index'
  · intro i; simp
  · intro i z w; exact add_mul z w _

theorem digitEval_sub (a : ℕ) (x y : ℕ →₀ ℤ) :
    digitEval a (x - y) = digitEval a x - digitEval a y := by
  have h := digitEval_add a (x - y) y
  rw [sub_add_cancel] at h
  omega

@[simp] theorem digitEval_single (a i : ℕ) (z : ℤ) :
    digitEval a (Finsupp.single i z) = z * (a : ℤ) ^ i := by
  simp [digitEval]

theorem digitEval_shift (a : ℕ) (x : ℕ →₀ ℤ) :
    digitEval a (digitShift x) = (a : ℤ) * digitEval a x := by
  unfold digitEval digitShift
  rw [Finsupp.sum_mapDomain_index (fun i => by simp)
    (fun i z w => add_mul z w _)]
  simp only [Nat.succ_eq_add_one, pow_succ, ← mul_assoc]
  rw [← Finsupp.sum_mul]
  ring

theorem digit_cons_tail (x : ℕ →₀ ℤ) :
    Finsupp.single 0 (x 0) + digitShift (digitTail x) = x := by
  ext i
  cases i with
  | zero => simp
  | succ i => simp

theorem digitEval_head_tail (a : ℕ) (x : ℕ →₀ ℤ) :
    digitEval a x = x 0 + (a : ℤ) * digitEval a (digitTail x) := by
  conv_lhs => rw [← digit_cons_tail x]
  rw [digitEval_add, digitEval_single, digitEval_shift]
  simp

def digitWordTail {a : ℕ} (x : DigitWord a) : DigitWord a :=
  ⟨digitTail x.val, fun i => x.property (i + 1)⟩

def digitWordZero (a : ℕ) (ha : 4 ≤ a) : DigitWord a :=
  ⟨0, fun i => by simp only [Finsupp.coe_zero, Pi.zero_apply]; omega⟩

def digitWordCons {a : ℕ} (d : ℤ) (hd : -1 ≤ d ∧ d ≤ (a : ℤ) - 2)
    (x : DigitWord a) : DigitWord a :=
  ⟨Finsupp.single 0 d + digitShift x.val, by
    intro i
    cases i with
    | zero => simpa using hd
    | succ i => simpa using x.property i⟩

@[simp] theorem decode_zero (a : ℕ) (ha : 4 ≤ a) :
    decode (digitWordZero a ha) = 0 := by
  exact digitEval_zero a

theorem decode_cons {a : ℕ} (d : ℤ) (hd : -1 ≤ d ∧ d ≤ (a : ℤ) - 2)
    (x : DigitWord a) :
    decode (digitWordCons d hd x) = d + (a : ℤ) * decode x := by
  unfold decode digitWordCons
  rw [digitEval_add, digitEval_single, digitEval_shift]
  simp

theorem digit_quotient_natAbs_lt (a : ℕ) (ha : 4 ≤ a) (z : ℤ) (hz : z ≠ 0) :
    ((z + 1) / (a : ℤ)).natAbs < z.natAbs := by
  have hap : (0 : ℤ) < a := by omega
  have ha4 : (4 : ℤ) ≤ a := by omega
  by_cases hp : 0 ≤ z
  · have hz1 : (1 : ℤ) ≤ z := by omega
    have hq0 : 0 ≤ (z + 1) / (a : ℤ) :=
      Int.ediv_nonneg (by omega) (by omega)
    apply Int.natAbs_lt_natAbs_of_nonneg_of_lt hq0
    apply (Int.ediv_lt_iff_lt_mul hap).2
    nlinarith
  · have hzn : z ≤ -1 := by omega
    have hq0 : (z + 1) / (a : ℤ) ≤ 0 :=
      Int.ediv_nonpos_of_nonpos_of_neg (by omega) hap
    have hq : z < (z + 1) / (a : ℤ) := by
      have hle : z + 1 ≤ (z + 1) / (a : ℤ) := by
        apply (Int.le_ediv_iff_mul_le hap).2
        nlinarith
      omega
    simpa only [Int.natAbs_neg] using
      (Int.natAbs_lt_natAbs_of_nonneg_of_lt
        (a := -((z + 1) / (a : ℤ))) (b := -z) (by omega) (by omega))

theorem decode_surjective (a : ℕ) (ha : 4 ≤ a) :
    Function.Surjective (@decode a) := by
  have main : ∀ N : ℕ, ∀ z : ℤ, z.natAbs = N →
      ∃ x : DigitWord a, decode x = z := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro z hzN
      by_cases hz : z = 0
      · subst z
        exact ⟨digitWordZero a ha, decode_zero a ha⟩
      · let q : ℤ := (z + 1) / (a : ℤ)
        let d : ℤ := (z + 1) % (a : ℤ) - 1
        have hap : (0 : ℤ) < a := by omega
        have hlt : q.natAbs < N := by
          rw [← hzN]
          exact digit_quotient_natAbs_lt a ha z hz
        obtain ⟨x, hx⟩ := ih q.natAbs hlt q rfl
        have hd : -1 ≤ d ∧ d ≤ (a : ℤ) - 2 := by
          have h0 := Int.emod_nonneg (z + 1) (ne_of_gt hap)
          have h1 := Int.emod_lt_of_pos (z + 1) hap
          dsimp [d]
          omega
        refine ⟨digitWordCons d hd x, ?_⟩
        rw [decode_cons, hx]
        have h := Int.emod_add_mul_ediv (z + 1) (a : ℤ)
        dsimp [d, q]
        nlinarith
  intro z
  exact main z.natAbs z rfl

theorem digit_head_eq (a : ℕ) (ha : 4 ≤ a) (x y : DigitWord a)
    (h : decode x = decode y) : x.val 0 = y.val 0 := by
  have hap : (0 : ℤ) < a := by omega
  have hx0 : 0 ≤ x.val 0 + 1 := by have := (x.property 0).1; omega
  have hy0 : 0 ≤ y.val 0 + 1 := by have := (y.property 0).1; omega
  have hxa : x.val 0 + 1 < (a : ℤ) := by have := (x.property 0).2; omega
  have hya : y.val 0 + 1 < (a : ℤ) := by have := (y.property 0).2; omega
  have hx : (decode x + 1) % (a : ℤ) = x.val 0 + 1 := by
    unfold decode
    rw [digitEval_head_tail]
    have he : x.val 0 + (a : ℤ) * digitEval a (digitTail x.val) + 1 =
        (x.val 0 + 1) + (a : ℤ) * digitEval a (digitTail x.val) := by ring
    rw [he, Int.add_emod]
    simp [Int.emod_eq_of_lt hx0 hxa]
  have hy : (decode y + 1) % (a : ℤ) = y.val 0 + 1 := by
    unfold decode
    rw [digitEval_head_tail]
    have he : y.val 0 + (a : ℤ) * digitEval a (digitTail y.val) + 1 =
        (y.val 0 + 1) + (a : ℤ) * digitEval a (digitTail y.val) := by ring
    rw [he, Int.add_emod]
    simp [Int.emod_eq_of_lt hy0 hya]
  rw [h] at hx
  omega

theorem digit_tail_decode_eq (a : ℕ) (ha : 4 ≤ a) (x y : DigitWord a)
    (h : decode x = decode y) :
    decode (digitWordTail x) = decode (digitWordTail y) := by
  have hhead := digit_head_eq a ha x y h
  change digitEval a x.val = digitEval a y.val at h
  rw [digitEval_head_tail a x.val, digitEval_head_tail a y.val] at h
  change digitEval a (digitTail x.val) = digitEval a (digitTail y.val)
  have hap : (0 : ℤ) < a := by omega
  apply mul_left_cancel₀ (ne_of_gt hap)
  omega

theorem decode_injective_bounded (a : ℕ) (ha : 4 ≤ a) (N : ℕ) :
    ∀ x y : DigitWord a,
      (∀ i, N ≤ i → x.val i = 0) →
      (∀ i, N ≤ i → y.val i = 0) →
      decode x = decode y → x = y := by
  induction N with
  | zero =>
    intro x y hx hy h
    apply Subtype.ext
    ext i
    rw [hx i (Nat.zero_le i), hy i (Nat.zero_le i)]
  | succ N ih =>
    intro x y hx hy h
    have hhead := digit_head_eq a ha x y h
    have htail := ih (digitWordTail x) (digitWordTail y)
      (fun i hi => hx (i + 1) (by omega))
      (fun i hi => hy (i + 1) (by omega))
      (digit_tail_decode_eq a ha x y h)
    apply Subtype.ext
    ext i
    cases i with
    | zero => exact hhead
    | succ i =>
      have he := congrArg (fun w : DigitWord a => w.val i) htail
      exact he

theorem decode_injective (a : ℕ) (ha : 4 ≤ a) :
    Function.Injective (@decode a) := by
  intro x y h
  let s := x.val.support ∪ y.val.support
  let N := s.sup id + 1
  apply decode_injective_bounded a ha N x y
  · intro i hi
    by_contra hn
    have hm : i ∈ s := Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hn)
    have hb : i ≤ s.sup id := Finset.le_sup (f := id) hm
    omega
  · intro i hi
    by_contra hn
    have hm : i ∈ s := Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hn)
    have hb : i ≤ s.sup id := Finset.le_sup (f := id) hm
    omega
  · exact h

theorem decode_bijective (a : ℕ) (ha : 4 ≤ a) :
    Function.Bijective (@decode a) :=
  ⟨decode_injective a ha, decode_surjective a ha⟩

def digitEquiv (a : ℕ) (ha : 4 ≤ a) : DigitWord a ≃ ℤ :=
  Equiv.ofBijective decode (decode_bijective a ha)

@[simp] theorem digitEquiv_apply (a : ℕ) (ha : 4 ≤ a) (x : DigitWord a) :
    digitEquiv a ha x = decode x := rfl

@[simp] theorem decode_digitEquiv_symm (a : ℕ) (ha : 4 ≤ a) (z : ℤ) :
    decode ((digitEquiv a ha).symm z) = z :=
  (digitEquiv a ha).apply_symm_apply z

theorem digitEval_update (a : ℕ) (x : ℕ →₀ ℤ) (i : ℕ) (z : ℤ) :
    digitEval a (x.update i z) = digitEval a x + (z - x i) * (a : ℤ) ^ i := by
  have h := Finsupp.sum_update_add x i z (fun j w => w * (a : ℤ) ^ j)
    (fun j => by simp) (fun j u v => add_mul u v _)
  change digitEval a (x.update i z) + x i * (a : ℤ) ^ i =
    digitEval a x + z * (a : ℤ) ^ i at h
  nlinarith

/-- Replace a finite interval starting at k with the minimum digit. -/
def digitFlip (x : ℕ →₀ ℤ) (k : ℕ) : ℕ → (ℕ →₀ ℤ)
  | 0 => x
  | c + 1 => (digitFlip x k c).update (k + c) (-1)

theorem digitFlip_apply (x : ℕ →₀ ℤ) (k c i : ℕ) :
    digitFlip x k c i = if k ≤ i ∧ i < k + c then -1 else x i := by
  induction c with
  | zero => simp [digitFlip]
  | succ c ih =>
    by_cases hi : i = k + c
    · subst i
      simp [digitFlip]
    · have hiff : (k ≤ i ∧ i < k + (c + 1)) ↔ (k ≤ i ∧ i < k + c) := by omega
      simp [digitFlip, Finsupp.update_apply, hi, ih, hiff]

def digitWordFlip {a : ℕ} (ha : 4 ≤ a) (x : DigitWord a) (k c : ℕ) :
    DigitWord a :=
  ⟨digitFlip x.val k c, by
    intro i
    rw [digitFlip_apply]
    split
    · constructor <;> omega
    · exact x.property i⟩

theorem digitEval_flip (a : ℕ) (x : ℕ →₀ ℤ) (k c : ℕ)
    (hrun : ∀ j, j < c → x (k + j) = (a : ℤ) - 2) :
    digitEval a (digitFlip x k c) =
      digitEval a x + (a : ℤ) ^ k - (a : ℤ) ^ (k + c) := by
  induction c with
  | zero => simp [digitFlip]
  | succ c ih =>
    rw [digitFlip, digitEval_update, ih (fun j hj => hrun j (by omega))]
    rw [digitFlip_apply]
    have hc : ¬(k ≤ k + c ∧ k + c < k + c) := by omega
    rw [if_neg hc, hrun c (Nat.lt_succ_self c)]
    rw [show k + (c + 1) = (k + c) + 1 by omega, pow_succ]
    ring

theorem exists_first_nonmax (a : ℕ) (ha : 4 ≤ a) (x : DigitWord a) (k : ℕ) :
    ∃ c : ℕ, x.val (k + c) < (a : ℤ) - 2 ∧
      ∀ j, j < c → x.val (k + j) = (a : ℤ) - 2 := by
  have hex : ∃ c : ℕ, x.val (k + c) ≠ (a : ℤ) - 2 := by
    let c := x.val.support.sup id + 1
    have hz : x.val (k + c) = 0 := by
      by_contra hn
      have hm := Finsupp.mem_support_iff.mpr hn
      have hb : k + c ≤ x.val.support.sup id := Finset.le_sup (f := id) hm
      dsimp [c] at hb
      omega
    refine ⟨c, ?_⟩
    rw [hz]
    omega
  let c := Nat.find hex
  refine ⟨c, ?_, ?_⟩
  · have hn := Nat.find_spec hex
    have hu := (x.property (k + c)).2
    change x.val (k + c) ≠ (a : ℤ) - 2 at hn
    omega
  · intro j hj
    exact not_not.mp (Nat.find_min hex hj)

/-- An exact finite carry decomposition. The intermediate word changes only
the maximal run to minimum digits; the final word changes one endpoint. -/
theorem digit_carry (a : ℕ) (ha : 4 ≤ a) (x : DigitWord a) (k : ℕ) :
    ∃ (c : ℕ) (u v : DigitWord a),
      (∀ j, j < c → x.val (k + j) = (a : ℤ) - 2) ∧
      x.val (k + c) < (a : ℤ) - 2 ∧
      (∀ i, u.val i = if k ≤ i ∧ i < k + c then -1 else x.val i) ∧
      v.val = u.val.update (k + c) (u.val (k + c) + 1) ∧
      decode v = decode x + (a : ℤ) ^ k := by
  obtain ⟨c, hstop, hrun⟩ := exists_first_nonmax a ha x k
  let u := digitWordFlip ha x k c
  have hu : ∀ i, u.val i = if k ≤ i ∧ i < k + c then -1 else x.val i :=
    digitFlip_apply x.val k c
  have hend : u.val (k + c) = x.val (k + c) := by simp [hu]
  have hvbound : ∀ i,
      -1 ≤ (u.val.update (k + c) (u.val (k + c) + 1)) i ∧
      (u.val.update (k + c) (u.val (k + c) + 1)) i ≤ (a : ℤ) - 2 := by
    intro i
    by_cases hi : i = k + c
    · subst i
      simp only [Finsupp.update_apply]
      rw [hend]
      have hlo := (x.property (k + c)).1
      constructor <;> omega
    · simpa [Finsupp.update_apply, hi] using u.property i
  let v : DigitWord a := ⟨u.val.update (k + c) (u.val (k + c) + 1), hvbound⟩
  refine ⟨c, u, v, hrun, hstop, hu, rfl, ?_⟩
  change digitEval a (u.val.update (k + c) (u.val (k + c) + 1)) =
    decode x + (a : ℤ) ^ k
  rw [digitEval_update]
  have he : digitEval a u.val = decode x + (a : ℤ) ^ k - (a : ℤ) ^ (k + c) :=
    digitEval_flip a x.val k c hrun
  rw [he]
  ring

end

end Nathanson

#print axioms Nathanson.decode_bijective
#print axioms Nathanson.digitEquiv
#print axioms Nathanson.digit_carry
