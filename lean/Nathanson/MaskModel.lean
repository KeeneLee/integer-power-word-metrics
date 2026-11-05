import Nathanson.Hamming

/-! # Exact decomposition of marked words by their finite frozen mask -/

noncomputable section

namespace Nathanson

variable {α : Type*} [Zero α]

@[simp] theorem edits_apply (x : RWord α) (j : ℕ) :
    edits x j = (x j).ordinary := rfl

/-- A finite frozen set, its high/low labels, and all editable data. -/
abbrev Masked (α : Type*) [Zero α] :=
  Σ F : Finset ℕ, (F → Bool) × ({j : ℕ // j ∉ F} →₀ α)

/-- Reassemble a marked word. This construction automatically has finite
support: the support is contained in the mask and the finite data support. -/
def maskJoin (F : Finset ℕ) (labels : F → Bool)
    (data : {j : ℕ // j ∉ F} →₀ α) : RWord α := by
  classical
  refine Finsupp.onFinset (F ∪ data.support.image Subtype.val)
    (fun j => if h : j ∈ F then
      (if labels ⟨j, h⟩ then Letter.high else Letter.low)
      else Letter.edit (data ⟨j, h⟩)) ?_
  intro j hj
  by_cases hF : j ∈ F
  · exact Finset.mem_union_left _ hF
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨⟨j, hF⟩, ?_, rfl⟩
    apply Finsupp.mem_support_iff.mpr
    intro hd
    apply hj
    simp [hF, hd]
    rfl

@[simp] theorem maskJoin_apply (F : Finset ℕ) (labels : F → Bool)
    (data : {j : ℕ // j ∉ F} →₀ α) (j : ℕ) :
    maskJoin F labels data j = if h : j ∈ F then
      (if labels ⟨j, h⟩ then Letter.high else Letter.low)
      else Letter.edit (data ⟨j, h⟩) := by
  classical
  rfl

@[simp] theorem maskJoin_apply_mem (F : Finset ℕ) (labels : F → Bool)
    (data : {j : ℕ // j ∉ F} →₀ α) (j : ℕ) (h : j ∈ F) :
    maskJoin F labels data j =
      (if labels ⟨j, h⟩ then Letter.high else Letter.low) := by
  simp [h]

@[simp] theorem maskJoin_apply_notMem (F : Finset ℕ) (labels : F → Bool)
    (data : {j : ℕ // j ∉ F} →₀ α) (j : ℕ) (h : j ∉ F) :
    maskJoin F labels data j = Letter.edit (data ⟨j, h⟩) := by
  simp [h]

@[simp] theorem frozenSet_maskJoin (F : Finset ℕ) (labels : F → Bool)
    (data : {j : ℕ // j ∉ F} →₀ α) :
    frozenSet (maskJoin F labels data) = F := by
  classical
  ext j
  by_cases h : j ∈ F
  · simp only [mem_frozenSet, maskJoin_apply_mem F labels data j h]
    cases labels ⟨j, h⟩ <;> simp [Letter.frozen, h]
  · simp [h]

/-- High is true and low is false; the value at an editable letter is
irrelevant when this function is restricted to the frozen mask. -/
def frozenLabel : Letter α → Bool
  | .high => true
  | .low => false
  | .edit _ => false

def maskEncode (x : RWord α) : Masked α :=
  ⟨frozenSet x, (fun j => frozenLabel (x j)),
    Finsupp.subtypeDomain (fun j => j ∉ frozenSet x) (edits x)⟩

@[simp] theorem maskEncode_fst (x : RWord α) :
    (maskEncode x).1 = frozenSet x := rfl

@[simp] theorem maskEncode_data (x : RWord α) (j : {j : ℕ // j ∉ frozenSet x}) :
    (maskEncode x).2.2 j = (x j).ordinary := rfl

theorem maskJoin_encode (x : RWord α) :
    maskJoin (maskEncode x).1 (maskEncode x).2.1 (maskEncode x).2.2 = x := by
  classical
  ext j
  by_cases h : j ∈ frozenSet x
  · have hf := (mem_frozenSet x j).mp h
    cases hx : x j with
    | edit a => simp [hx, Letter.frozen] at hf
    | high => simp [maskEncode, h, hx, frozenLabel]
    | low => simp [maskEncode, h, hx, frozenLabel]
  · have hf : (x j).frozen = none := by simpa using h
    cases hx : x j with
    | edit a => simp [maskEncode, h, hx, Letter.ordinary]
    | high => simp [hx, Letter.frozen] at hf
    | low => simp [hx, Letter.frozen] at hf

theorem maskJoin_injective : Function.Injective
    (fun p : Masked α => maskJoin p.1 p.2.1 p.2.2) := by
  classical
  rintro ⟨F, labels, data⟩ ⟨G, labels', data'⟩ h
  have hFG : F = G := by
    simpa using congrArg frozenSet h
  subst G
  have hl : labels = labels' := by
    funext j
    have hj := congrArg (fun x : RWord α => x j) h
    simp only [maskJoin_apply_mem F labels data j j.property,
      maskJoin_apply_mem F labels' data' j j.property] at hj
    cases h₁ : labels j <;> cases h₂ : labels' j <;>
      simp [h₁, h₂] at hj ⊢
  have hd : data = data' := by
    ext j
    have hj := congrArg (fun x : RWord α => x j) h
    simpa only [maskJoin_apply_notMem F labels data j j.property,
      maskJoin_apply_notMem F labels' data' j j.property, Letter.edit.injEq] using hj
  subst labels'
  subst data'
  rfl

theorem maskEncode_join (p : Masked α) :
    maskEncode (maskJoin p.1 p.2.1 p.2.2) = p := by
  apply maskJoin_injective
  exact maskJoin_encode _

/-- Exact marked-word decomposition, with an explicitly defined inverse. -/
def maskEquiv : RWord α ≃ Masked α where
  toFun := maskEncode
  invFun p := maskJoin p.1 p.2.1 p.2.2
  left_inv := maskJoin_encode
  right_inv := maskEncode_join

@[simp] theorem maskEquiv_apply (x : RWord α) : maskEquiv x = maskEncode x := rfl

@[simp] theorem maskEquiv_symm_apply (p : Masked α) :
    maskEquiv.symm p = maskJoin p.1 p.2.1 p.2.2 := rfl

/-- Editable output does not depend on any of the frozen high/low labels. -/
theorem edits_maskJoin_independent (F : Finset ℕ) (labels labels' : F → Bool)
    (data : {j : ℕ // j ∉ F} →₀ α) :
    edits (maskJoin F labels data) = edits (maskJoin F labels' data) := by
  classical
  ext j
  change (maskJoin F labels data j).ordinary = (maskJoin F labels' data j).ordinary
  by_cases h : j ∈ F
  · simp only [maskJoin_apply_mem F labels data j h,
      maskJoin_apply_mem F labels' data j h]
    cases labels ⟨j, h⟩ <;> cases labels' ⟨j, h⟩ <;> rfl
  · simp [h]

/-- Flipping frozen labels does not alter the editable data at any position. -/
@[simp] theorem edits_flipAt (s : Finset ℕ) (x : RWord α) :
    edits (flipAt s x) = edits x := by
  classical
  ext j
  change (flipAt s x j).ordinary = (x j).ordinary
  rw [flipAt_apply]
  by_cases h : j ∈ s
  · rw [if_pos h]
    cases x j <;> rfl
  · rw [if_neg h]

@[simp] theorem frozenSet_flipAt (s : Finset ℕ) (x : RWord α) :
    frozenSet (flipAt s x) = frozenSet x := by
  classical
  ext j
  simp only [mem_frozenSet, flipAt_apply]
  by_cases h : j ∈ s <;> simp only [h, if_true, if_false]
  cases x j <;> simp [Letter.flip, Letter.frozen]

theorem flipAt_maskJoin (s F : Finset ℕ) (labels : F → Bool)
    (data : {j : ℕ // j ∉ F} →₀ α) :
    flipAt s (maskJoin F labels data) =
      maskJoin F (fun j => if j.val ∈ s then !(labels j) else labels j) data := by
  classical
  ext j
  by_cases hF : j ∈ F
  · simp only [flipAt_apply, maskJoin_apply_mem F labels data j hF]
    by_cases hs : j ∈ s <;> cases hl : labels ⟨j, hF⟩ <;>
      simp [hF, hs, hl, Letter.flip]
  · simp [hF, Letter.flip]

end Nathanson

#print axioms Nathanson.maskEquiv
#print axioms Nathanson.frozenSet_maskJoin
#print axioms Nathanson.edits_maskJoin_independent
#print axioms Nathanson.flipAt_maskJoin
