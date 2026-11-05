import Nathanson.MaskModel
import Nathanson.Composition
import Nathanson.Blocks

/-! # Lifting editable-data equivalences to marked words -/

noncomputable section

namespace Nathanson

variable {α β : Type*} [Zero α] [Zero β]

/-- An equivalence on editable data for each fixed finite frozen mask. -/
abbrev MaskFamily (α β : Type*) [Zero α] [Zero β] :=
  ∀ F : Finset ℕ, ({j : ℕ // j ∉ F} →₀ α) ≃ ({j : ℕ // j ∉ F} →₀ β)

def maskedDataEquiv (e : MaskFamily α β) : Masked α ≃ Masked β :=
  Equiv.sigmaCongrRight fun F => Equiv.prodCongr (Equiv.refl (F → Bool)) (e F)

def liftMasked (e : MaskFamily α β) : RWord α ≃ RWord β :=
  maskEquiv.trans ((maskedDataEquiv e).trans maskEquiv.symm)

theorem liftMasked_maskJoin (e : MaskFamily α β) (F : Finset ℕ) (labels : F → Bool)
    (data : {j : ℕ // j ∉ F} →₀ α) :
    liftMasked e (maskJoin F labels data) = maskJoin F labels (e F data) := by
  change maskEquiv.symm (maskedDataEquiv e (maskEncode (maskJoin F labels data))) = _
  rw [maskEncode_join (⟨F, labels, data⟩ : Masked α)]
  rfl

theorem liftMasked_symm_maskJoin (e : MaskFamily α β) (F : Finset ℕ)
    (labels : F → Bool) (data : {j : ℕ // j ∉ F} →₀ β) :
    (liftMasked e).symm (maskJoin F labels data) = maskJoin F labels ((e F).symm data) := by
  apply (liftMasked e).injective
  rw [Equiv.apply_symm_apply, liftMasked_maskJoin, Equiv.apply_symm_apply]

theorem liftMasked_frozen (e : MaskFamily α β) (x : RWord α) (i : ℕ) :
    (liftMasked e x i).frozen = (x i).frozen := by
  classical
  obtain ⟨⟨F, labels, data⟩, rfl⟩ := maskEquiv.symm.surjective x
  change (liftMasked e (maskJoin F labels data) i).frozen = (maskJoin F labels data i).frozen
  rw [liftMasked_maskJoin]
  by_cases h : i ∈ F
  · simp only [maskJoin_apply_mem _ _ _ _ h]
    cases labels ⟨i, h⟩ <;> rfl
  · simp [h]

theorem liftMasked_flip (e : MaskFamily α β) (s : Finset ℕ) (x : RWord α) :
    liftMasked e (flipAt s x) = flipAt s (liftMasked e x) := by
  classical
  obtain ⟨⟨F, labels, data⟩, rfl⟩ := maskEquiv.symm.surjective x
  change liftMasked e (flipAt s (maskJoin F labels data)) =
    flipAt s (liftMasked e (maskJoin F labels data))
  rw [flipAt_maskJoin, liftMasked_maskJoin, liftMasked_maskJoin, flipAt_maskJoin]

/-- One-coordinate corrections in each editable block remain one-coordinate
corrections after reinserting all frozen letters. -/
theorem liftMasked_forward_move (e : MaskFamily α (α × β)) (block : ℕ → ℕ)
    (hm : ∀ F (data : {j : ℕ // j ∉ F} →₀ α) i,
      ∃ j, ∀ k (hk : k ∉ F), block k = i → k ≠ j →
        (e F data ⟨k, hk⟩).1 = data ⟨k, hk⟩)
    (x : RWord α) (i : ℕ) :
    ∃ j, ∀ k, block k = i → k ≠ j → firstWord (liftMasked e x) k = x k := by
  classical
  obtain ⟨⟨F, labels, data⟩, rfl⟩ := maskEquiv.symm.surjective x
  obtain ⟨j, hj⟩ := hm F data i
  refine ⟨j, ?_⟩
  intro k hk hkj
  change firstWord (liftMasked e (maskJoin F labels data)) k = maskJoin F labels data k
  rw [liftMasked_maskJoin, firstWord_apply]
  by_cases hF : k ∈ F
  · simp only [maskJoin_apply_mem F labels (e F data) k hF,
      maskJoin_apply_mem F labels data k hF]
    cases labels ⟨k, hF⟩ <;> rfl
  · simp only [maskJoin_apply_notMem F labels (e F data) k hF,
      maskJoin_apply_notMem F labels data k hF, firstLetter]
    exact congrArg Letter.edit (hj k hF hk hkj)

theorem liftMasked_inverse_move (e : MaskFamily α (α × β)) (block : ℕ → ℕ)
    (hm : ∀ F (data : {j : ℕ // j ∉ F} →₀ (α × β)) i,
      ∃ j, ∀ k (hk : k ∉ F), block k = i → k ≠ j →
        ((e F).symm data) ⟨k, hk⟩ = (data ⟨k, hk⟩).1)
    (x : RWord (α × β)) (i : ℕ) :
    ∃ j, ∀ k, block k = i → k ≠ j → (liftMasked e).symm x k = firstWord x k := by
  classical
  obtain ⟨⟨F, labels, data⟩, rfl⟩ := maskEquiv.symm.surjective x
  obtain ⟨j, hj⟩ := hm F data i
  refine ⟨j, ?_⟩
  intro k hk hkj
  change (liftMasked e).symm (maskJoin F labels data) k = firstWord (maskJoin F labels data) k
  rw [liftMasked_symm_maskJoin, firstWord_apply]
  by_cases hF : k ∈ F
  · simp only [maskJoin_apply_mem F labels ((e F).symm data) k hF,
      maskJoin_apply_mem F labels data k hF]
    cases labels ⟨k, hF⟩ <;> rfl
  · simp only [maskJoin_apply_notMem F labels ((e F).symm data) k hF,
      maskJoin_apply_notMem F labels data k hF, firstLetter]
    exact congrArg Letter.edit (hj k hF hk hkj)

theorem maskJoin_mem_iff_of_eq (F G : Finset ℕ) (l : F → Bool) (l' : G → Bool)
    (d : {j : ℕ // j ∉ F} →₀ α) (d' : {j : ℕ // j ∉ G} →₀ α)
    (i : ℕ) (h : maskJoin F l d i = maskJoin G l' d' i) :
    i ∈ F ↔ i ∈ G := by
  have hm : i ∈ frozenSet (maskJoin F l d) ↔ i ∈ frozenSet (maskJoin G l' d') := by
    simp only [mem_frozenSet]
    rw [h]
  simpa only [frozenSet_maskJoin] using hm

theorem maskJoin_data_eq_of_eq (F G : Finset ℕ) (l : F → Bool) (l' : G → Bool)
    (d : {j : ℕ // j ∉ F} →₀ α) (d' : {j : ℕ // j ∉ G} →₀ α)
    (i : ℕ) (hF : i ∉ F) (hG : i ∉ G)
    (h : maskJoin F l d i = maskJoin G l' d' i) : d ⟨i, hF⟩ = d' ⟨i, hG⟩ := by
  simpa only [maskJoin_apply_notMem _ _ _ _ hF, maskJoin_apply_notMem _ _ _ _ hG,
    Letter.edit.injEq] using h

/-- The precise raw-data forward locality condition. Its hypotheses mention
only one block, together with the activation status of its extra coordinate. -/
def MaskForwardLocal (e : MaskFamily α (α × β)) (block : ℕ → ℕ) : Prop :=
  ∀ F G (d : {j : ℕ // j ∉ F} →₀ α) (d' : {j : ℕ // j ∉ G} →₀ α) i,
    (∀ k, block k = i → (k ∈ F ↔ k ∈ G)) →
    (i ∈ F ↔ i ∈ G) →
    (∀ k (hF : k ∉ F) (hG : k ∉ G), block k = i → d ⟨k, hF⟩ = d' ⟨k, hG⟩) →
    (∀ k (hF : k ∉ F) (hG : k ∉ G), block k = i →
      (e F d ⟨k, hF⟩).1 = (e G d' ⟨k, hG⟩).1) ∧
    (∀ (hF : i ∉ F) (hG : i ∉ G), (e F d ⟨i, hF⟩).2 = (e G d' ⟨i, hG⟩).2)

def MaskInverseLocal (e : MaskFamily α (α × β)) (block : ℕ → ℕ) : Prop :=
  ∀ F G (d : {j : ℕ // j ∉ F} →₀ (α × β)) (d' : {j : ℕ // j ∉ G} →₀ (α × β)) i,
    (∀ k, block k = i → (k ∈ F ↔ k ∈ G)) →
    (i ∈ F ↔ i ∈ G) →
    (∀ k (hF : k ∉ F) (hG : k ∉ G), block k = i → d ⟨k, hF⟩ = d' ⟨k, hG⟩) →
    (∀ (hF : i ∉ F) (hG : i ∉ G), d ⟨i, hF⟩ = d' ⟨i, hG⟩) →
    ∀ k (hF : k ∉ F) (hG : k ∉ G), block k = i →
      ((e F).symm d) ⟨k, hF⟩ = ((e G).symm d') ⟨k, hG⟩

theorem liftMasked_forward_local (e : MaskFamily α (α × β)) (block : ℕ → ℕ)
    (hc : MaskForwardLocal e block) (x y : RWord α) (i : ℕ)
    (hb : BlockAgree block x y i) (hi : x i = y i) :
    (∀ k, block k = i → firstWord (liftMasked e x) k = firstWord (liftMasked e y) k) ∧
      extraWord (liftMasked e x) i = extraWord (liftMasked e y) i := by
  classical
  obtain ⟨⟨F, l, d⟩, rfl⟩ := maskEquiv.symm.surjective x
  obtain ⟨⟨G, l', d'⟩, rfl⟩ := maskEquiv.symm.surjective y
  change BlockAgree block (maskJoin F l d) (maskJoin G l' d') i at hb
  change maskJoin F l d i = maskJoin G l' d' i at hi
  have hm (k : ℕ) (hk : block k = i) :=
    maskJoin_mem_iff_of_eq F G l l' d d' k (hb k hk)
  have hmi := maskJoin_mem_iff_of_eq F G l l' d d' i hi
  have hd (k : ℕ) (hkF : k ∉ F) (hkG : k ∉ G) (hk : block k = i) :=
    maskJoin_data_eq_of_eq F G l l' d d' k hkF hkG (hb k hk)
  obtain ⟨ht, he⟩ := hc F G d d' i hm hmi hd
  constructor
  · intro k hk
    change firstWord (liftMasked e (maskJoin F l d)) k =
      firstWord (liftMasked e (maskJoin G l' d')) k
    rw [liftMasked_maskJoin, liftMasked_maskJoin, firstWord_apply, firstWord_apply]
    by_cases hkF : k ∈ F
    · have hkG := (hm k hk).mp hkF
      have hletters := hb k hk
      cases hl : l ⟨k, hkF⟩ <;> cases hl' : l' ⟨k, hkG⟩ <;>
        simp [hkF, hkG, hl, hl', firstLetter] at hletters ⊢
    · have hkG : k ∉ G := fun h => hkF ((hm k hk).mpr h)
      simp only [maskJoin_apply_notMem _ _ _ _ hkF, maskJoin_apply_notMem _ _ _ _ hkG,
        firstLetter]
      exact congrArg Letter.edit (ht k hkF hkG hk)
  · change extraWord (liftMasked e (maskJoin F l d)) i =
      extraWord (liftMasked e (maskJoin G l' d')) i
    rw [liftMasked_maskJoin, liftMasked_maskJoin, extraWord_apply, extraWord_apply]
    by_cases hiF : i ∈ F
    · have hiG := hmi.mp hiF
      cases hl : l ⟨i, hiF⟩ <;> cases hl' : l' ⟨i, hiG⟩ <;>
        simp [hiF, hiG, hl, hl', extraLetter]
    · have hiG : i ∉ G := fun h => hiF (hmi.mpr h)
      simpa only [maskJoin_apply_notMem _ _ _ _ hiF, maskJoin_apply_notMem _ _ _ _ hiG,
        extraLetter] using he hiF hiG

theorem liftMasked_inverse_local (e : MaskFamily α (α × β)) (block : ℕ → ℕ)
    (hc : MaskInverseLocal e block) (x y : RWord (α × β)) (i : ℕ)
    (hb : BlockAgree block x y i) (hi : x i = y i) :
    ∀ k, block k = i → (liftMasked e).symm x k = (liftMasked e).symm y k := by
  classical
  obtain ⟨⟨F, l, d⟩, rfl⟩ := maskEquiv.symm.surjective x
  obtain ⟨⟨G, l', d'⟩, rfl⟩ := maskEquiv.symm.surjective y
  change BlockAgree block (maskJoin F l d) (maskJoin G l' d') i at hb
  change maskJoin F l d i = maskJoin G l' d' i at hi
  have hm (k : ℕ) (hk : block k = i) :=
    maskJoin_mem_iff_of_eq F G l l' d d' k (hb k hk)
  have hmi := maskJoin_mem_iff_of_eq F G l l' d d' i hi
  have hd (k : ℕ) (hkF : k ∉ F) (hkG : k ∉ G) (hk : block k = i) :=
    maskJoin_data_eq_of_eq F G l l' d d' k hkF hkG (hb k hk)
  have hdi (hiF : i ∉ F) (hiG : i ∉ G) :=
    maskJoin_data_eq_of_eq F G l l' d d' i hiF hiG hi
  have ht := hc F G d d' i hm hmi hd hdi
  intro k hk
  change (liftMasked e).symm (maskJoin F l d) k =
    (liftMasked e).symm (maskJoin G l' d') k
  rw [liftMasked_symm_maskJoin, liftMasked_symm_maskJoin]
  by_cases hkF : k ∈ F
  · have hkG := (hm k hk).mp hkF
    have hletters := hb k hk
    cases hl : l ⟨k, hkF⟩ <;> cases hl' : l' ⟨k, hkG⟩ <;>
      simp [hkF, hkG, hl, hl'] at hletters ⊢
  · have hkG : k ∉ G := fun h => hkF ((hm k hk).mpr h)
    simp only [maskJoin_apply_notMem _ _ _ _ hkF, maskJoin_apply_notMem _ _ _ _ hkG]
    exact congrArg Letter.edit (ht k hkF hkG hk)

theorem blockSet_eq_of_mask_agree (F G : Finset ℕ) (i : ℕ)
    (hm : ∀ k, block k = i → (k ∈ F ↔ k ∈ G)) : blockSet F i = blockSet G i := by
  ext k
  constructor
  · rintro ⟨hk, hF⟩
    exact ⟨hk, fun hG => hF ((hm k hk).mpr hG)⟩
  · rintro ⟨hk, hG⟩
    exact ⟨hk, fun hF => hG ((hm k hk).mp hF)⟩

@[simp] theorem finsuppProd_first_apply {ι : Type*} (d : ι →₀ (α × β)) (j : ι) :
    ((finsuppProd α β) d).1 j = (d j).1 := rfl

@[simp] theorem finsuppProd_second_apply {ι : Type*} (d : ι →₀ (α × β)) (j : ι) :
    ((finsuppProd α β) d).2 j = (d j).2 := rfl

section Absorption

variable [Countable α] [Nontrivial α] [Countable β]

theorem maskedAbsorb_forward_local : MaskForwardLocal (maskedAbsorb α β) block := by
  classical
  intro F G d d' i hm hi hd
  have hE := blockSet_eq_of_mask_agree F G i hm
  have hc := localAbsorb_congr α β (blockSet F i) (blockSet G i)
    (blockSet_infinite F i) (blockSet_infinite G i) hE
    (splitBlocks F α d i) (splitBlocks G α d' i)
    (fun k hkF hkG => hd k hkF.2 hkG.2 hkF.1)
  by_cases hiF : i ∈ F
  · have hiG := hi.mp hiF
    constructor
    · intro k hkF hkG hki
      rw [maskedAbsorb_first, maskedAbsorb_first]
      subst i
      rw [localBlockEquiv_frozen α β F (block k) hiF,
        localBlockEquiv_frozen α β G (block k) hiG]
      exact hd k hkF hkG rfl
    · intro hF _
      exact (hF hiF).elim
  · have hiG : i ∉ G := fun h => hiF (hi.mpr h)
    constructor
    · intro k hkF hkG hki
      rw [maskedAbsorb_first, maskedAbsorb_first]
      subst i
      rw [localBlockEquiv_active_tail α β F (block k) hiF,
        localBlockEquiv_active_tail α β G (block k) hiG]
      exact hc.2 k ⟨rfl, hkF⟩ ⟨rfl, hkG⟩
    · intro hF hG
      rw [maskedAbsorb_second, maskedAbsorb_second,
        localBlockEquiv_active_extra α β F i hiF,
        localBlockEquiv_active_extra α β G i hiG]
      exact hc.1

theorem maskedAbsorb_inverse_local : MaskInverseLocal (maskedAbsorb α β) block := by
  classical
  intro F G d d' i hm hi hd hdi
  have hE := blockSet_eq_of_mask_agree F G i hm
  by_cases hiF : i ∈ F
  · have hiG := hi.mp hiF
    intro k hkF hkG hki
    rw [maskedAbsorb_symm_apply, maskedAbsorb_symm_apply]
    subst i
    rw [localBlockEquiv_symm_frozen α β F (block k) hiF,
      localBlockEquiv_symm_frozen α β G (block k) hiG]
    exact congrArg Prod.fst (hd k hkF hkG rfl)
  · have hiG : i ∉ G := fun h => hiF (hi.mpr h)
    have he : (extraFromWord F ((finsuppProd α β) d).2 i).1 =
        (extraFromWord G ((finsuppProd α β) d').2 i).1 := by
      simp only [extraFromWord_apply, Finsupp.extendDomain_apply,
        dif_pos hiF, dif_pos hiG, finsuppProd_second_apply]
      exact congrArg Prod.snd (hdi hiF hiG)
    have hc := localAbsorb_symm_congr α β (blockSet F i) (blockSet G i)
      (blockSet_infinite F i) (blockSet_infinite G i) hE _ _ he
      (splitBlocks F α ((finsuppProd α β) d).1 i)
      (splitBlocks G α ((finsuppProd α β) d').1 i)
      (fun k hkF hkG => congrArg Prod.fst (hd k hkF.2 hkG.2 hkF.1))
    intro k hkF hkG hki
    rw [maskedAbsorb_symm_apply, maskedAbsorb_symm_apply]
    subst i
    rw [localBlockEquiv_symm_active α β F (block k) hiF,
      localBlockEquiv_symm_active α β G (block k) hiG]
    exact hc k ⟨rfl, hkF⟩ ⟨rfl, hkG⟩

/-- Unconditional relative absorption: all cross-mask control follows from
the same local matching on equal editable sets, not from an extra hypothesis. -/
def relativeAbsorption (α β : Type*) [Zero α] [Countable α] [Nontrivial α]
    [Zero β] [Countable β] : RelativeAbsorption α β where
  equiv := liftMasked (maskedAbsorb α β)
  forward := forward_seven block _
    (liftMasked_forward_move _ block (maskedAbsorb_correction α β))
    (liftMasked_forward_local _ block maskedAbsorb_forward_local)
  backward := inverse_five block _
    (liftMasked_inverse_move _ block (maskedAbsorb_symm_correction α β))
    (liftMasked_inverse_local _ block maskedAbsorb_inverse_local)
  frozen := liftMasked_frozen _
  flip := liftMasked_flip _

end Absorption

end Nathanson

#print axioms Nathanson.maskedAbsorb_forward_local
#print axioms Nathanson.maskedAbsorb_inverse_local
#print axioms Nathanson.relativeAbsorption
