module

public import Nathanson.Absorption
public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.Data.Nat.Pairing

/-! Fixed-mask absorption. All local choices depend only on the editable set. -/

@[expose] public section
namespace Nathanson

universe u v

abbrev FWord (F : Finset ℕ) (A : Type u) [Zero A] := {j : ℕ // j ∉ F} →₀ A

def block (j : ℕ) : ℕ := (Nat.unpair j).1

abbrev blockSet (F : Finset ℕ) (i : ℕ) : Set ℕ := {j | block j = i ∧ j ∉ F}

theorem blockSet_infinite (F : Finset ℕ) (i : ℕ) : (blockSet F i).Infinite := by
  have h : Set.Infinite {j | block j = i} := by
    apply Set.infinite_of_injective_forall_mem (f := Nat.pair i)
    · intro m n h
      have := congrArg (fun j => (Nat.unpair j).2) h
      simpa using this
    · intro n
      simp [block]
  exact h.sdiff F.finite_toSet

noncomputable def editableSigma (F : Finset ℕ) :
    {j : ℕ // j ∉ F} ≃ Σ i, blockSet F i where
  toFun j := ⟨block j.1, ⟨j.1, rfl, j.2⟩⟩
  invFun j := ⟨j.2.1, j.2.2.2⟩
  left_inv j := rfl
  right_inv := by
    rintro ⟨i, j, hij, hj⟩
    subst i
    rfl

noncomputable def splitBlocks (F : Finset ℕ) (A : Type u) [Zero A] :
    FWord F A ≃ Π₀ i, (blockSet F i →₀ A) :=
  (Finsupp.equivCongrLeft (editableSigma F)).trans sigmaFinsuppEquivDFinsupp

@[simp] theorem splitBlocks_apply (F : Finset ℕ) {A : Type u} [Zero A]
    (x : FWord F A) (i : ℕ) (j : blockSet F i) :
    splitBlocks F A x i j = x ⟨j.1, j.2.2⟩ := rfl

@[simp] theorem splitBlocks_symm_apply (F : Finset ℕ) {A : Type u} [Zero A]
    (x : Π₀ i, (blockSet F i →₀ A)) (j : {j : ℕ // j ∉ F}) :
    (splitBlocks F A).symm x j = x (block j.1) ⟨j.1, rfl, j.2⟩ := rfl

@[simp] theorem splitBlocks_zero (F : Finset ℕ) (A : Type u) [Zero A] :
    splitBlocks F A 0 = 0 := by ext i j; rfl

/-- Pointwise equivalences of pointed types act on dependent finite support. -/
noncomputable def dfinsuppCongr {ι : Type*} {C D : ι → Type*}
    [∀ i, Zero (C i)] [∀ i, Zero (D i)]
    (e : ∀ i, C i ≃ D i) (he : ∀ i, e i 0 = 0) :
    (Π₀ i, C i) ≃ (Π₀ i, D i) where
  toFun := DFinsupp.mapRange (fun i => e i) he
  invFun := DFinsupp.mapRange (fun i => (e i).symm)
    (fun i => (e i).injective (by simp [he i]))
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

@[simp] theorem dfinsuppCongr_apply {ι : Type*} {C D : ι → Type*}
    [∀ i, Zero (C i)] [∀ i, Zero (D i)]
    (e : ∀ i, C i ≃ D i) (he : ∀ i, e i 0 = 0) (x : Π₀ i, C i) (i : ι) :
    dfinsuppCongr e he x i = e i (x i) := rfl

@[simp] theorem dfinsuppCongr_symm_apply {ι : Type*} {C D : ι → Type*}
    [∀ i, Zero (C i)] [∀ i, Zero (D i)]
    (e : ∀ i, C i ≃ D i) (he : ∀ i, e i 0 = 0) (x : Π₀ i, D i) (i : ι) :
    (dfinsuppCongr e he).symm x i = (e i).symm (x i) := rfl

noncomputable def dfinsuppProd {ι : Type*} (C D : ι → Type*)
    [∀ i, Zero (C i)] [∀ i, Zero (D i)] :
    (Π₀ i, C i × D i) ≃ (Π₀ i, C i) × (Π₀ i, D i) where
  toFun x := (DFinsupp.mapRange (fun _ => Prod.fst) (fun _ => rfl) x,
    DFinsupp.mapRange (fun _ => Prod.snd) (fun _ => rfl) x)
  invFun x := DFinsupp.zipWith (fun _ => Prod.mk) (fun _ => rfl) x.1 x.2
  left_inv x := by ext i <;> rfl
  right_inv x := by apply Prod.ext <;> ext i <;> rfl

noncomputable def finsuppProd {ι : Type*} (A : Type u) (B : Type v)
    [Zero A] [Zero B] : (ι →₀ (A × B)) ≃ (ι →₀ A) × (ι →₀ B) where
  toFun x := (Finsupp.mapRange Prod.fst rfl x, Finsupp.mapRange Prod.snd rfl x)
  invFun x := Finsupp.zipWith Prod.mk rfl x.1 x.2
  left_inv x := by ext i <;> rfl
  right_inv x := by apply Prod.ext <;> ext i <;> rfl

noncomputable def dfinsuppOfFinite {ι : Type*} {C : ι → Type*} [∀ i, Zero (C i)]
    (f : ∀ i, C i) (hf : Set.Finite {i | f i ≠ 0}) : Π₀ i, C i := by
  classical
  exact ⟨f, Trunc.mk ⟨hf.toFinset.val, fun i => by
    by_cases h : f i = 0
    · exact Or.inr h
    · exact Or.inl (by change i ∈ hf.toFinset; exact hf.mem_toFinset.mpr h)⟩⟩

abbrev Extra (F : Finset ℕ) (i : ℕ) (B : Type v) [Zero B] :=
  {b : B // i ∈ F → b = 0}

instance extraZero (F : Finset ℕ) (i : ℕ) (B : Type v) [Zero B] :
    Zero (Extra F i B) := ⟨⟨0, fun _ => rfl⟩⟩

noncomputable def extraToWord (F : Finset ℕ) {B : Type v} [Zero B]
    (x : Π₀ i, Extra F i B) : FWord F B :=
  Finsupp.ofSupportFinite (fun j => (x j.1).1) (by
    apply (x.finite_support.preimage Subtype.val_injective.injOn).subset
    intro j hj hzero
    exact hj (congrArg Subtype.val hzero))

noncomputable def extraFromWord (F : Finset ℕ) {B : Type v} [Zero B]
    (x : FWord F B) : Π₀ i, Extra F i B := by
  classical
  let f : ∀ i, Extra F i B := fun i => ⟨x.extendDomain i, by
    intro hi
    simp [Finsupp.extendDomain_apply, hi]⟩
  exact dfinsuppOfFinite f (x.extendDomain.hasFiniteSupport.subset (by
    intro i hi hzero
    apply hi
    exact Subtype.ext hzero))

@[simp] theorem extraFromWord_apply (F : Finset ℕ) {B : Type v} [Zero B]
    (x : FWord F B) (i : ℕ) :
    (extraFromWord F x i).1 = x.extendDomain i := rfl

noncomputable def extraWordEquiv (F : Finset ℕ) (B : Type v) [Zero B] :
    (Π₀ i, Extra F i B) ≃ FWord F B where
  toFun := extraToWord F
  invFun := extraFromWord F
  left_inv x := by
    classical
    ext i
    change (extraFromWord F (extraToWord F x) i).1 = (x i).1
    rw [extraFromWord_apply]
    by_cases hi : i ∈ F
    · simp [Finsupp.extendDomain_apply, hi, (x i).2 hi]
    · simp [Finsupp.extendDomain_apply, hi, extraToWord]
      rfl
  right_inv x := by
    classical
    ext j
    change (extraFromWord F x j.1).1 = x j
    simp [Finsupp.extendDomain_apply, j.2]

section Local
variable (A : Type u) (B : Type v) [Zero A] [Countable A] [Nontrivial A]
    [Zero B] [Countable B]

/-- The only matching choice: its parameter is the editable set itself. -/
noncomputable def localAbsorb (E : Set ℕ) (hE : E.Infinite) :
    (E →₀ A) ≃ B × (E →₀ A) := by
  letI : Infinite E := hE.to_subtype
  exact Classical.choose (exists_absorption_equiv (ι := E) (A := A) (B := B))

theorem localAbsorb_spec (E : Set ℕ) (hE : E.Infinite) :
    localAbsorb A B E hE 0 = (0, 0) ∧
      (∀ x, OneCoordinateClose x (localAbsorb A B E hE x).2) ∧
      (∀ y, OneCoordinateClose ((localAbsorb A B E hE).symm y) y.2) := by
  letI : Infinite E := hE.to_subtype
  exact Classical.choose_spec (exists_absorption_equiv (ι := E) (A := A) (B := B))

/-- Equal editable sets and equal input values use the same local matching. -/
theorem localAbsorb_congr (E D : Set ℕ) (hE : E.Infinite) (hD : D.Infinite)
    (hED : E = D) (x : E →₀ A) (y : D →₀ A)
    (hxy : ∀ j (hjE : j ∈ E) (hjD : j ∈ D), x ⟨j, hjE⟩ = y ⟨j, hjD⟩) :
    (localAbsorb A B E hE x).1 = (localAbsorb A B D hD y).1 ∧
      ∀ j (hjE : j ∈ E) (hjD : j ∈ D),
        (localAbsorb A B E hE x).2 ⟨j, hjE⟩ =
          (localAbsorb A B D hD y).2 ⟨j, hjD⟩ := by
  subst D
  have h : x = y := by ext j; exact hxy j.1 j.2 j.2
  subst y
  exact ⟨rfl, fun _ _ _ => rfl⟩

theorem localAbsorb_symm_congr (E D : Set ℕ) (hE : E.Infinite) (hD : D.Infinite)
    (hED : E = D) (b c : B) (hbc : b = c) (x : E →₀ A) (y : D →₀ A)
    (hxy : ∀ j (hjE : j ∈ E) (hjD : j ∈ D), x ⟨j, hjE⟩ = y ⟨j, hjD⟩) :
    ∀ j (hjE : j ∈ E) (hjD : j ∈ D),
      (localAbsorb A B E hE).symm (b, x) ⟨j, hjE⟩ =
        (localAbsorb A B D hD).symm (c, y) ⟨j, hjD⟩ := by
  subst D
  subst c
  have h : x = y := by ext j; exact hxy j.1 j.2 j.2
  subst y
  exact fun _ _ _ => rfl

noncomputable def localBlockEquiv (F : Finset ℕ) (i : ℕ) :
    (blockSet F i →₀ A) ≃ Extra F i B × (blockSet F i →₀ A) := by
  classical
  by_cases hi : i ∈ F
  · exact {
      toFun := fun x => (0, x)
      invFun := Prod.snd
      left_inv := fun _ => rfl
      right_inv := fun x => by
        apply Prod.ext
        · exact Subtype.ext ((x.1.2 hi).symm)
        · rfl }
  · exact (localAbsorb A B (blockSet F i) (blockSet_infinite F i)).trans
      ((Equiv.subtypeUnivEquiv (fun b : B => hi.elim)).symm.prodCongr (Equiv.refl _))

@[simp] theorem localBlockEquiv_zero (F : Finset ℕ) (i : ℕ) :
    localBlockEquiv A B F i 0 = (0, 0) := by
  classical
  by_cases hi : i ∈ F
  · simp [localBlockEquiv, hi]
  · simp [localBlockEquiv, hi, (localAbsorb_spec A B _ (blockSet_infinite F i)).1]
    rfl

theorem localBlockEquiv_close (F : Finset ℕ) (i : ℕ) (x : blockSet F i →₀ A) :
    OneCoordinateClose x (localBlockEquiv A B F i x).2 := by
  classical
  letI : Infinite (blockSet F i) := (blockSet_infinite F i).to_subtype
  by_cases hi : i ∈ F
  · simpa [localBlockEquiv, hi] using OneCoordinateClose.refl x
  · simpa [localBlockEquiv, hi] using
      (localAbsorb_spec A B _ (blockSet_infinite F i)).2.1 x

theorem localBlockEquiv_symm_close (F : Finset ℕ) (i : ℕ)
    (x : Extra F i B × (blockSet F i →₀ A)) :
    OneCoordinateClose ((localBlockEquiv A B F i).symm x) x.2 := by
  simpa only [Equiv.apply_symm_apply] using
    localBlockEquiv_close A B F i ((localBlockEquiv A B F i).symm x)

theorem localBlockEquiv_frozen (F : Finset ℕ) (i : ℕ) (hi : i ∈ F)
    (x : blockSet F i →₀ A) : localBlockEquiv A B F i x = (0, x) := by
  classical
  simp [localBlockEquiv, hi]

theorem localBlockEquiv_active_tail (F : Finset ℕ) (i : ℕ) (hi : i ∉ F)
    (x : blockSet F i →₀ A) : (localBlockEquiv A B F i x).2 =
      (localAbsorb A B (blockSet F i) (blockSet_infinite F i) x).2 := by
  classical
  simp [localBlockEquiv, hi]

theorem localBlockEquiv_active_extra (F : Finset ℕ) (i : ℕ) (hi : i ∉ F)
    (x : blockSet F i →₀ A) : (localBlockEquiv A B F i x).1.1 =
      (localAbsorb A B (blockSet F i) (blockSet_infinite F i) x).1 := by
  classical
  simp [localBlockEquiv, hi]

theorem localBlockEquiv_symm_frozen (F : Finset ℕ) (i : ℕ) (hi : i ∈ F)
    (x : Extra F i B × (blockSet F i →₀ A)) :
    (localBlockEquiv A B F i).symm x = x.2 := by
  classical
  simp [localBlockEquiv, hi]

theorem localBlockEquiv_symm_active (F : Finset ℕ) (i : ℕ) (hi : i ∉ F)
    (x : Extra F i B × (blockSet F i →₀ A)) :
    (localBlockEquiv A B F i).symm x =
      (localAbsorb A B (blockSet F i) (blockSet_infinite F i)).symm (x.1.1, x.2) := by
  classical
  simp [localBlockEquiv, hi]
  rfl

/-- Absorb a factor independently in each active infinite block. -/
noncomputable def maskedAbsorb (F : Finset ℕ) : FWord F A ≃ FWord F (A × B) :=
  (splitBlocks F A).trans
    ((dfinsuppCongr (localBlockEquiv A B F) (localBlockEquiv_zero A B F)).trans
      ((dfinsuppProd (fun i => Extra F i B) (fun i => blockSet F i →₀ A)).trans
        (((extraWordEquiv F B).prodCongr (splitBlocks F A).symm).trans
          ((Equiv.prodComm _ _).trans (finsuppProd A B).symm))))

@[simp] theorem maskedAbsorb_first (F : Finset ℕ) (x : FWord F A)
    (j : {j : ℕ // j ∉ F}) :
    (maskedAbsorb A B F x j).1 =
      (localBlockEquiv A B F (block j.1) (splitBlocks F A x (block j.1))).2
        ⟨j.1, rfl, j.2⟩ := rfl

@[simp] theorem maskedAbsorb_second (F : Finset ℕ) (x : FWord F A)
    (j : {j : ℕ // j ∉ F}) :
    (maskedAbsorb A B F x j).2 =
      (localBlockEquiv A B F j.1 (splitBlocks F A x j.1)).1.1 := rfl

@[simp] theorem maskedAbsorb_symm_apply (F : Finset ℕ) (x : FWord F (A × B))
    (j : {j : ℕ // j ∉ F}) :
    (maskedAbsorb A B F).symm x j =
      ((localBlockEquiv A B F (block j.1)).symm
        (extraFromWord F ((finsuppProd A B) x).2 (block j.1),
          splitBlocks F A ((finsuppProd A B) x).1 (block j.1)))
        ⟨j.1, rfl, j.2⟩ := rfl

@[simp] theorem maskedAbsorb_zero (F : Finset ℕ) : maskedAbsorb A B F 0 = 0 := by
  ext j <;> simp
  rfl

theorem maskedAbsorb_correction (F : Finset ℕ) (x : FWord F A) (i : ℕ) :
    ∃ j : ℕ, ∀ k (hk : k ∉ F), block k = i → k ≠ j →
      (maskedAbsorb A B F x ⟨k, hk⟩).1 = x ⟨k, hk⟩ := by
  obtain ⟨j, hj⟩ := localBlockEquiv_close A B F i (splitBlocks F A x i)
  refine ⟨j.1, ?_⟩
  intro k hk hki hkj
  rw [maskedAbsorb_first]
  subst i
  exact (hj ⟨k, rfl, hk⟩ (fun h => hkj (congrArg Subtype.val h))).symm

theorem maskedAbsorb_symm_correction (F : Finset ℕ) (x : FWord F (A × B)) (i : ℕ) :
    ∃ j : ℕ, ∀ k (hk : k ∉ F), block k = i → k ≠ j →
      (maskedAbsorb A B F).symm x ⟨k, hk⟩ = (x ⟨k, hk⟩).1 := by
  obtain ⟨j, hj⟩ := maskedAbsorb_correction A B F ((maskedAbsorb A B F).symm x) i
  refine ⟨j, ?_⟩
  intro k hk hki hkj
  simpa only [Equiv.apply_symm_apply] using (hj k hk hki hkj).symm

end Local

#print axioms maskedAbsorb
#print axioms maskedAbsorb_zero
#print axioms maskedAbsorb_correction
#print axioms maskedAbsorb_symm_correction

end Nathanson
