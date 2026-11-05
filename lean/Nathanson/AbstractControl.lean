import Nathanson.Hamming

noncomputable section
open Function
namespace Nathanson
variable {α β : Type*}

def firstLetter [Zero α] [Zero β] : Letter (α × β) → Letter α
  | .edit p => .edit p.1
  | .high => .high
  | .low => .low

def extraLetter [Zero α] [Zero β] : Letter (α × β) → β
  | .edit p => p.2
  | .high => 0
  | .low => 0

def firstWord [Zero α] [Zero β] (x : RWord (α × β)) : RWord α :=
  x.mapRange firstLetter rfl

def extraWord [Zero α] [Zero β] (x : RWord (α × β)) : ℕ →₀ β :=
  x.mapRange extraLetter rfl

@[simp] theorem firstWord_apply [Zero α] [Zero β] (x : RWord (α × β)) (i : ℕ) :
    firstWord x i = firstLetter (x i) := rfl
@[simp] theorem extraWord_apply [Zero α] [Zero β] (x : RWord (α × β)) (i : ℕ) :
    extraWord x i = extraLetter (x i) := rfl

theorem hDist_firstWord_le [Zero α] [Zero β] (x y : RWord (α × β)) :
    hDist (firstWord x) (firstWord y) ≤ hDist x y :=
  hDist_mapRange_le firstLetter rfl x y

theorem hDist_pair_le [Zero α] [Zero β] (x y : RWord (α × β)) :
    hDist x y ≤ hDist (firstWord x) (firstWord y) +
      hDist (extraWord x) (extraWord y) := by
  classical
  have h : hdiff x y ⊆ hdiff (firstWord x) (firstWord y) ∪
      hdiff (extraWord x) (extraWord y) := by
    intro i hi
    simp only [mem_hdiff, Finset.mem_union, firstWord_apply, extraWord_apply] at *
    by_contra hc
    push_neg at hc
    apply hi
    have h1 := hc.1
    have h2 := hc.2
    cases hx : x i <;> cases hy : y i <;>
      simp_all [firstLetter, extraLetter, Prod.ext_iff]
  exact (Finset.card_le_card h).trans (Finset.card_union_le _ _)

theorem affected_block_bound [Zero α] (block : ℕ → ℕ)
    (s : Finset ℕ) (x y u v : ℕ →₀ α)
    (hu : ∀ i, ∃ j, ∀ k, block k = i → k ≠ j → u k = x k)
    (hv : ∀ i, ∃ j, ∀ k, block k = i → k ≠ j → v k = y k)
    (hoff : ∀ k, block k ∉ s → u k = v k) :
    hDist u v ≤ hDist x y + 2 * s.card := by
  classical
  choose ju hju using hu
  choose jv hjv using hv
  let t := hdiff x y ∪ s.image ju ∪ s.image jv
  have hcard : t.card ≤ hDist x y + 2 * s.card := by
    have h1 := Finset.card_union_le (hdiff x y) (s.image ju)
    have h2 := Finset.card_union_le (hdiff x y ∪ s.image ju) (s.image jv)
    have h3 := Finset.card_image_le (s := s) (f := ju)
    have h4 := Finset.card_image_le (s := s) (f := jv)
    dsimp [t, hDist] at *
    omega
  apply (hDist_le_of_agree_off u v t ?_).trans hcard
  intro k hk
  have hkxy : k ∉ hdiff x y := by
    intro hx; exact hk (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  by_cases hb : block k ∈ s
  · have hku : k ≠ ju (block k) := by
      intro he
      exact hk (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨block k,hb,he.symm⟩)))
    have hkv : k ≠ jv (block k) := by
      intro he
      exact hk (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨block k,hb,he.symm⟩))
    exact (hju (block k) k rfl hku).trans
      ((agree_off_hdiff x y k hkxy).trans (hjv (block k) k rfl hkv).symm)
  · exact hoff k hb

def BlockAgree [Zero α] (block : ℕ → ℕ) (x y : RWord α) (i : ℕ) : Prop :=
  ∀ k, block k = i → x k = y k

theorem forward_seven [Zero α] [Zero β] (block : ℕ → ℕ)
    (f : RWord α → RWord (α × β))
    (hmove : ∀ x i, ∃ j, ∀ k, block k = i → k ≠ j → firstWord (f x) k = x k)
    (hloc : ∀ x y i, BlockAgree block x y i → x i = y i →
      (∀ k, block k = i → firstWord (f x) k = firstWord (f y) k) ∧
      extraWord (f x) i = extraWord (f y) i)
    (x y : RWord α) : hDist (f x) (f y) ≤ 7 * hDist x y := by
  classical
  let c := hdiff x y
  let s := c.image block ∪ c
  have hs : s.card ≤ 2 * hDist x y := by
    have h1 := Finset.card_union_le (c.image block) c
    have h2 := Finset.card_image_le (s := c) (f := block)
    dsimp [s,c,hDist] at *
    omega
  have hlocal (i : ℕ) (hi : i ∉ s) := by
    have hic : i ∉ c := fun h => hi (Finset.mem_union_right _ h)
    have hblock : BlockAgree block x y i := by
      intro k hk
      apply agree_off_hdiff x y k
      intro hc
      exact hi (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k,hc,hk⟩))
    exact hloc x y i hblock (agree_off_hdiff x y i hic)
  have hp : hDist (firstWord (f x)) (firstWord (f y)) ≤ hDist x y + 2*s.card :=
    affected_block_bound block s x y _ _ (hmove x) (hmove y)
      (fun k hk => (hlocal (block k) hk).1 k rfl)
  have he : hDist (extraWord (f x)) (extraWord (f y)) ≤ s.card :=
    hDist_le_of_agree_off _ _ s (fun i hi => (hlocal i hi).2)
  have hm := hDist_pair_le (f x) (f y)
  omega

theorem inverse_five [Zero α] [Zero β] (block : ℕ → ℕ)
    (f : RWord (α × β) → RWord α)
    (hmove : ∀ x i, ∃ j, ∀ k, block k = i → k ≠ j → f x k = firstWord x k)
    (hloc : ∀ x y i, BlockAgree block x y i → x i = y i →
      ∀ k, block k = i → f x k = f y k)
    (x y : RWord (α × β)) : hDist (f x) (f y) ≤ 5 * hDist x y := by
  classical
  let c := hdiff x y
  let s := c.image block ∪ c
  have hs : s.card ≤ 2 * hDist x y := by
    have h1 := Finset.card_union_le (c.image block) c
    have h2 := Finset.card_image_le (s := c) (f := block)
    dsimp [s,c,hDist] at *
    omega
  have hoff (k : ℕ) (hk : block k ∉ s) : f x k = f y k := by
    have hic : block k ∉ c := fun h => hk (Finset.mem_union_right _ h)
    apply hloc x y (block k) ?_ (agree_off_hdiff x y (block k) hic) k rfl
    intro j hj
    apply agree_off_hdiff x y j
    intro hc
    exact hk (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,hc,hj⟩))
  have hp := affected_block_bound block s (firstWord x) (firstWord y) (f x) (f y)
    (hmove x) (hmove y) hoff
  have hfirst := hDist_firstWord_le x y
  omega

#print axioms forward_seven
#print axioms inverse_five
end Nathanson
