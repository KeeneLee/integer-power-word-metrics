module

public import Nathanson.Matching
public import Mathlib.Data.Countable.Basic
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Finsupp.Single

/-!
# Absorbing a countable factor into finitely supported configurations

The equivalence fixes zero. Its configuration component, and the inverse
configuration, differ from the original data at at most one coordinate.
This strengthens the finite-factor existence statement to a countable factor.
The existence proof is classical and does not assert computability.
-/

@[expose] public section

namespace Nathanson

universe u v w

variable {ι : Type u} {A : Type v} {B : Type w} [Zero A]

/-- Two configurations agree outside one coordinate; equality is allowed. -/
def OneCoordinateClose (x z : ι →₀ A) : Prop :=
  ∃ j : ι, ∀ k : ι, k ≠ j → x k = z k

theorem OneCoordinateClose.refl [Nonempty ι] (x : ι →₀ A) :
    OneCoordinateClose x x := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  exact ⟨j, fun _ _ => rfl⟩

theorem OneCoordinateClose.symm {x z : ι →₀ A} (h : OneCoordinateClose x z) :
    OneCoordinateClose z x := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun k hk => (hj k hk).symm⟩

/-- There are infinitely many configurations within one-coordinate change. -/
theorem infinite_oneCoordinateClose [Infinite ι] [Nontrivial A] (x : ι →₀ A) :
    Set.Infinite {z : ι →₀ A | OneCoordinateClose x z} := by
  classical
  obtain ⟨c, hc⟩ := exists_ne (0 : A)
  let S : Set ι := {i | i ∉ x.support}
  have hS : S.Infinite := x.support.finite_toSet.infinite_compl
  letI : Infinite S := hS.to_subtype
  let g (i : S) : ι →₀ A := x.update i.1 c
  have hg : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hzero : x i.1 = 0 := Finsupp.notMem_support_iff.mp i.2
    have heq := congrArg (fun z : ι →₀ A => z i.1) hij
    have hc0 : c = 0 := by
      simpa [g, Finsupp.update_apply, hne, hzero] using heq
    exact hc hc0
  apply Set.infinite_of_injective_forall_mem hg
  intro i
  refine ⟨i.1, ?_⟩
  intro k hk
  simp only [g, Finsupp.update_apply, if_neg hk]

/-- Absorb a countable pointed factor while fixing zero and changing at most one
configuration coordinate, in both directions. -/
theorem exists_absorption_equiv
    [Countable ι] [Infinite ι] [Countable A] [Nontrivial A]
    [Zero B] [Countable B] :
    ∃ e : (ι →₀ A) ≃ (B × (ι →₀ A)),
      e 0 = (0, 0) ∧
      (∀ x, OneCoordinateClose x (e x).2) ∧
      (∀ y, OneCoordinateClose (e.symm y) y.2) := by
  classical
  let R (x : ι →₀ A) (y : B × (ι →₀ A)) : Prop :=
    OneCoordinateClose x y.2
  have hleft (x : ι →₀ A) : Set.Infinite {y : B × (ι →₀ A) | R x y} := by
    exact (infinite_oneCoordinateClose x).preimage
      (f := fun y : B × (ι →₀ A) => y.2)
      (by
        intro z hz
        exact ⟨(0, z), rfl⟩)
  have hright (y : B × (ι →₀ A)) : Set.Infinite {x : ι →₀ A | R x y} := by
    have hset : {x : ι →₀ A | R x y} =
        {x : ι →₀ A | OneCoordinateClose y.2 x} := by
      ext x
      exact ⟨OneCoordinateClose.symm, OneCoordinateClose.symm⟩
    rw [hset]
    exact infinite_oneCoordinateClose y.2
  obtain ⟨e, heR, he0⟩ := exists_equiv_of_infinite_fibers_fix
    R hleft hright (0 : ι →₀ A) (0, 0) (OneCoordinateClose.refl 0)
  have heclose (x : ι →₀ A) : OneCoordinateClose x (e x).2 := heR x
  refine ⟨e, he0, heclose, ?_⟩
  intro y
  simpa only [e.apply_symm_apply] using heclose (e.symm y)

#print axioms infinite_oneCoordinateClose
#print axioms exists_absorption_equiv

end Nathanson
