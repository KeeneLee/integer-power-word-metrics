import Nathanson.CarryTransfer
import Nathanson.MetricModel

/-! Passage from a relative recoding for squared bases to the original metrics. -/

namespace Nathanson
noncomputable section
open scoped NNReal

/-- The forward constant used by the complete formal construction. -/
def comparisonConstant (a b : ℕ) : ℕ := a * (2 + 35 * (b ^ 2 - 1))

theorem integer_equiv_of_squared_relative (a b : ℕ)
    [NeZero (a ^ 2 - 2)] [NeZero (b ^ 2 - 2)]
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (e : RelativeEquiv (Fin (a ^ 2 - 2)) (Fin (b ^ 2 - 2)) 35) :
    ∃ f : ℤ ≃ ℤ,
      (∀ x y, wordDist b (f x) (f y) ≤ comparisonConstant a b * wordDist a x y) ∧
      (∀ x y, wordDist a x y ≤ comparisonConstant b a * wordDist b (f x) (f y)) := by
  have ha2 : 4 ≤ a ^ 2 := by nlinarith
  have hb2 : 4 ≤ b ^ 2 := by nlinarith
  obtain ⟨f, hf, hr⟩ := relative_integer_transfer (a ^ 2) (b ^ 2) ha2 hb2 e
  refine ⟨f, ?_, ?_⟩
  · intro x y
    calc
      wordDist b (f x) (f y) ≤ wordDist (b ^ 2) (f x) (f y) :=
        wordDist_le_square b _ _
      _ ≤ (2 + 35 * (b ^ 2 - 1)) * wordDist (a ^ 2) x y := hf x y
      _ ≤ (2 + 35 * (b ^ 2 - 1)) * (a * wordDist a x y) :=
        Nat.mul_le_mul_left _ (wordDist_square_le (by omega : 1 ≤ a) x y)
      _ = comparisonConstant a b * wordDist a x y := by
        simp only [comparisonConstant]; ring
  · intro x y
    calc
      wordDist a x y ≤ wordDist (a ^ 2) x y := wordDist_le_square a x y
      _ ≤ (2 + 35 * (a ^ 2 - 1)) * wordDist (b ^ 2) (f x) (f y) := hr x y
      _ ≤ (2 + 35 * (a ^ 2 - 1)) * (b * wordDist b (f x) (f y)) :=
        Nat.mul_le_mul_left _ (wordDist_square_le (by omega : 1 ≤ b) _ _)
      _ = comparisonConstant b a * wordDist b (f x) (f y) := by
        simp only [comparisonConstant]; ring

theorem metric_equiv_of_squared_relative (a b : ℕ)
    [NeZero (a ^ 2 - 2)] [NeZero (b ^ 2 - 2)]
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (e : RelativeEquiv (Fin (a ^ 2 - 2)) (Fin (b ^ 2 - 2)) 35) :
    ∃ f : PowerInt a ≃ PowerInt b,
      LipschitzWith (comparisonConstant a b : ℝ≥0) f ∧
      AntilipschitzWith (comparisonConstant b a : ℝ≥0) f := by
  obtain ⟨f, hf, hr⟩ := integer_equiv_of_squared_relative a b ha hb e
  exact metric_bilipschitz_of_wordBounds a b _ _ f hf hr

end
end Nathanson

#print axioms Nathanson.integer_equiv_of_squared_relative
#print axioms Nathanson.metric_equiv_of_squared_relative
