import Nathanson.Relative
import Nathanson.IntegerComparison

/-! Unconditional equivalence of all signed-power integer word metrics. -/

namespace Nathanson
noncomputable section
open scoped NNReal

def relativeEquiv35 (α β : Type*) [Zero α] [Countable α] [Nontrivial α]
    [Zero β] [Countable β] [Nontrivial β] : RelativeEquiv α β 35 :=
  relativeFromAbsorptions (relativeAbsorption α β) (relativeAbsorption β α)

/-- For every pair of integer bases at least two, the actual signed-power
word distances admit a bijection with explicit two-sided linear bounds. -/
theorem all_bases_bilipschitz (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ f : ℤ ≃ ℤ,
      (∀ x y, wordDist b (f x) (f y) ≤ comparisonConstant a b * wordDist a x y) ∧
      (∀ x y, wordDist a x y ≤ comparisonConstant b a * wordDist b (f x) (f y)) := by
  have ha2 : 4 ≤ a ^ 2 := by nlinarith
  have hb2 : 4 ≤ b ^ 2 := by nlinarith
  letI : NeZero (a ^ 2 - 2) := ⟨by omega⟩
  letI : NeZero (b ^ 2 - 2) := ⟨by omega⟩
  letI : Nontrivial (Fin (a ^ 2 - 2)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  letI : Nontrivial (Fin (b ^ 2 - 2)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  exact integer_equiv_of_squared_relative a b ha hb
    (relativeEquiv35 (Fin (a ^ 2 - 2)) (Fin (b ^ 2 - 2)))

/-- The same theorem in mathlib's genuine metric-space interfaces. -/
theorem all_bases_metric_bilipschitz (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ f : PowerInt a ≃ PowerInt b,
      LipschitzWith (comparisonConstant a b : ℝ≥0) f ∧
      AntilipschitzWith (comparisonConstant b a : ℝ≥0) f := by
  obtain ⟨f, hf, hr⟩ := all_bases_bilipschitz a b ha hb
  exact metric_bilipschitz_of_wordBounds a b _ _ f hf hr

theorem prime_bases_metric_bilipschitz (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    ∃ f : PowerInt p ≃ PowerInt q,
      LipschitzWith (comparisonConstant p q : ℝ≥0) f ∧
      AntilipschitzWith (comparisonConstant q p : ℝ≥0) f :=
  all_bases_metric_bilipschitz p q hp.two_le hq.two_le

theorem two_three_bilipschitz :
    ∃ f : ℤ ≃ ℤ,
      (∀ x y, wordDist 3 (f x) (f y) ≤ 564 * wordDist 2 x y) ∧
      (∀ x y, wordDist 2 x y ≤ 321 * wordDist 3 (f x) (f y)) := by
  simpa [comparisonConstant] using all_bases_bilipschitz 2 3 (by decide) (by decide)

theorem two_three_metric_bilipschitz :
    ∃ f : PowerInt 2 ≃ PowerInt 3,
      LipschitzWith 564 f ∧ AntilipschitzWith 321 f := by
  simpa [comparisonConstant] using all_bases_metric_bilipschitz 2 3 (by decide) (by decide)

end
end Nathanson

#print axioms Nathanson.relativeEquiv35
#print axioms Nathanson.all_bases_bilipschitz
#print axioms Nathanson.all_bases_metric_bilipschitz
#print axioms Nathanson.prime_bases_metric_bilipschitz
#print axioms Nathanson.two_three_bilipschitz
#print axioms Nathanson.two_three_metric_bilipschitz
