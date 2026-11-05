import Nathanson.WordMetric
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic.NormNum

/-!
# The signed-power word distance as a mathlib metric

PowerInt is a type synonym for the integers with the real-valued distance
obtained by casting the actual minimum signed-power word length.
The metric instance does not use the usual Euclidean distance on the integers.
-/

namespace Nathanson
noncomputable section
open scoped NNReal

def PowerInt (_a : ℕ) : Type := ℤ

namespace PowerInt

def toInt {a : ℕ} (x : PowerInt a) : ℤ := x
def ofInt (a : ℕ) (z : ℤ) : PowerInt a := z

@[simp] theorem toInt_ofInt (a : ℕ) (z : ℤ) : toInt (ofInt a z) = z := rfl
@[simp] theorem ofInt_toInt {a : ℕ} (x : PowerInt a) : ofInt a x.toInt = x := rfl

instance metricSpace (a : ℕ) : MetricSpace (PowerInt a) where
  dist x y := (wordDist a x.toInt y.toInt : ℝ)
  dist_self x := by simp
  dist_comm x y := by rw [wordDist_comm]
  dist_triangle x y z := by
    exact_mod_cast wordDist_triangle a x.toInt y.toInt z.toInt
  eq_of_dist_eq_zero := by
    intro x y h
    have h0 : wordDist a x.toInt y.toInt = 0 := by exact_mod_cast h
    exact wordDist_eq_zero.mp h0

@[simp] theorem dist_eq_wordDist (a : ℕ) (x y : PowerInt a) :
    dist x y = (wordDist a x.toInt y.toInt : ℝ) := rfl

def equivOfIntEquiv (a b : ℕ) (e : ℤ ≃ ℤ) : PowerInt a ≃ PowerInt b where
  toFun x := ofInt b (e x.toInt)
  invFun y := ofInt a (e.symm y.toInt)
  left_inv x := e.symm_apply_apply x
  right_inv y := e.apply_symm_apply y

@[simp] theorem equivOfIntEquiv_toInt (a b : ℕ) (e : ℤ ≃ ℤ) (x : PowerInt a) :
    (equivOfIntEquiv a b e x).toInt = e x.toInt := rfl

end PowerInt

theorem powerInt_lipschitz_of_wordBound (a b C : ℕ) (e : ℤ ≃ ℤ)
    (h : ∀ x y : ℤ, wordDist b (e x) (e y) ≤ C * wordDist a x y) :
    LipschitzWith (C : ℝ≥0) (PowerInt.equivOfIntEquiv a b e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change (wordDist b (e x.toInt) (e y.toInt) : ℝ) ≤
    ((C : ℝ≥0) : ℝ) * (wordDist a x.toInt y.toInt : ℝ)
  exact_mod_cast h x.toInt y.toInt

theorem powerInt_antilipschitz_of_wordBound (a b D : ℕ) (e : ℤ ≃ ℤ)
    (h : ∀ x y : ℤ, wordDist a x y ≤ D * wordDist b (e x) (e y)) :
    AntilipschitzWith (D : ℝ≥0) (PowerInt.equivOfIntEquiv a b e) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  change (wordDist a x.toInt y.toInt : ℝ) ≤
    ((D : ℝ≥0) : ℝ) * (wordDist b (e x.toInt) (e y.toInt) : ℝ)
  exact_mod_cast h x.toInt y.toInt

/-- A genuine mathlib bilipschitz equivalence from bounds on the actual
signed-power distances. Existence of the integer equivalence is explicit. -/
theorem metric_bilipschitz_of_wordBounds (a b C D : ℕ) (e : ℤ ≃ ℤ)
    (hforward : ∀ x y : ℤ, wordDist b (e x) (e y) ≤ C * wordDist a x y)
    (hreverse : ∀ x y : ℤ, wordDist a x y ≤ D * wordDist b (e x) (e y)) :
    ∃ f : PowerInt a ≃ PowerInt b,
      LipschitzWith (C : ℝ≥0) f ∧ AntilipschitzWith (D : ℝ≥0) f :=
  ⟨PowerInt.equivOfIntEquiv a b e,
    powerInt_lipschitz_of_wordBound a b C e hforward,
    powerInt_antilipschitz_of_wordBound a b D e hreverse⟩

end
end Nathanson

#print axioms Nathanson.PowerInt.metricSpace
#print axioms Nathanson.metric_bilipschitz_of_wordBounds
