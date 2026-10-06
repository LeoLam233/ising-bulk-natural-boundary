import Mathlib.Tactic

/-! Exact finite-dimensional algebra of eq:twofield and its residual field.
Analytic coordinate construction and pole estimates are separate obligations. -/
namespace IsingBulk.Jets
noncomputable section
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

def selectedField (a b : ι → K) (p q : ι) (i : ι) : K :=
  a i + (if i = p then (∑ k, a k) * b q / (b p-b q) else 0) -
    (if i = q then (∑ k, a k) * b p / (b p-b q) else 0)

theorem selectedField_sum (a b : ι → K) (p q : ι) (h : b p-b q ≠ 0) :
    ∑ i, selectedField a b p q i = 0 := by
  simp only [selectedField, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp
  ring

theorem selectedField_weighted_sum (a b : ι → K) (p q : ι) :
    ∑ i, b i * selectedField a b p q i = ∑ i, b i * a i := by
  simp only [selectedField, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem selectedField_off_pair (a b : ι → K) (p q i : ι)
    (hip : i ≠ p) (hiq : i ≠ q) : selectedField a b p q i = a i := by
  simp [selectedField, hip, hiq]

def residualField (a b : ι → K) (p q : ι) (i : ι) : K :=
  b i * a i - b i * selectedField a b p q i

theorem residualField_two_entries (a b : ι → K) (p q : ι) (hpq : p ≠ q) :
    residualField a b p q = fun i =>
      (if i = p then -(∑ k, a k)*b p*b q/(b p-b q) else 0) +
      (if i = q then (∑ k, a k)*b p*b q/(b p-b q) else 0) := by
  funext i
  by_cases hip : i = p
  · subst i
    simp [residualField, selectedField, hpq]
    ring
  · by_cases hiq : i = q
    · subst i
      simp [residualField, selectedField, Ne.symm hpq]
      ring
    · simp [residualField, selectedField, hip, hiq]

theorem residualField_sum (a b : ι → K) (p q : ι) :
    ∑ i, residualField a b p q i = 0 := by
  simp only [residualField, Finset.sum_sub_distrib, selectedField_weighted_sum, sub_self]

/-- The elementary denominator conversion underlying the selected difference
pole. Analytic divisibility of the final denominator is not assumed here. -/
theorem residual_denominator (Bp Bq xp xq : K) (hxp : xp ≠ 0) (hxq : xq ≠ 0)
    (hd : Bp*xq-Bq*xp ≠ 0) :
    (Bp/xp)*(Bq/xq)/(Bp/xp-Bq/xq) = Bp*Bq/(Bp*xq-Bq*xp) := by
  have h : Bp/xp-Bq/xq ≠ 0 := by
    rw [div_sub_div _ _ hxp hxq]
    exact div_ne_zero (by simpa [mul_comm] using hd) (mul_ne_zero hxp hxq)
  field_simp

end
end IsingBulk.Jets


