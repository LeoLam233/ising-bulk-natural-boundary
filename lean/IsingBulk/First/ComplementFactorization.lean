import IsingBulk.First.ComplementPhase
import IsingBulk.First.LocalizedDouble

/-! Complete factorization of the literal normalized double density into its
regular numerator and actual singular denominators. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- Invalid ordered-pair indices contribute one, so the fixed finite index
space represents exactly the source i<j factors without multiplicity changes. -/
def sourceFactorDenominator {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    SingularFactorIndex N → ℂ
  | .inl false => 1-coordinateProduct x
  | .inl true => 1-coordinateProduct y
  | .inr (.inl (false, i, j)) => if i < j then 1-x i*x j else 1
  | .inr (.inl (true, i, j)) => if i < j then 1-y i*y j else 1
  | .inr (.inr i) => dispersion (x i) (y i) s

def sourcePairNumerator {N : ℕ} (x : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), (x i-x j)

def sourcePairDenominator {N : ℕ} (x : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), (1-x i*x j)

def sourceDoubleNumerator {N : ℕ} (x y : Fin N → ℂ) : ℂ :=
  ((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹) * sourcePairNumerator x * sourcePairNumerator y

theorem pairProduct_eq_source_quotient {N : ℕ} (x : Fin N → ℂ) :
    pairProduct x = sourcePairNumerator x / sourcePairDenominator x := by
  unfold pairProduct pairKernel sourcePairNumerator sourcePairDenominator
  simp only [Finset.prod_div_distrib]

/-- The complete finite factor product has precisely the two global factors,
two ordered pair products and N dispersion factors of the manuscript. -/
theorem sourceFactorDenominator_prod {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    (∏ f, sourceFactorDenominator s x y f) =
      (1-coordinateProduct x)*(1-coordinateProduct y)*sourcePairDenominator x*
        sourcePairDenominator y*(∏ i, dispersion (x i) (y i) s) := by
  simp [Fintype.prod_sum_type, Fintype.prod_prod_type, sourceFactorDenominator,
    sourcePairDenominator, Finset.prod_filter]
  ring

/-- Exact actual-density factorization, including totalized algebra. Analytic
uses separately establish nonzero denominators on their contour domains. -/
theorem doubleDensity_eq_source_factorization {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    doubleDensity s x y = sourceDoubleNumerator x y * ∏ f, (sourceFactorDenominator s x y f)⁻¹ := by
  rw [Finset.prod_inv_distrib, sourceFactorDenominator_prod]
  unfold doubleDensity commonDensity sourceDoubleNumerator
  rw [pairProduct_eq_source_quotient, pairProduct_eq_source_quotient]
  simp only [div_eq_mul_inv, mul_inv, Finset.prod_inv_distrib]
  ring

/-- At an actual unit-torus point the source dispersion is its real level equation. -/
theorem dispersion_unit_eq_real {x y : ℂ} {s : ℂ} {S : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hS : sourceS s = (S : ℂ)) :
    dispersion x y s = ((S-x.re-y.re : ℝ) : ℂ) := by
  rw [dispersion, hS, Complex.inv_eq_conj hx, Complex.inv_eq_conj hy]
  apply Complex.ext <;> simp

/-- Activation is proved equivalent to vanishing of the literal source
factor. This prevents the vector classification from substituting a model. -/
theorem sourceFactorDenominator_zero_iff_active {N : ℕ} (s : ℂ) (S : ℝ)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : sourceS s = (S : ℂ)) (f : SingularFactorIndex N) :
    sourceFactorDenominator s x y f = 0 ↔ singularFactorActive x y S f := by
  rcases f with b | (⟨b, i, j⟩ | i)
  · cases b <;> simp only [sourceFactorDenominator, singularFactorActive, coordinateProduct, sub_eq_zero]
    all_goals exact eq_comm
  · cases b <;> by_cases hij : i < j <;>
      simp only [sourceFactorDenominator, singularFactorActive, hij, ite_true, ite_false,
        true_and, false_and, sub_eq_zero, one_ne_zero, iff_self] <;> exact eq_comm
  · rw [sourceFactorDenominator, dispersion_unit_eq_real (hx i) (hy i) hS]
    simp only [Complex.ofReal_eq_zero, singularFactorActive]
    constructor <;> intro h <;> linarith

end
end IsingBulk.First
