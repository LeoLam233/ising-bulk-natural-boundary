import IsingBulk.First.ComplementLocalizedFactors
import IsingBulk.First.ComplementOnsiteGeometry

/-! Literal onsite factorization. The two global product denominators are
absent; their unused entries in the common finite index type are exactly one. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- Only pair and dispersion factors occur in the onsite coefficient. -/
def isOnsiteFactor {N : ℕ} : SingularFactorIndex N → Prop
  | .inl _ => False
  | .inr _ => True

def onsiteFactorDenominator {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) : SingularFactorIndex N → ℂ
  | .inl _ => 1
  | .inr f => sourceFactorDenominator s x y (.inr f)

def sourceOnsiteNumerator {N : ℕ} (x y : Fin N → ℂ) : ℂ :=
  (coordinateProduct x * coordinateProduct y)⁻¹ * sourcePairNumerator x * sourcePairNumerator y

def localizedOnsiteAngleDensity {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (u : DoubleAngularVector N) : ℂ :=
  (w u : ℂ) * angleProductJacobian r u.2 * angleProductJacobian r u.1 *
    onsiteDensity s (angleTuple r u.1) (angleTuple r u.2)

def onsiteRegularAmplitude {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (u : DoubleAngularVector N) : ℂ :=
  (w u : ℂ) * angleProductJacobian r u.2 * angleProductJacobian r u.1 *
    sourceOnsiteNumerator (angleTuple r u.1) (angleTuple r u.2) *
    (∏ f ∈ Jᶜ, (onsiteFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f)⁻¹) *
    ∏ f ∈ J, sourceFactorExponentialScalar f

theorem onsiteFactorDenominator_eq_source {N : ℕ} (s : ℂ) (x y : Fin N → ℂ)
    (f : SingularFactorIndex N) (hf : isOnsiteFactor f) :
    onsiteFactorDenominator s x y f = sourceFactorDenominator s x y f := by
  cases f with
  | inl b => exact hf.elim
  | inr f => rfl

theorem onsiteFactorDenominator_prod {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    (∏ f, onsiteFactorDenominator s x y f) =
      sourcePairDenominator x * sourcePairDenominator y * ∏ i, dispersion (x i) (y i) s := by
  simp [Fintype.prod_sum_type, Fintype.prod_prod_type, onsiteFactorDenominator,
    sourceFactorDenominator, sourcePairDenominator, Finset.prod_filter, mul_comm]

theorem onsiteDensity_eq_source_factorization {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) :
    onsiteDensity s x y = sourceOnsiteNumerator x y * ∏ f, (onsiteFactorDenominator s x y f)⁻¹ := by
  rw [Finset.prod_inv_distrib, onsiteFactorDenominator_prod]
  unfold onsiteDensity commonDensity sourceOnsiteNumerator
  rw [pairProduct_eq_source_quotient, pairProduct_eq_source_quotient]
  simp only [div_eq_mul_inv, mul_inv, Finset.prod_inv_distrib]
  ring

theorem localizedOnsiteAngleDensity_factorization {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (hJ : ∀ f ∈ J, isOnsiteFactor f ∧ validSourceFactor f) (u : DoubleAngularVector N) :
    localizedOnsiteAngleDensity r s w u = onsiteRegularAmplitude r s w J u *
      ∏ f ∈ J, (-sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f u)⁻¹ := by
  classical
  have hprod : (∏ f ∈ J, (onsiteFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f)⁻¹) =
      (∏ f ∈ J, sourceFactorExponentialScalar f) *
        ∏ f ∈ J, (-sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f u)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro f hf
    rw [onsiteFactorDenominator_eq_source _ _ _ f (hJ f hf).1]
    exact sourceFactor_inverse_exponent r s u f (hJ f hf).2
  unfold localizedOnsiteAngleDensity onsiteRegularAmplitude
  rw [onsiteDensity_eq_source_factorization,
    ← Finset.prod_compl_mul_prod J (fun f =>
      (onsiteFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f)⁻¹), hprod]
  ring

theorem onsiteFactorDenominator_zero_iff_active {N : ℕ} (s : ℂ) (S : ℝ)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : sourceS s = (S : ℂ)) (f : SingularFactorIndex N) :
    onsiteFactorDenominator s x y f = 0 ↔ isOnsiteFactor f ∧ singularFactorActive x y S f := by
  cases f with
  | inl b => simp [onsiteFactorDenominator, isOnsiteFactor]
  | inr f =>
    simpa only [onsiteFactorDenominator, isOnsiteFactor, true_and] using
      sourceFactorDenominator_zero_iff_active s S x y hx hy hS (.inr f)

end
end IsingBulk.First
