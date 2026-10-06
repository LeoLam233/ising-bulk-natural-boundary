import IsingBulk.First.ComplementFactorization
import IsingBulk.First.ComplementExponentialProduct

/-! The precise finite-factor exponential representation of the actual
localized normalized double-contour density. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators

def validSourceFactor {N : ℕ} : SingularFactorIndex N → Prop
  | .inl _ => True
  | .inr (.inl (_, i, j)) => i < j
  | .inr (.inr _) => True

def sourceFactorExponentialScalar {N : ℕ} : SingularFactorIndex N → ℂ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => -Complex.I

theorem active_source_factor_valid {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (f : SingularFactorIndex N) (hf : singularFactorActive x y S f) : validSourceFactor f := by
  rcases f with b | (⟨b, i, j⟩ | i)
  · trivial
  · cases b <;> exact hf.1
  · trivial

theorem anglePoint_eq_angularCurve (r θ : ℝ) :
    anglePoint r θ = angularCurve ((r : ℂ) * 1) θ 1 := by
  simp [anglePoint, circleMap, angularCurve]

/-- Exact factor-by-factor complex prefactors, including -i for each dispersion. -/
theorem sourceFactor_inverse_exponent {N : ℕ} (r : ℝ) (s : ℂ)
    (u : DoubleAngularVector N) (f : SingularFactorIndex N) (hf : validSourceFactor f) :
    (sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f)⁻¹ =
      sourceFactorExponentialScalar f *
        (-sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f u)⁻¹ := by
  rcases f with b | (⟨b, i, j⟩ | i)
  · cases b <;> simp [sourceFactorDenominator, sourceFactorExponentialScalar,
      sourceAngularExponent, singularFactorExponent, coordinateProduct, angleTuple,
      anglePoint_eq_angularCurve, neg_sub]
  · change i < j at hf
    cases b <;> simp [sourceFactorDenominator, sourceFactorExponentialScalar,
      sourceAngularExponent, singularFactorExponent, angleTuple, anglePoint_eq_angularCurve,
      hf, neg_sub]
  · simp only [sourceFactorDenominator, sourceFactorExponentialScalar,
      sourceAngularExponent, singularFactorExponent, angleTuple, anglePoint_eq_angularCurve]
    simp
    ring_nf
    simp [Complex.I_sq]

/-- Everything except the selected potentially singular factors stays in the
literal regular amplitude, with the normalized angular Jacobians unchanged. -/
def localizedRegularAmplitude {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (u : DoubleAngularVector N) : ℂ :=
  (w u : ℂ) * angleProductJacobian r u.2 * angleProductJacobian r u.1 *
    sourceDoubleNumerator (angleTuple r u.1) (angleTuple r u.2) *
    (∏ f ∈ Jᶜ, (sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f)⁻¹) *
    ∏ f ∈ J, sourceFactorExponentialScalar f

/-- Literal source factorization with a fixed selected finite subset J. -/
theorem localizedDoubleAngleDensity_factorization {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (hJ : ∀ f ∈ J, validSourceFactor f) (u : DoubleAngularVector N) :
    localizedDoubleAngleDensity r s w u = localizedRegularAmplitude r s w J u *
      ∏ f ∈ J, (-sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f u)⁻¹ := by
  classical
  have hprod : (∏ f ∈ J, (sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f)⁻¹) =
      (∏ f ∈ J, sourceFactorExponentialScalar f) *
        ∏ f ∈ J, (-sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f u)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun f hf => sourceFactor_inverse_exponent r s u f (hJ f hf))
  unfold localizedDoubleAngleDensity localizedRegularAmplitude
  rw [doubleDensity_eq_source_factorization,
    ← Finset.prod_compl_mul_prod J (fun f =>
      (sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f)⁻¹), hprod]
  ring

/-- Exact positive-half-line representation of the actual localized density.
It retains every source pair, global factor, normalized measure and scalar phase. -/
theorem localizedDoubleAngleDensity_exponential {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hmargin : r⁻¹-r < (sourceS s).im) (w : DoubleAngularVector N → ℝ)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, validSourceFactor f)
    (u : DoubleAngularVector N) :
    localizedDoubleAngleDensity r s w u =
      ∫ ξ : J → ℝ in positiveAuxiliaryOrthant J,
        localizedRegularAmplitude r s w J u * Complex.exp
          (∑ f : J, sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f.val u * (ξ f : ℂ)) := by
  rw [localizedDoubleAngleDensity_factorization r s w J hJ, integral_const_mul]
  have hd (f : J) : (sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f.val u).re < 0 :=
    singularFactorExponent_re_negative hN hr hr1 hmargin _ _ (by simp) (by simp) u f.val 1
  rw [integral_auxiliary_exponential _ hd]
  congr 1
  exact (Finset.prod_finset_coe (fun f : SingularFactorIndex N =>
    (-sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f u)⁻¹) J).symm

end
end IsingBulk.First
