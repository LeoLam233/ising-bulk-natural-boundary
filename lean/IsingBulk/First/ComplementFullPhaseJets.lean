import IsingBulk.First.ComplementSourceAnalytic
import IsingBulk.First.ComplementPhaseSum
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Exact fixed-radius derivatives of the complete source exponential phase.
The angular part of the phase stays inside the exponential throughout. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- Auxiliary mass carried by dispersion factors, the only s-dependent factors. -/
def dispersionAuxiliaryTotal {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → SingularFactorIndex N) (ξ : ι → ℝ) : ℝ :=
  ∑ i, match J i with
    | .inr (.inr _) => ξ i
    | _ => 0

/-- All temperature dependence of the complete phase is affine in s+s⁻¹. -/
theorem sourcePhaseSum_temperature_split {ι : Type*} [Fintype ι] {N : ℕ}
    (r : ℝ) (s : ℂ) (x y : Fin N → ℂ) (J : ι → SingularFactorIndex N)
    (ξ : ι → ℝ) (u : DoubleAngularVector N) :
    sourcePhaseSum r s x y J ξ u =
      sourceTemperaturePhase s * (dispersionAuxiliaryTotal J ξ : ℂ) +
      sourcePhaseSum r 0 x y J ξ u := by
  unfold sourcePhaseSum dispersionAuxiliaryTotal
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases J i with b | (⟨b, a, c⟩ | a)
  · cases b <;> simp [sourceAngularExponent, singularFactorExponent]
  · cases b <;> simp [sourceAngularExponent, singularFactorExponent]
  · simp only [sourceAngularExponent, singularFactorExponent, dispersion,
      sourceTemperaturePhase, sourceS, inv_zero, add_zero]
    ring

/-- The polynomial derivative identity is unchanged by an s-independent phase
shift. Its exponential is never bounded separately from the complete phase. -/
theorem parameter_exponential_shift_derivative (A B : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (j : ℕ) (z H : ℂ) {s : ℂ} (hs : s ∈ U) :
    (deriv^[j] (fun w => A w * Complex.exp (B w * z + H))) s =
      parameterExpPolynomial z (parameterExpTerms A B j) s *
        Complex.exp (B s * z + H) := by
  have he : (fun w => A w * Complex.exp (B w * z + H)) =
      (fun w => (A w * Complex.exp (B w * z)) * Complex.exp H) := by
    funext w
    rw [Complex.exp_add, mul_assoc]
  rw [he, ← iteratedDeriv_eq_iterate, iteratedDeriv_mul_const_field,
    iteratedDeriv_eq_iterate, parameter_exponential_derivative A B U hU hA hB j z s hs,
    Complex.exp_add, mul_assoc]

/-- Actual parameter derivatives of the exact localized exponential integrand,
with all angular variables and the contour radius held fixed. -/
theorem source_full_phase_derivative {N : ℕ} (r : ℝ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (u : DoubleAngularVector N) (ξ : J → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hs0 : ∀ s ∈ U, s ≠ 0)
    (hden : ∀ s ∈ U, ∀ f ∈ Jᶜ,
      sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0)
    (j : ℕ) {s : ℂ} (hs : s ∈ U) :
    (deriv^[j] (fun z => localizedRegularAmplitude r z w J u *
      Complex.exp (sourcePhaseSum r z (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u))) s =
      parameterExpPolynomial (dispersionAuxiliaryTotal (fun f : J => f.1) ξ : ℂ)
        (parameterExpTerms (fun z => localizedRegularAmplitude r z w J u) sourceTemperaturePhase j) s *
      Complex.exp (sourcePhaseSum r s (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u) := by
  have he : (fun z => localizedRegularAmplitude r z w J u *
      Complex.exp (sourcePhaseSum r z (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u)) =
      (fun z => localizedRegularAmplitude r z w J u * Complex.exp
        (sourceTemperaturePhase z * (dispersionAuxiliaryTotal (fun f : J => f.1) ξ : ℂ) +
          sourcePhaseSum r 0 (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u)) := by
    funext z
    rw [sourcePhaseSum_temperature_split r z]
  rw [he, sourcePhaseSum_temperature_split r s]
  exact parameter_exponential_shift_derivative _ _ U hU
    (fun s hs => localizedRegularAmplitude_analyticAt r w J u (hs0 s hs) (hden s hs))
    (fun s hs => sourceTemperaturePhase_analyticAt (hs0 s hs)) j _ _ hs

end
end IsingBulk.First
