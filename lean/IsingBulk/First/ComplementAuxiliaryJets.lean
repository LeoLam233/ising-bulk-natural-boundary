import IsingBulk.First.ComplementSourceUniform

/-! Exact unnormalization of genuine fixed-radius s-derivatives before the
angular integral. The scalar Rʲ cost is explicit. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators

/-- Point-local form of the exact normalized jet identity. -/
theorem normalizedParameterJet_derivative_at (A B : ℂ → ℂ) {s : ℂ}
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s)
    (R v H : ℂ) (hR : R ≠ 0) (j : ℕ) :
    (deriv^[j] (fun z => A z * Complex.exp (B z * (R*v) + H))) s =
      R^j * normalizedParameterJet A B R⁻¹ v j s * Complex.exp (B s * (R*v) + H) := by
  let U := {z | AnalyticAt ℂ A z} ∩ {z | AnalyticAt ℂ B z}
  exact normalizedParameterJet_derivative A B U
    ((isOpen_analyticAt ℂ A).inter (isOpen_analyticAt ℂ B))
    (fun _ h => h.1) (fun _ h => h.2) R v H hR j s ⟨hA,hB⟩

def sourceAuxiliaryJet {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (j : ℕ) (ξ : J → ℝ) (u : DoubleAngularVector N) : ℂ :=
  (deriv^[j] (fun z => localizedRegularAmplitude r z w J u *
    Complex.exp (sourcePhaseSum r z (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u))) s

/-- Exact normalization of the literal s-jet on one auxiliary ray. -/
theorem sourceAuxiliaryJet_normalize {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (j : ℕ) (ξ : J → ℝ) (R : ℝ) (hR : R ≠ 0) (u : DoubleAngularVector N)
    (hs : s ≠ 0)
    (hden : ∀ f ∈ Jᶜ, sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0) :
    sourceAuxiliaryJet r s w J j ξ u =
      (R : ℂ)^j * sourceIBPAmplitude w J j ((r,s),((fun f => ξ f/R),R⁻¹)) u *
        Complex.exp ((R : ℂ) * sourceIBPPhase J ((r,s),((fun f => ξ f/R),R⁻¹)) u) := by
  let η : J → ℝ := fun f => ξ f/R
  let v : ℂ := (dispersionAuxiliaryTotal (fun f : J => f.1) η : ℂ)
  let H : ℂ := (R : ℂ) * sourcePhaseSum r 0 (fun _ => 1) (fun _ => 1) (fun f : J => f.1) η u
  have hphase (z : ℂ) : sourcePhaseSum r z (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u =
      sourceTemperaturePhase z * ((R : ℂ)*v) + H := by
    rw [sourcePhaseSum_normalize r z _ _ _ ξ R hR u,
      sourcePhaseSum_temperature_split r z]
    change (R : ℂ) * (sourceTemperaturePhase z * v + _) = _
    dsimp [H]
    ring
  have he : (fun z => localizedRegularAmplitude r z w J u *
      Complex.exp (sourcePhaseSum r z (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u)) =
      (fun z => localizedRegularAmplitude r z w J u * Complex.exp (sourceTemperaturePhase z*((R : ℂ)*v)+H)) := by
    funext z
    rw [hphase]
  unfold sourceAuxiliaryJet
  rw [he, normalizedParameterJet_derivative_at _ _
    (localizedRegularAmplitude_analyticAt r w J u hs hden) (sourceTemperaturePhase_analyticAt hs)
    (R : ℂ) v H (Complex.ofReal_ne_zero.mpr hR) j, ← hphase s]
  rw [sourcePhaseSum_normalize r s _ _ _ ξ R hR u]
  simp only [sourceIBPAmplitude, sourceIBPPhase, sourceNormalizedAmplitude, Complex.ofReal_inv]
  rfl

/-- The explicit Rʲ factor leaves the actual angular integral unchanged. -/
theorem integral_sourceAuxiliaryJet_normalize {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (j : ℕ) (ξ : J → ℝ) (R : ℝ) (hR : R ≠ 0) (hs : s ≠ 0)
    (hden : ∀ u : DoubleAngularVector N, ∀ f ∈ Jᶜ,
      sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0) :
    (∫ u, sourceAuxiliaryJet r s w J j ξ u) =
      (R : ℂ)^j * ∫ u,
        sourceIBPAmplitude w J j ((r,s),((fun f => ξ f/R),R⁻¹)) u *
        Complex.exp ((R : ℂ) * sourceIBPPhase J ((r,s),((fun f => ξ f/R),R⁻¹)) u) := by
  simp_rw [sourceAuxiliaryJet_normalize r s w J j ξ R hR _ hs (hden _), mul_assoc]
  exact integral_const_mul _ _

/-- At each strictly admissible radius every original source denominator is
nonzero on the entire angular torus, before any localization. -/
theorem sourceFactorDenominator_ne_zero_of_damping {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) (u : DoubleAngularVector N) (f : SingularFactorIndex N) :
    sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0 := by
  by_cases hf : validSourceFactor f
  · intro hz
    have hneg : (sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f u).re < 0 :=
      singularFactorExponent_re_negative hN hr hr1 hm _ _ (by simp) (by simp) u f 1
    rw [sourceAngularExponent_eq_denominator r s f hf u, hz, mul_zero, Complex.zero_re] at hneg
    exact lt_irrefl 0 hneg
  · rcases f with b | (⟨b,i,j⟩ | i)
    · exact (hf trivial).elim
    · change ¬ i < j at hf
      cases b <;> simp [sourceFactorDenominator, hf]
    · exact (hf trivial).elim

end
end IsingBulk.First
