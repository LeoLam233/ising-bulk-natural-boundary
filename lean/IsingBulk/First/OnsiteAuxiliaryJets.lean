import IsingBulk.First.OnsiteUniform
import IsingBulk.First.ComplementAuxiliaryJets

/-! Exact unnormalization of genuine fixed-radius s-derivatives before the
angular integral. The scalar Rʲ cost is explicit. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators

def onsiteAuxiliaryJet {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (j : ℕ) (ξ : J → ℝ) (u : DoubleAngularVector N) : ℂ :=
  (deriv^[j] (fun z => onsiteRegularAmplitude r z w J u *
    Complex.exp (sourcePhaseSum r z (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u))) s

/-- Exact normalization of the literal s-jet on one auxiliary ray. -/
theorem onsiteAuxiliaryJet_normalize {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (j : ℕ) (ξ : J → ℝ) (R : ℝ) (hR : R ≠ 0) (u : DoubleAngularVector N)
    (hs : s ≠ 0)
    (hden : ∀ f ∈ Jᶜ, onsiteFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0) :
    onsiteAuxiliaryJet r s w J j ξ u =
      (R : ℂ)^j * onsiteIBPAmplitude w J j ((r,s),((fun f => ξ f/R),R⁻¹)) u *
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
  have he : (fun z => onsiteRegularAmplitude r z w J u *
      Complex.exp (sourcePhaseSum r z (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u)) =
      (fun z => onsiteRegularAmplitude r z w J u * Complex.exp (sourceTemperaturePhase z*((R : ℂ)*v)+H)) := by
    funext z
    rw [hphase]
  unfold onsiteAuxiliaryJet
  rw [he, normalizedParameterJet_derivative_at _ _
    (onsiteRegularAmplitude_analyticAt r w J u hs hden) (sourceTemperaturePhase_analyticAt hs)
    (R : ℂ) v H (Complex.ofReal_ne_zero.mpr hR) j, ← hphase s]
  rw [sourcePhaseSum_normalize r s _ _ _ ξ R hR u]
  simp only [onsiteIBPAmplitude, sourceIBPPhase, onsiteNormalizedAmplitude, Complex.ofReal_inv]
  rfl

/-- The explicit Rʲ factor leaves the actual angular integral unchanged. -/
theorem integral_onsiteAuxiliaryJet_normalize {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (j : ℕ) (ξ : J → ℝ) (R : ℝ) (hR : R ≠ 0) (hs : s ≠ 0)
    (hden : ∀ u : DoubleAngularVector N, ∀ f ∈ Jᶜ,
      onsiteFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0) :
    (∫ u, onsiteAuxiliaryJet r s w J j ξ u) =
      (R : ℂ)^j * ∫ u,
        onsiteIBPAmplitude w J j ((r,s),((fun f => ξ f/R),R⁻¹)) u *
        Complex.exp ((R : ℂ) * sourceIBPPhase J ((r,s),((fun f => ξ f/R),R⁻¹)) u) := by
  simp_rw [onsiteAuxiliaryJet_normalize r s w J j ξ R hR _ hs (hden _), mul_assoc]
  exact integral_const_mul _ _

theorem onsiteFactorDenominator_ne_zero_of_damping {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) (u : DoubleAngularVector N) (f : SingularFactorIndex N) :
    onsiteFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0 := by
  cases f with
  | inl b => exact one_ne_zero
  | inr f => exact sourceFactorDenominator_ne_zero_of_damping hN hr hr1 hm u (.inr f)

end
end IsingBulk.First
