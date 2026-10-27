import IsingBulk.Preferred22.ContourHomotopyJets
import IsingBulk.Preferred22.ContourDensityBridge

/-! LT22 Lemma 5.1: whole-integral equality and dimension-uniform fixed
Jacobian jets, for the literal balanced deformation. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped ContDiff

theorem exact_constrained_deformation (s : ℂ)
    (hS : 0 < (temperatureTrace s).im) (τ : ℝ) (hτ : 0≤τ)
    (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (hp0 : ∀ x, 0≤p x) (hm0 : ∀ x, 0≤m x)
    (hps : ∀ x, Real.sin x≤0 → p x=0)
    (hms : ∀ x, 0≤Real.sin x → m x=0) :
    (∀ n : ℕ, coefficient (n+1) s = deformedCoefficient n s τ 1 p m) ∧
    (∀ J : ℕ, ∃ C : ℝ, 0<C ∧ ∀ lam : ℝ, |lam| ≤ 1 →
      ∀ (n : ℕ) (θ : Fin n → ℝ) (r : ℕ), r≤J →
        ‖iteratedFDeriv ℝ r (fun x => (constrainedAngularJacobian τ lam p m x).det) θ‖ ≤
          C^(n+1)*((n+1:ℕ):ℝ)^(2*r)) := by
  constructor
  · intro n
    exact coefficient_eq_deformedCoefficient n s hS τ hτ p m hp hm hpp hmp hp0 hm0 hps hms
  · intro J
    exact constrainedAngularJacobian_homotopy_uniform_jets p m hp hm hpp hmp τ J

end
end IsingBulk.Preferred22
