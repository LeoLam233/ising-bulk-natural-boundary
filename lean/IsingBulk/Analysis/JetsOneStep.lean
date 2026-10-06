import IsingBulk.Analysis.JetsPullback

/-! Analytic one-step recurrence on a coefficient times an unfactored
numerator jet. The kernel is the actual source kernel, whose transport
derivative has been proved zero. This is not an all-order expansion. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Branch
open scoped BigOperators

theorem regularDensityStep_coefficient_numerator {N : ℕ} (p q : Fin N)
    (C Q : ℂ → (Fin N → ℂ) → ℂ) (s : ℂ) (φ : Fin N → ℂ)
    (hC : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => C z.1 z.2) (s,φ))
    (hQ : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => Q z.1 z.2) (s,φ))
    (hs : s ≠ 0) (hslit : ∀ i, 1-(s+s⁻¹-Complex.cos (φ i))^2 ∈ Complex.slitPlane)
    (hd : ∀ i, 1-(regularY s (φ i))^(-2:ℤ) ≠ 0)
    (hg : ∀ i, regularG s (φ i) ≠ 0) (hn : ∀ i, Complex.sin (φ i) ≠ 0)
    (hpq : regularB s (φ p)-regularB s (φ q) ≠ 0) (hK : regularKernel s φ ≠ 0) :
    regularDensityStep p q (fun t ψ => C t ψ*Q t ψ/regularKernel t ψ) s φ =
      (deriv (fun t => C t φ) s*Q s φ +
        (∑ i, regularResidualField p q s φ i*fderiv ℂ (C s) φ (Pi.single i 1))*Q s φ +
        residualDivergence p q (s,φ)*C s φ*Q s φ +
        C s φ*(∑ i, regularResidualField p q s φ i*fderiv ℂ (Q s) φ (Pi.single i 1)) +
        C s φ*deriv (fun t => Q t φ) s)/regularKernel s φ := by
  have hc := regularTransport_hasDerivAt p q C s φ hC
  have hq := regularTransport_hasDerivAt p q Q s φ hQ
  have hY := regularYProduct_transport p q s φ hs hslit hd hg hn hpq
  have hZ := regularZProduct_transport p q s φ
  have hk := (hY.const_sub 1).fun_mul (hZ.const_sub 1)
  have hk0 : (1-regularYProduct (s+0) (fun i => φ i+0*regularResidualField p q s φ i))*
      (1-regularZProduct (s+0) (fun i => φ i+0*regularResidualField p q s φ i)) ≠ 0 := by
    simpa only [regularKernel, zero_mul, add_zero] using hK
  have he := ((hc.fun_mul hq).fun_div hk hk0).deriv
  change regularTransport p q (fun t ψ => C t ψ*Q t ψ/regularKernel t ψ) s φ = _ at he
  simp only [zero_mul, add_zero, neg_zero, mul_zero, sub_zero] at he
  change regularTransport p q (fun t ψ => C t ψ*Q t ψ/regularKernel t ψ) s φ =
    (regularTransport p q C s φ*Q s φ+C s φ*regularTransport p q Q s φ)*
      regularKernel s φ/(regularKernel s φ)^2 at he
  rw [regularDensityStep, he, regularTransport_eq_partials p q C s φ hC,
    regularTransport_eq_partials p q Q s φ hQ]
  field_simp
  ring

end
end IsingBulk.Jets
