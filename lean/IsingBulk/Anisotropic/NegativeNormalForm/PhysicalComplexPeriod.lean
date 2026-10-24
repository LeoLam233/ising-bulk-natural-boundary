import IsingBulk.Anisotropic.NegativeNormalForm.ComplexShapePeriod
import IsingBulk.Anisotropic.NegativeNormalForm.HessianBounds
import IsingBulk.Anisotropic.NegativeDominance.PeriodNormalization

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.First Filter
open scoped Topology

theorem centralHessian_uniform_rightHalfPlane (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) :
    ∃ r : ℝ, 0<r ∧ ∀ d : ℂ, ‖d‖<r → 0<(centralHessian B phi d).re := by
  have hc : ContinuousAt (fun d : ℂ => (centralHessian B phi d).re) 0 :=
    Complex.continuous_re.continuousAt.comp (centralHessian_analyticAt_zero B phi hB).continuousAt
  have he : ∀ᶠ d in 𝓝 (0:ℂ), 0<(centralHessian B phi d).re :=
    hc (Ioi_mem_nhds (by simp [centralHessian_zero]))
  obtain ⟨r,hr,he⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨r,hr,fun d hd => he (by simpa using hd)⟩

theorem centralDensity_complex_period_eq_model {n : ℕ} (hn : Odd n) (hn3 : 3≤n)
    (Bn rootBn H : ℂ) (s : ℝ) (hH : 0<H.re) (j : ℕ) (haj : alpha n≤j) :
    2*centralDensity Bn rootBn s n*shapePeriod (n-1) j (tau n) (H/(2*(n:ℂ)))=
      model Bn rootBn H s n j := by
  rw [negativeEdge_complex_period hn hn3 j haj H hH,←mul_assoc]
  exact central_period_eq_model Bn rootBn H s hn hn3 j haj

/-- The actual center residue times the literal complex-Hessian period equals
M(n,j), with no artificial insertion of h^-alpha. -/
theorem regularResidue_complex_period_eq_model {n : ℕ} (hn : Odd n) (hn3 : 3≤n)
    (B rootB : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ)
    (hd : 1-Complex.cos d=(tau n:ℂ)) (hB : AnalyticAt ℂ B (tau n))
    (T : Config n → ℂ) (hT : T 0=(tau n:ℂ)) (hBn : B (tau n)≠0)
    (hr : rootB (tau n)≠0) (hsq : rootB (tau n)^2=B (tau n))
    (hH : 0<(centralHessian B phi d).re) (j : ℕ) (haj : alpha n≤j) :
    2*regularResidue B rootB phi hphi d T 0*
      shapePeriod (n-1) j (tau n) (centralHessian B phi d/(2*(n:ℂ)))=
        model (B (tau n)) (rootB (tau n)) (centralHessian B phi d) (Real.sin phi) n j := by
  rw [negativeEdge_complex_period hn hn3 j haj _ hH,←mul_assoc]
  exact regularResidue_period_eq_model hn hn3 B rootB phi hphi d hd hB T hT hBn hr hsq _ j haj

end
end IsingBulk.Anisotropic.NegativeNormalForm
