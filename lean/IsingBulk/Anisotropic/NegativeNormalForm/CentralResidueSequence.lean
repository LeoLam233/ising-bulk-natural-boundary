import IsingBulk.Anisotropic.NegativeNormalForm.CentralPeriodUniformLoss
import IsingBulk.Anisotropic.NegativeDominance.BetaModelComparison

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Filter IsingBulk.First IsingBulk.Anisotropic.NegativeDominance
open scoped Topology

/-- Every actual central residue has the exact physical center and exact full
complex period normalization, uniformly along the winding sequence. -/
theorem central_residue_sequence_eventually (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (hr : AnalyticAt ℂ rootB 0) (hrn : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0:ℂ),rootB t^2=B t) :
    ∀ᶠ N : ℕ in atTop, Odd N →
      let d : ℂ := ((Real.pi/(N:ℝ):ℝ):ℂ)
      ∀ T : Config N → ℂ,T 0=1-Complex.cos d →
        regularResidue B rootB phi hphi d T 0=
          centralDensity (B (tau N)) (rootB (tau N)) (Real.sin phi) N ∧
        regularResidue B rootB phi hphi d T 0≠0 ∧
        ∀ j : ℕ,alpha N≤j →
          2*regularResidue B rootB phi hphi d T 0*
            shapePeriod (N-1) j (tau N) (centralHessian B phi d/(2*(N:ℂ)))=
            model (B (tau N)) (rootB (tau N)) (centralHessian B phi d) (Real.sin phi) N j := by
  have hp := tau_complex_tendsto_zero.eventually
    (hB.eventually_analyticAt.and ((hB.continuousAt.eventually_ne hBn).and
      ((hr.continuousAt.eventually_ne hrn).and hsq)))
  obtain ⟨F,_hF,hphase⟩ := exists_central_period_uniform_loss B phi hB
  filter_upwards [hp,hphase,eventually_ge_atTop (3:ℕ)] with N hp hphase hN ho
  dsimp only
  intro T hT
  let d : ℂ := ((Real.pi/(N:ℝ):ℝ):ℂ)
  have hd : 1-Complex.cos d=(tau N:ℂ) := by
    simp only [d,tau,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_cos]
  have hcenter := regularResidue_center_normalized ho B rootB phi hphi d
    (hd.symm ▸ hp.1) T hT (hd.symm ▸ hp.2.1) (hd.symm ▸ hp.2.2.1) (hd.symm ▸ hp.2.2.2)
  rw [hd] at hcenter
  refine ⟨hcenter,?_,?_⟩
  · rw [hcenter]
    exact centralDensity_ne_zero _ _ _ (by omega) hp.2.1 hp.2.2.1 hphi
  · intro j hj
    exact regularResidue_complex_period_eq_model ho hN B rootB phi hphi d hd hp.1 T
      (hT.trans hd) hp.2.1 hp.2.2.1 hp.2.2.2 (by linarith [hphase.1]) j hj

end
end IsingBulk.Anisotropic.NegativeNormalForm
