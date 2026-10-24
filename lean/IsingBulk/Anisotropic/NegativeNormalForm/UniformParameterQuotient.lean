import IsingBulk.Anisotropic.NegativeNormalForm.TripleScalarIdentity
import IsingBulk.Anisotropic.NegativeNormalForm.PoleSeparableMap

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

/-- Explicit removable parameter factor, with both the center angle and t varying. -/
def parameterFactor (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (t d : ℂ) : ℂ :=
  B t / hyperbolicDivisor ((phi:ℂ)*Complex.I)
    (negativePhase B phi hphi t d-(phi:ℂ)*Complex.I)

 theorem parameterDivisor_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => hyperbolicDivisor ((phi:ℂ)*Complex.I)
      (negativePhase B phi hphi p.1 p.2-(phi:ℂ)*Complex.I)) (0,0) := by
  have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => negativePhase B phi hphi p.1 p.2) (0,0) := by
    simpa using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  have hg0 : negativePhase B phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center B phi hphi 0
  exact (hyperbolicDivisor_analyticAt ((phi:ℂ)*Complex.I)).fun_comp_of_eq
    (f := fun p : ℂ × ℂ => ((phi:ℂ)*Complex.I,
      negativePhase B phi hphi p.1 p.2-(phi:ℂ)*Complex.I))
    (analyticAt_const.prod (hg.sub analyticAt_const)) (by simp [hg0])

 theorem parameterFactor_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => parameterFactor B phi hphi p.1 p.2) (0,0) := by
  have hg0 : negativePhase B phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center B phi hphi 0
  apply (hB.comp (f := fun p : ℂ × ℂ => p.1) analyticAt_fst).div
    (parameterDivisor_analyticAt B phi hphi hB)
  simpa [hg0,Complex.sinh_mul_I,←Complex.ofReal_sin] using
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero

 theorem phaseParameterQuotient_eq_factor_eventually (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0), phaseParameterQuotient B phi hphi p.2 p.1=
      parameterFactor B phi hphi p.1 p.2 := by
  have hg0 : negativePhase B phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center B phi hphi 0
  have hden : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0), hyperbolicDivisor ((phi:ℂ)*Complex.I)
      (negativePhase B phi hphi p.1 p.2-(phi:ℂ)*Complex.I) ≠ 0 := (parameterDivisor_analyticAt B phi hphi hB).continuousAt.eventually_ne
    (by simpa [hg0,Complex.sinh_mul_I,←Complex.ofReal_sin] using
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero)
  have hcosh : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0),
      Complex.cosh (negativePhase B phi hphi p.1 p.2)=negativeDispersion B (Real.cos phi) p.1 p.2 := by
    simpa using negativePhase_cosh_eventually B phi hphi 0 (by simpa using hB)
  have htau : ContinuousAt (fun p : ℂ × ℂ => 1-Complex.cos p.2) (0,0) := by fun_prop
  have hBe : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0), AnalyticAt ℂ B (1-Complex.cos p.2) := by
    have htau' : Filter.Tendsto (fun p : ℂ × ℂ => 1-Complex.cos p.2) (𝓝 (0,0)) (𝓝 0) := by simpa using htau.tendsto
    exact htau'.eventually hB.eventually_analyticAt
  filter_upwards [hden,hcosh,hBe] with p hp hc hb
  by_cases he : p.1=1-Complex.cos p.2
  · rw [he,phaseParameterQuotient_center B phi hphi p.2 hb]
    simp only [parameterFactor,negativePhase_center,sub_self,hyperbolicDivisor_zero,Complex.sinh_mul_I,←Complex.ofReal_sin,div_eq_mul_inv]
    ring
  · have hf := cosh_increment_factor ((phi:ℂ)*Complex.I)
      (negativePhase B phi hphi p.1 p.2-(phi:ℂ)*Complex.I)
    simp only [add_sub_cancel] at hf
    rw [hc,Complex.cosh_mul_I,←Complex.ofReal_cos,
      phaseParameterQuotient_identity B phi hphi p.2 p.1] at hf
    have hz : p.1-(1-Complex.cos p.2) ≠ 0 := sub_ne_zero.mpr he
    apply (eq_div_iff hp).2
    have hzprod : (p.1-(1-Complex.cos p.2)) *
        (phaseParameterQuotient B phi hphi p.2 p.1 *
          hyperbolicDivisor ((phi:ℂ)*Complex.I)
            (negativePhase B phi hphi p.1 p.2-(phi:ℂ)*Complex.I)-B p.1)=0 := by
      unfold negativeDispersion at hf
      rw [phaseParameterQuotient_identity B phi hphi p.2 p.1]
      linear_combination -hf
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzprod).resolve_left hz)

 theorem phaseParameterQuotient_joint_origin_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => phaseParameterQuotient B phi hphi p.2 p.1) (0,0) := by
  apply (parameterFactor_analyticAt B phi hphi hB).congr
  filter_upwards [phaseParameterQuotient_eq_factor_eventually B phi hphi hB] with p hp using hp.symm

end
end IsingBulk.Anisotropic.NegativeNormalForm
