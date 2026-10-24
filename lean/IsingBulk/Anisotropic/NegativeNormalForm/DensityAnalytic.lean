import IsingBulk.Anisotropic.NegativeNormalForm.DensityFactors

/-! Holomorphy and nonvanishing of the complete Vandermonde-divided density.
These finite-dimensional facts do not assert the dimension-uniform logarithmic bound. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology BigOperators
open IsingBulk.First IsingBulk.Anisotropic.NegativeDominance

theorem phaseAlongPole_analyticAt {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (T : Config n → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0 = 1-Complex.cos d) (i : Fin n) :
    AnalyticAt ℂ (fun v => negativePhase B phi hphi (T v) (d+v i)) 0 := by
  apply (negativePhase_analyticAt_center B phi hphi d hB).comp_of_eq
    (hT.prod (analyticAt_const.add ((ContinuousLinearMap.proj i : Config n →L[ℂ] ℂ).analyticAt _)))
  simp [hT0]

theorem regularNumerator_analyticAt {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (hr : AnalyticAt ℂ rootB (1-Complex.cos d)) (T : Config n → ℂ)
    (hT : AnalyticAt ℂ T 0) (hT0 : T 0 = 1-Complex.cos d) :
    AnalyticAt ℂ (fun v => regularNumerator B rootB phi hphi d (T v) v) 0 := by
  have hs : (Real.sin phi : ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero
  have hg := phaseAlongPole_analyticAt B phi hphi d hB T hT hT0
  have hpre : AnalyticAt ℂ (fun v => densityPrefactor B rootB n (T v)) 0 :=
    ((hr.comp_of_eq hT hT0).mul ((hB.comp_of_eq hT hT0).pow _)).div_const
  have hone : AnalyticAt ℂ (fun v => ∏ i,
      (Complex.sinh (negativePhase B phi hphi (T v) (d+v i)))⁻¹) 0 := by
    apply Finset.analyticAt_fun_prod
    intro i _
    apply (Complex.analyticAt_sinh.comp (hg i)).inv
    simpa [hT0, negativePhase_center, Complex.sinh_mul_I, ← Complex.ofReal_sin] using hs
  have hpair : AnalyticAt ℂ (fun v => ∏ p ∈ firstStrictPairs n,
      (halfSineSlope (v p.1-v p.2) / pairDenominator B phi hphi d (T v) (v p.1) (v p.2))^2) 0 := by
    apply Finset.analyticAt_fun_prod
    intro p _
    apply AnalyticAt.pow
    have hdiff : AnalyticAt ℂ (fun v : Config n => v p.1-v p.2) 0 :=
      ((ContinuousLinearMap.proj p.1 : Config n →L[ℂ] ℂ).analyticAt _).sub
      ((ContinuousLinearMap.proj p.2 : Config n →L[ℂ] ℂ).analyticAt _)
    have hnum := halfSineSlope_analyticAt.comp_of_eq hdiff (by simp)
    have hden := Complex.analyticAt_sinh.comp (((hg p.1).add (hg p.2)).div_const (c := 2))
    apply hnum.div hden
    have hh : ((phi : ℂ)*Complex.I+(phi : ℂ)*Complex.I)/2 = (phi : ℂ)*Complex.I := by ring
    simpa [hT0, negativePhase_center, hh, Complex.sinh_mul_I, ← Complex.ofReal_sin] using hs
  exact (hpre.mul hone).mul hpair

theorem regularNumerator_center_ne_zero {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : B (1-Complex.cos d) ≠ 0) (hr : rootB (1-Complex.cos d) ≠ 0) :
    regularNumerator B rootB phi hphi d (1-Complex.cos d) (0 : Config n) ≠ 0 := by
  rw [regularNumerator_center]
  have hs : (Real.sin phi : ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply div_ne_zero (mul_ne_zero hr (pow_ne_zero _ hB))
      apply mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)
      apply pow_ne_zero
      exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    · exact pow_ne_zero _ (inv_ne_zero hs)
  · exact pow_ne_zero _ (div_ne_zero (by norm_num) hs)


theorem poleParameterDerivative_eq_fderiv {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n)
    (hF : DifferentiableAt ℂ (fun z : Config n × ℂ => poleEquation B phi hphi d z.2 z.1) (v,t)) :
    poleParameterDerivative B phi hphi d t v =
      fderiv ℂ (fun z : Config n × ℂ => poleEquation B phi hphi d z.2 z.1) (v,t) (0,1) := by
  have hm : HasFDerivAt (fun u : ℂ => (v,u)) (ContinuousLinearMap.inr ℂ (Config n) ℂ) t := by
    simpa using ((ContinuousLinearMap.inr ℂ (Config n) ℂ).hasFDerivAt (x := t)).const_add (v,0)
  have h := hF.hasFDerivAt.comp t hm
  exact h.hasDerivAt.deriv

theorem poleParameterDerivative_analyticAt {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (T : Config n → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0 = 1-Complex.cos d) :
    AnalyticAt ℂ (fun v => poleParameterDerivative B phi hphi d (T v) v) 0 := by
  let F : Config n × ℂ → ℂ := fun z => poleEquation B phi hphi d z.2 z.1
  have hF : AnalyticAt ℂ F (0,1-Complex.cos d) := poleEquation_analyticAt_center B phi hphi d hB
  let L : ((Config n × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,1)
  have hg : AnalyticAt ℂ (fun v => (v,T v)) 0 := analyticAt_id.prod hT
  have hparam : AnalyticAt ℂ (fun v => L (fderiv ℂ F (v,T v))) 0 :=
    ((L.analyticAt _).comp hF.fderiv).comp_of_eq hg (by simp [hT0])
  have ht : Filter.Tendsto (fun v => (v,T v)) (𝓝 0) (𝓝 (0,1-Complex.cos d)) := by
    simpa [hT0] using hg.continuousAt.tendsto
  apply hparam.congr
  filter_upwards [ht.eventually hF.eventually_analyticAt] with v hv
  exact (poleParameterDerivative_eq_fderiv B phi hphi d (T v) v hv.differentiableAt).symm

theorem regularResidue_analyticAt {n : ℕ} (hn : n ≠ 0) (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d))
    (hBn : B (1-Complex.cos d) ≠ 0) (hr : AnalyticAt ℂ rootB (1-Complex.cos d))
    (T : Config n → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0 = 1-Complex.cos d) :
    AnalyticAt ℂ (regularResidue B rootB phi hphi d T) 0 := by
  apply (analyticAt_const.mul (regularNumerator_analyticAt B rootB phi hphi d hB hr T hT hT0)).div
    (poleParameterDerivative_analyticAt B phi hphi d hB T hT hT0)
  rw [hT0]
  have hd := (poleEquation_hasDerivAt_center (n := n) B phi hphi d _ hB.differentiableAt.hasDerivAt).deriv
  change deriv _ _ ≠ 0
  rw [hd]
  exact poleEquation_parameter_derivative_ne_zero hn B phi hphi d hBn

theorem regularResidue_eventually_ne_zero {n : ℕ} (hn : n ≠ 0)
    (B rootB : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hr : AnalyticAt ℂ rootB (1-Complex.cos d)) (hrn : rootB (1-Complex.cos d) ≠ 0)
    (T : Config n → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0 = 1-Complex.cos d) :
    ∀ᶠ v in 𝓝 (0 : Config n), regularResidue B rootB phi hphi d T v ≠ 0 := by
  apply (regularResidue_analyticAt hn B rootB phi hphi d hB hBn hr T hT hT0).continuousAt.eventually_ne
  apply div_ne_zero
  · apply mul_ne_zero (by norm_num)
    rw [hT0]
    exact regularNumerator_center_ne_zero B rootB phi hphi d hBn hrn
  · rw [hT0]
    change deriv _ _ ≠ 0
    rw [(poleEquation_hasDerivAt_center (n := n) B phi hphi d _ hB.differentiableAt.hasDerivAt).deriv]
    exact poleEquation_parameter_derivative_ne_zero hn B phi hphi d hBn

end
end IsingBulk.Anisotropic.NegativeNormalForm
