import IsingBulk.Analysis.BranchAttenuation

/-! The actual second angular derivative, using locality on the open branch
quadrant rather than differentiation of a pointwise equality. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology

theorem real_parameter_sin_derivative {f : ℝ → ℂ} {f' : ℂ} {u : ℝ}
    (h : HasDerivAt f f' u) :
    HasDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f u)*f') u := by
  have hd := ((Complex.hasDerivAt_sin (f u)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt u h
  simpa [Function.comp_def,mul_comm] using hd

theorem current_phase_sin_ne_zero (d : LocalBranchData) (ε t u : ℝ)
    (hre : 0 < (currentW d ε t u).re) (him : 0 < (currentW d ε t u).im) :
    Complex.sin (currentPhase d ε t u) ≠ 0 := by
  have hhi : (1-(currentW d ε t u)^2).im < 0 := by
    simp [pow_two,Complex.mul_im]
    nlinarith [mul_pos hre him]
  intro hs
  have he : Complex.sin (currentPhase d ε t u)^2 = 1-(currentW d ε t u)^2 := by
    rw [currentPhase,sin_lowerArccos,sqrt_sq]
  rw [hs,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at he
  have hi := congrArg Complex.im he
  simp only [Complex.zero_im] at hi
  linarith

theorem current_phase_quadrant_near (d : LocalBranchData) (ε t u : ℝ)
    (hre : 0 < (currentW d ε t u).re) (him : 0 < (currentW d ε t u).im) :
    ∀ᶠ v in 𝓝 u, 0 < (currentW d ε t v).re ∧ 0 < (currentW d ε t v).im := by
  have hc : ContinuousAt (currentW d ε t) u := by
    change ContinuousAt (fun v : ℝ => plateauW (radialParameter d.theta ε)
      (-d.c₀*ε+d.tau*t/2) d.thetaB (v:ℂ)) u
    unfold plateauW
    fun_prop
  have hr := (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) u).eventually_lt
    (Complex.continuous_re.continuousAt.comp hc) hre
  have hi := (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) u).eventually_lt
    (Complex.continuous_im.continuousAt.comp hc) him
  exact hr.and hi

theorem currentPhase_second_hasDerivAt (d : LocalBranchData) (ε t u : ℝ)
    (hre : 0 < (currentW d ε t u).re) (him : 0 < (currentW d ε t u).im) :
    HasDerivAt (deriv (currentPhase d ε t))
      (currentDuu d ε t u/Complex.sin (currentPhase d ε t u)-
        (currentDu d ε t u)^2*currentW d ε t u/Complex.sin (currentPhase d ε t u)^3) u := by
  have hp := currentPhase_hasDerivAt d ε t u hre him
  have hs := real_parameter_sin_derivative hp
  have hcos : Complex.cos (currentPhase d ε t u) = currentW d ε t u := cos_lowerArccos _
  rw [hcos] at hs
  have hn := current_phase_sin_ne_zero d ε t u hre him
  have hd := (currentDu_hasDerivAt d ε t u).div hs hn
  have hv : deriv (currentPhase d ε t) =ᶠ[𝓝 u]
      (fun v => currentDu d ε t v/Complex.sin (currentPhase d ε t v)) := by
    filter_upwards [current_phase_quadrant_near d ε t u hre him] with v hv
    exact (currentPhase_hasDerivAt d ε t v hv.1 hv.2).deriv
  have he : (currentDuu d ε t u*Complex.sin (currentPhase d ε t u)-
      currentDu d ε t u*(currentW d ε t u*(currentDu d ε t u/Complex.sin (currentPhase d ε t u)))) /
        Complex.sin (currentPhase d ε t u)^2 =
      currentDuu d ε t u/Complex.sin (currentPhase d ε t u)-
        (currentDu d ε t u)^2*currentW d ε t u/Complex.sin (currentPhase d ε t u)^3 := by
    field_simp
  rw [he] at hd
  exact hd.congr_of_eventuallyEq hv

theorem currentPhase_second_deriv (d : LocalBranchData) (ε t u : ℝ)
    (hre : 0 < (currentW d ε t u).re) (him : 0 < (currentW d ε t u).im) :
    deriv (deriv (currentPhase d ε t)) u =
      currentDuu d ε t u/Complex.sqrt (1-(currentW d ε t u)^2)-
        (currentDu d ε t u)^2*(1-currentD d ε t u)/
          Complex.sqrt (1-(currentW d ε t u)^2)^3 := by
  rw [(currentPhase_second_hasDerivAt d ε t u hre him).deriv,currentPhase,sin_lowerArccos]
  simp [currentD]

theorem realPhase_deriv (d : LocalBranchData) (ε t u : ℝ)
    (hre : 0 < (currentW d ε t u).re) (him : 0 < (currentW d ε t u).im) :
    deriv (fun v => (currentPhase d ε t v).re) u = (deriv (currentPhase d ε t) u).re := by
  have h := currentPhase_hasDerivAt d ε t u hre him
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h
  simpa [Function.comp_def,h.deriv] using hr.deriv

end
end IsingBulk.Branch
