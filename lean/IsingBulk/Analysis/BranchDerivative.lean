import IsingBulk.Analysis.BranchInclusion

/-! Exact derivatives of the actual branch; all plateau parameters are fixed
under the real angular derivative. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology

theorem sin_lowerArccos (W : ℂ) :
    Complex.sin (lowerArccos W) = Complex.sqrt (1-W^2) := by
  have he : lowerArccos W*Complex.I = Complex.log (inverseCosineRoot W) := by
    unfold lowerArccos
    calc
      _ = -(Complex.I*Complex.I)*Complex.log (inverseCosineRoot W) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [Complex.sin,neg_mul,he,Complex.exp_neg,
    Complex.exp_log (inverseCosineRoot_ne_zero W),inverseCosineRoot_inverse,inverseCosineRoot]
  ring_nf
  simp [Complex.I_sq]

def currentDu (d : LocalBranchData) (ε t u : ℝ) : ℂ :=
  Complex.sinh (((-d.c₀*ε+d.tau*t/2:ℝ):ℂ)+
    (-(d.thetaB:ℂ)+(u:ℂ))*Complex.I)*Complex.I

def currentDuu (d : LocalBranchData) (ε t u : ℝ) : ℂ :=
  -Complex.cosh (((-d.c₀*ε+d.tau*t/2:ℝ):ℂ)+
    (-(d.thetaB:ℂ)+(u:ℂ))*Complex.I)

theorem currentD_hasDerivAt (d : LocalBranchData) (ε t u : ℝ) :
    HasDerivAt (currentD d ε t) (currentDu d ε t u) u := by
  have h := ((plateauW_hasDerivAt (radialParameter d.theta ε)
    (-d.c₀*ε+d.tau*t/2) d.thetaB (u:ℂ)).comp_ofReal).const_sub 1
  convert h using 1
  · rfl
  · dsimp [currentDu]; ring

theorem currentDu_hasDerivAt (d : LocalBranchData) (ε t u : ℝ) :
    HasDerivAt (currentDu d ε t) (currentDuu d ε t u) u := by
  let v : ℂ := ((-d.c₀*ε+d.tau*t/2:ℝ):ℂ)
  have hi : HasDerivAt (fun z : ℂ => v+(-(d.thetaB:ℂ)+z)*Complex.I) Complex.I (u:ℂ) := by
    convert (((hasDerivAt_id (u:ℂ)).const_add (-(d.thetaB:ℂ))).mul_const Complex.I).const_add v using 1 <;> simp
  have h := (((Complex.hasDerivAt_sinh (v+(-(d.thetaB:ℂ)+(u:ℂ))*Complex.I)).comp (u:ℂ) hi).mul_const Complex.I).comp_ofReal
  convert h using 1
  · rfl
  · dsimp [currentDuu]
    rw [mul_assoc,Complex.I_mul_I]
    ring

theorem currentPhase_hasDerivAt (d : LocalBranchData) (ε t u : ℝ)
    (hre : 0 < (currentW d ε t u).re) (him : 0 < (currentW d ε t u).im) :
    HasDerivAt (currentPhase d ε t)
      (currentDu d ε t u / Complex.sin (currentPhase d ε t u)) u := by
  have h := plateau_phase_hasDerivAt (radialParameter d.theta ε)
    (-d.c₀*ε+d.tau*t/2) d.thetaB u hre him
  convert h using 1
  · rfl
  · dsimp [currentDu,currentPhase,currentW]
    ring

theorem currentPhase_deriv (d : LocalBranchData) (ε t u : ℝ)
    (hre : 0 < (currentW d ε t u).re) (him : 0 < (currentW d ε t u).im) :
    deriv (currentPhase d ε t) u =
      currentDu d ε t u / Complex.sqrt (1-(currentW d ε t u)^2) := by
  rw [(currentPhase_hasDerivAt d ε t u hre him).deriv]
  exact congrArg (fun z => currentDu d ε t u/z) (sin_lowerArccos _)

theorem currentPhase_deriv_norm (d : LocalBranchData) (ε t u : ℝ)
    (hre : 0 < (currentW d ε t u).re) (him : 0 < (currentW d ε t u).im) :
    ‖deriv (currentPhase d ε t) u‖ =
      ‖currentDu d ε t u‖ / Real.sqrt ‖currentD d ε t u*(2-currentD d ε t u)‖ := by
  have hn : ‖Complex.sqrt (1-(currentW d ε t u)^2)‖ =
      Real.sqrt ‖1-(currentW d ε t u)^2‖ := by
    calc
      _ = Real.sqrt (‖Complex.sqrt (1-(currentW d ε t u)^2)‖^2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := by rw [← norm_pow,sqrt_sq]
  rw [currentPhase_deriv d ε t u hre him,norm_div,hn]
  congr 3
  dsimp [currentD]
  ring

end
end IsingBulk.Branch
