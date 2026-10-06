import IsingBulk.Analysis.RegularPair
import IsingBulk.Analysis.SelectedField
import IsingBulk.Analysis.BranchRadial
import IsingBulk.Analysis.JetsPoleFactor

/-! The actual local dispersion chart for Appendix D. The radius and branch
center are fixed during parameter differentiation. No branch estimates are
assumed. The regular scalar numerator beta is distinct from the residual
vector field and from the source's global regular analytic factor. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Branch

def sourceS (s : ℂ) : ℂ := s+s⁻¹
def sourceSPrime (s : ℂ) : ℂ := 1-(s^2)⁻¹

theorem sourceS_hasDerivAt (s : ℂ) (hs : s ≠ 0) :
    HasDerivAt sourceS (sourceSPrime s) s := by
  convert! (hasDerivAt_id s).add (hasDerivAt_inv hs) using 1

def angularY (v θ : ℝ) (u : ℂ) : ℂ :=
  Complex.exp ((v:ℂ)+(u-(θ:ℂ))*Complex.I)

def chartW (s : ℂ) (v θ : ℝ) (u : ℂ) : ℂ := dispersion s (angularY v θ u)

def chartPhase (s : ℂ) (v θ : ℝ) (u : ℂ) : ℂ := lowerArccos (chartW s v θ u)

def angularG (v θ : ℝ) (u : ℂ) : ℂ :=
  Complex.I * (angularY v θ u - (angularY v θ u)⁻¹) / 2

def chartA (s : ℂ) (v θ : ℝ) (u : ℂ) : ℂ := sourceSPrime s / (-angularG v θ u)

def chartB (s : ℂ) (v θ : ℝ) (u : ℂ) : ℂ :=
  angularG v θ u / Complex.sin (chartPhase s v θ u)

theorem angularY_hasDerivAt (v θ : ℝ) (u : ℂ) :
    HasDerivAt (angularY v θ) (Complex.I * angularY v θ u) u := by
  have h := ((((hasDerivAt_id u).sub_const (θ:ℂ)).mul_const Complex.I).const_add (v:ℂ)).cexp
  convert! h using 1
  simp [angularY, mul_comm]

theorem chartW_eq_plateauW (s : ℂ) (v θ : ℝ) (u : ℂ) :
    chartW s v θ u = plateauW s v θ u := by
  simp only [chartW, dispersion, angularY, plateauW, Complex.cosh, ← Complex.exp_neg]
  congr 3 <;> ring_nf

theorem chartW_parameter (s : ℂ) (v θ : ℝ) (u : ℂ) (hs : s ≠ 0) :
    HasDerivAt (fun t => chartW t v θ u) (sourceSPrime s) s :=
  (sourceS_hasDerivAt s hs).sub_const _

theorem chartW_angular (s : ℂ) (v θ : ℝ) (u : ℂ) :
    HasDerivAt (chartW s v θ) (-angularG v θ u) u := by
  have h := plateauW_hasDerivAt s v θ u
  have he : chartW s v θ = plateauW s v θ := funext (chartW_eq_plateauW s v θ)
  rw [he]
  convert! h using 1
  simp only [angularG, angularY, Complex.sinh, ← Complex.exp_neg]
  ring_nf

theorem chartPhase_cos (s : ℂ) (v θ : ℝ) (u : ℂ) :
    Complex.cos (chartPhase s v θ u) = chartW s v θ u := cos_lowerArccos _

theorem chartPhase_parameter (s : ℂ) (v θ : ℝ) (u : ℂ) (hs : s ≠ 0)
    (hr : 0 < (chartW s v θ u).re) (hi : 0 < (chartW s v θ u).im) :
    HasDerivAt (fun t => chartPhase t v θ u)
      (-sourceSPrime s / Complex.sin (chartPhase s v θ u)) s := by
  have h := (lowerArccos_differentiable _ hr hi).hasDerivAt
  rw [lowerArccos_deriv _ hr hi] at h
  convert! h.comp s (chartW_parameter s v θ u hs) using 1
  simp [chartPhase, div_eq_mul_inv, mul_comm]

theorem chartPhase_angular (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hr : 0 < (chartW s v θ u).re) (hi : 0 < (chartW s v θ u).im) :
    HasDerivAt (chartPhase s v θ) (chartB s v θ u) u := by
  have h := (lowerArccos_differentiable _ hr hi).hasDerivAt
  rw [lowerArccos_deriv _ hr hi] at h
  convert! h.comp u (chartW_angular s v θ u) using 1
  simp [chartPhase, chartB, div_eq_mul_inv, mul_comm]

theorem chartPhase_real_angular (s : ℂ) (v θ u : ℝ)
    (hr : 0 < (chartW s v θ (u:ℂ)).re) (hi : 0 < (chartW s v θ (u:ℂ)).im) :
    HasDerivAt (fun t : ℝ => chartPhase s v θ (t:ℂ)) (chartB s v θ (u:ℂ)) u :=
  (chartPhase_angular s v θ (u:ℂ) hr hi).comp_ofReal

theorem chartB_mul_chartA (s : ℂ) (v θ : ℝ) (u : ℂ) (hg : angularG v θ u ≠ 0) :
    chartB s v θ u * chartA s v θ u =
      -sourceSPrime s / Complex.sin (chartPhase s v θ u) := by
  unfold chartB chartA
  field_simp

theorem regularY_hasDerivAt (s φ : ℂ) (hs : s ≠ 0)
    (hslit : 1-(s+s⁻¹-Complex.cos φ)^2 ∈ Complex.slitPlane)
    (hd : 1-(regularY s φ)^(-2:ℤ) ≠ 0) :
    HasDerivAt (regularY s) (2*Complex.sin φ/(1-(regularY s φ)^(-2:ℤ))) φ := by
  have hy : DifferentiableAt ℂ (regularY s) φ :=
    (AnalyticAt.comp (f := fun z : ℂ => (s,z)) (regularY_analytic s φ hs hslit)
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have he : (fun z => dispersion s (regularY s z)) = Complex.cos := funext (dispersion_regularY s)
  have h := ((hy.hasDerivAt.add (hy.hasDerivAt.inv (regularY_ne_zero s φ))).div_const 2).const_sub (s+s⁻¹)
  change HasDerivAt (fun z => dispersion s (regularY s z)) _ φ at h
  rw [he] at h
  have hh := h.unique (Complex.hasDerivAt_cos φ)
  have heder : deriv (regularY s) φ = 2*Complex.sin φ/(1-(regularY s φ)^(-2:ℤ)) := by
    apply (eq_div_iff hd).mpr
    simp only [zpow_neg, zpow_ofNat] at hh ⊢
    field_simp [regularY_ne_zero s φ] at hh ⊢
    linear_combination -hh
  rw [← heder]
  exact hy.hasDerivAt

/-- Exact coefficient of the one-body form after the inverse coordinate
change. The original expression is compared only where its denominator is
nonzero. gamma = i*phi and z = exp(-i*phi) are the source branch values. -/
theorem one_body_jacobian (s φ : ℂ) (hs : s ≠ 0)
    (hslit : 1-(s+s⁻¹-Complex.cos φ)^2 ∈ Complex.slitPlane)
    (hd : 1-(regularY s φ)^(-2:ℤ) ≠ 0) (hφ : Complex.sin φ ≠ 0) :
    deriv (regularY s) φ / (2 * (Real.pi:ℂ) * Complex.I) *
      (Complex.exp (-Complex.I*φ) / Complex.sinh (Complex.I*φ)) =
      -Complex.exp (-Complex.I*φ) / ((Real.pi:ℂ)*(1-(regularY s φ)^(-2:ℤ))) := by
  rw [(regularY_hasDerivAt s φ hs hslit hd).deriv, mul_comm Complex.I φ, Complex.sinh_mul_I]
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  simp [Complex.I_sq]
  ring

/-- The inverse formula selects the same lower root as the angular chart.
The sign hypothesis chooses the square root; the dispersion equation alone
would not distinguish the two roots. -/
theorem regularY_chartPhase (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hg : 0 < (angularG v θ u).re) :
    regularY s (chartPhase s v θ u) = angularY v θ u := by
  have hy : angularY v θ u ≠ 0 := Complex.exp_ne_zero _
  have hH : s+s⁻¹-Complex.cos (chartPhase s v θ u) =
      (angularY v θ u+(angularY v θ u)⁻¹)/2 := by
    rw [chartPhase_cos, chartW, dispersion]
    ring
  have hsq : (angularG v θ u)^2 =
      1-((angularY v θ u+(angularY v θ u)⁻¹)/2)^2 := by
    unfold angularG
    field_simp
    ring_nf
    simp [Complex.I_sq]
    ring
  have hsqrt : Complex.sqrt (1-((angularY v θ u+(angularY v θ u)⁻¹)/2)^2) =
      angularG v θ u := by
    have he := sqrt_sq (1-((angularY v θ u+(angularY v θ u)⁻¹)/2)^2)
    rw [← hsq] at he
    rw [← hsq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
    · exact h
    · have hr : 0 ≤ (Complex.sqrt ((angularG v θ u)^2)).re := by
        rw [Complex.sqrt_eq_real_add_ite]
        split_ifs <;> simp <;> positivity
      have hh := congrArg Complex.re h
      simp only [Complex.neg_re] at hh
      linarith
  rw [regularY_formula, hH, hsqrt]
  unfold angularG
  ring_nf
  simp [Complex.I_sq]
  ring

theorem regularG_chartPhase (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hg : 0 < (angularG v θ u).re) :
    regularG s (chartPhase s v θ u) = angularG v θ u := by
  simp only [regularG, regularY_chartPhase s v θ u hg, angularG]

theorem regularB_chartPhase (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hg : 0 < (angularG v θ u).re) :
    regularB s (chartPhase s v θ u) = chartB s v θ u := by
  rw [regularB, regularG_chartPhase s v θ u hg]
  rfl

theorem regularY_line_derivative (s φ σ η : ℂ) (hs : s ≠ 0)
    (hslit : 1-(s+s⁻¹-Complex.cos φ)^2 ∈ Complex.slitPlane)
    (hd : 1-(regularY s φ)^(-2:ℤ) ≠ 0) :
    HasDerivAt (fun t : ℂ => regularY (s+t*σ) (φ+t*η))
      (2*(sourceSPrime s*σ+Complex.sin φ*η)/(1-(regularY s φ)^(-2:ℤ))) 0 := by
  let f : ℂ → ℂ := fun t => regularY (s+t*σ) (φ+t*η)
  have hy : DifferentiableAt ℂ f 0 := by
    apply AnalyticAt.differentiableAt
    exact AnalyticAt.comp_of_eq (g := fun z : ℂ × ℂ => regularY z.1 z.2)
      (f := fun t : ℂ => (s+t*σ,φ+t*η)) (regularY_analytic s φ hs hslit)
      (show AnalyticAt ℂ (fun t : ℂ => (s+t*σ,φ+t*η)) 0 by fun_prop) (by simp)
  have harg : HasDerivAt (fun t : ℂ => s+t*σ) σ 0 := by
    convert! ((hasDerivAt_id (0:ℂ)).mul_const σ).const_add s using 1
    simp
  have hpar : HasDerivAt (fun t : ℂ => sourceS (s+t*σ)) (sourceSPrime s*σ) 0 := by
    convert! (sourceS_hasDerivAt s hs).comp_of_eq 0 harg (by simp) using 1
  have hphi : HasDerivAt (fun t : ℂ => Complex.cos (φ+t*η)) (-Complex.sin φ*η) 0 := by
    convert! (((hasDerivAt_id (0:ℂ)).mul_const η).const_add φ).ccos using 1
    simp
  have htrace : (fun t => f t+(f t)⁻¹) = fun t => 2*sourceS (s+t*σ)-2*Complex.cos (φ+t*η) := by
    funext t
    have h := dispersion_regularY (s+t*σ) (φ+t*η)
    unfold dispersion at h
    dsimp [f, sourceS]
    linear_combination -2*h
  have hn : f 0 ≠ 0 := by simpa [f] using regularY_ne_zero s φ
  have hh := hy.hasDerivAt.add (hy.hasDerivAt.inv hn)
  change HasDerivAt (fun t => f t+(f t)⁻¹) _ 0 at hh
  rw [htrace] at hh
  have he := hh.unique ((hpar.const_mul 2).sub (hphi.const_mul 2))
  have hd' : deriv f 0 = 2*(sourceSPrime s*σ+Complex.sin φ*η)/(1-(regularY s φ)^(-2:ℤ)) := by
    apply (eq_div_iff hd).mpr
    rw [show f 0 = regularY s φ by simp [f]] at he
    generalize deriv f 0 = d at he ⊢
    simp only [zpow_neg, zpow_ofNat] at he ⊢
    field_simp [regularY_ne_zero] at he ⊢
    linear_combination he
  rw [← hd']
  exact hy.hasDerivAt

end
end IsingBulk.Jets

