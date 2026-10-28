import IsingBulk.HT22.Geometry.InverseJets
import IsingBulk.HT22.Transport.ProjectedProduct

/-! The first reciprocal cone is different from the old inverse-cube coarea
cone. In particular, this module retains the negative branch sliver. -/
namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Filter
open IsingBulk.Preferred22

def covarianceDirection : ℂ := Complex.exp (-Complex.I*((Real.pi/4:ℝ):ℂ))

theorem covarianceDirection_norm : ‖covarianceDirection‖ = 1 := by
  simp [covarianceDirection, Complex.norm_exp, Complex.mul_re]

theorem covarianceDirection_components :
    covarianceDirection.re = Real.sqrt 2/2 ∧
    covarianceDirection.im = -(Real.sqrt 2/2) := by
  simp [covarianceDirection, Complex.exp_re, Complex.exp_im, Complex.mul_re,
    Complex.mul_im, Real.cos_pi_div_four, Real.sin_pi_div_four]

/-- The reciprocal of the entire fourth quadrant has a protected π/4
projection. No positive-real-side condition is imposed on the source u. -/
theorem first_reciprocal_cone (z : ℂ) (hr : 0 ≤ z.re) (hi : z.im ≤ 0) :
    (1/2:ℝ)*‖z⁻¹‖ ≤ (covarianceDirection*z⁻¹).re := by
  have hri : 0 ≤ (z⁻¹).re := by
    rw [Complex.inv_re]
    exact div_nonneg hr (Complex.normSq_nonneg z)
  have hii : 0 ≤ (z⁻¹).im := by
    rw [Complex.inv_im]
    exact div_nonneg (neg_nonneg.mpr hi) (Complex.normSq_nonneg z)
  have hn := Complex.norm_le_abs_re_add_abs_im (z⁻¹)
  rw [abs_of_nonneg hri, abs_of_nonneg hii] at hn
  obtain ⟨hdre,hdim⟩ := covarianceDirection_components
  rw [Complex.mul_re, hdre, hdim]
  have hs : 1 ≤ Real.sqrt 2 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hri,
    mul_nonneg (sub_nonneg.mpr hs) hii]

/-- Uniform source sine control on both sides of the lower branch point.
Constants depend on the fixed branch geometry, before ε, δ, or u are chosen. -/
theorem outward_sine_all_signs (d : PreferredBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      c*Real.sqrt (|u|+ε+δ) ≤ ‖Complex.sin (outwardPlateauPhase d ε δ u)‖ ∧
      ‖Complex.sin (outwardPlateauPhase d ε δ u)‖ ≤ C*Real.sqrt (|u|+ε+δ) ∧
      0 < (Complex.sin (outwardPlateauPhase d ε δ u)).re ∧
      (Complex.sin (outwardPlateauPhase d ε δ u)).im < 0 := by
  let e := d.localData
  obtain ⟨c,C,r₁,hc,hC,hr₁,hmod⟩ := IsingBulk.Branch.current_modulus_Q e
  obtain ⟨r₂,hr₂,hbranch⟩ := IsingBulk.Branch.current_branch_inclusion e
  obtain ⟨r₃,hr₃,hfactor⟩ := Metric.eventually_nhds_iff.mp
    (IsingBulk.Branch.current_factors_near_zero e)
  let r₀ := min r₁ (min r₂ r₃)
  have hr₀ : 0 < r₀ := lt_min hr₁ (lt_min hr₂ hr₃)
  let K := 2+2*e.c₀
  have hK : 0 < K := by dsimp [K]; have := e.c₀_pos; positivity
  refine ⟨Real.sqrt c, Real.sqrt (3*C*K), outwardTransferRadius d r₀,
    Real.sqrt_pos.mpr hc, Real.sqrt_pos.mpr (by positivity),
    outwardTransferRadius_pos d hr₀, ?_⟩
  intro ε δ u hε hεr hδ hδr hur
  obtain ⟨he,ht,ht',hu'⟩ := outwardTransfer_small d (u := u) hr₀ hε hεr hδ hδr hur
  have h1 : r₀ ≤ r₁ := min_le_left _ _
  have h2 : r₀ ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : r₀ ≤ r₃ := (min_le_right _ _).trans (min_le_right _ _)
  let t := δ+e.c₀*ε
  have htime : 0 ≤ t := ht
  obtain ⟨hlo,hhi⟩ := hmod ε t u hε (he.trans_le h1) htime (ht'.trans_le h1) (hu'.trans_le h1)
  obtain ⟨hwr,hwi⟩ := hbranch ε t u hε (he.trans_le h2) htime (ht'.trans_le h2) (hu'.trans_le h2)
  have hz : dist (ε,t,u) (0:ℝ × ℝ × ℝ) < r₃ := by
    simpa only [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, abs_of_pos hε,
      abs_of_nonneg htime, max_lt_iff] using
      And.intro (he.trans_le h3) (And.intro (ht'.trans_le h3) (hu'.trans_le h3))
  obtain ⟨_,_,hflo,hfhi⟩ := hfactor hz
  let W := IsingBulk.Branch.currentW e ε t u
  let D := IsingBulk.Branch.currentD e ε t u
  let z := Complex.sqrt (1-W^2)
  have hfactorization : 1-W^2 = D*(2-D) := by dsimp [W,D,IsingBulk.Branch.currentD]; ring
  have hnsq : ‖z‖^2 = ‖D‖*‖2-D‖ := by
    rw [← norm_pow, IsingBulk.Branch.sqrt_sq, hfactorization, norm_mul]
  have hnormlo : c*(|u|+ε+δ) ≤ ‖z‖^2 := by
    have hQ : |u|+ε+δ ≤ |u|+ε+e.tau*t := by
      change |u|+ε+δ ≤ |u|+ε+2*(δ+e.c₀*ε)
      nlinarith [mul_nonneg e.c₀_pos.le hε.le]
    have hcQ := mul_le_mul_of_nonneg_left hQ hc.le
    rw [hnsq]
    change 1 ≤ ‖2-D‖ at hflo
    change c*(|u|+ε+e.tau*t) ≤ ‖D‖ at hlo
    nlinarith [mul_le_mul_of_nonneg_left hflo (norm_nonneg D)]
  have hnormhi : ‖z‖^2 ≤ 3*C*K*(|u|+ε+δ) := by
    have hQ : |u|+ε+e.tau*t ≤ K*(|u|+ε+δ) := by
      change |u|+ε+2*(δ+e.c₀*ε) ≤ (2+2*e.c₀)*(|u|+ε+δ)
      nlinarith [abs_nonneg u, mul_nonneg e.c₀_pos.le (abs_nonneg u), mul_nonneg e.c₀_pos.le hδ]
    have hcQ := mul_le_mul_of_nonneg_left hQ hC.le
    rw [hnsq]
    change ‖2-D‖ ≤ 3 at hfhi
    change ‖D‖ ≤ C*(|u|+ε+e.tau*t) at hhi
    nlinarith [mul_le_mul_of_nonneg_left hfhi (norm_nonneg D)]
  have hzim : (1-W^2).im < 0 := by
    simp only [pow_two, Complex.sub_im, Complex.one_im, Complex.mul_im]
    change 0 < W.re at hwr
    change 0 < W.im at hwi
    nlinarith [mul_pos hwr hwi]
  obtain ⟨hzr,hzi⟩ := IsingBulk.Branch.sqrt_lower_orientation (1-W^2) hzim
  have hsine : Complex.sin (outwardPlateauPhase d ε δ u) = z := by
    rw [← outwardPlateauPhase_transfer]
    exact IsingBulk.Branch.sin_lowerArccos W
  rw [hsine]
  refine ⟨?_,?_,hzr,hzi⟩
  · have hh := Real.sqrt_le_sqrt hnormlo
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg z)] at hh
    exact hh
  · have hh := Real.sqrt_le_sqrt hnormhi
    rw [Real.sqrt_mul (by positivity : 0 ≤ 3*C*K), Real.sqrt_sq (norm_nonneg z)] at hh
    exact hh

end
end IsingBulk.HT22.Geometry
