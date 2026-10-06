import IsingBulk.Analysis.BranchData

/-! Analytic Taylor bounds used for the actual local dispersion. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology

theorem analytic_quadratic_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (hf : AnalyticAt ℂ f 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 (0:E),
      ‖f z-f 0-fderiv ℂ f 0 z‖ ≤ C*‖z‖^2 := by
  obtain ⟨p,hp⟩ := hf
  have he : ∀ z : E, p.partialSum 2 z = f 0+fderiv ℂ f 0 z := by
    intro z
    have h₁ : p 1 (fun _ => z) = fderiv ℂ f 0 z := by
      rw [hp.fderiv_eq,continuousMultilinearCurryFin1_apply]
      congr 1
    simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,Finset.sum_range_zero,
      zero_add,hp.coeff_zero,h₁]
  obtain ⟨C,hC,hb⟩ := (hp.isBigO_sub_partialSum_pow 2).exists_pos
  refine ⟨C,hC,?_⟩
  filter_upwards [hb.bound] with z hz
  simpa only [zero_add,he,sub_add_eq_sub_sub,Real.norm_eq_abs,abs_pow,abs_norm] using hz

theorem shifted_cosh_remainder (b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 (0:ℂ),
      ‖Complex.cosh (-(b:ℂ)*Complex.I+z)-(Real.cos b:ℂ)+
        Complex.I*(Real.sin b:ℂ)*z‖ ≤ C*‖z‖^2 := by
  let f : ℂ → ℂ := fun z => Complex.cosh (-(b:ℂ)*Complex.I+z)
  have ha : AnalyticAt ℂ f 0 := by dsimp [f]; fun_prop
  have hd : HasDerivAt f (-Complex.I*(Real.sin b:ℂ)) 0 := by
    rw [show -Complex.I*(Real.sin b:ℂ) = -((Real.sin b:ℂ)*Complex.I) by ring]
    simpa [f,Function.comp_def,Complex.sinh_mul_I,← Complex.ofReal_sin] using
      (Complex.hasDerivAt_cosh (-(b:ℂ)*Complex.I+0)).comp 0
        ((hasDerivAt_id (0:ℂ)).const_add (-(b:ℂ)*Complex.I))
  have hval : f 0 = (Real.cos b:ℂ) := by simp [f,Complex.cosh_mul_I,← Complex.ofReal_cos]
  obtain ⟨C,hC,hb⟩ := analytic_quadratic_remainder f ha
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with z hz
  rw [hval,fderiv_eq_deriv_mul,hd.deriv] at hz
  convert hz using 1
  congr 1
  dsimp [f]
  ring

theorem original_remainder_identity (d : LocalBranchData) (ε u : ℝ) (hε : 1+ε ≠ 0) :
    originalD d ε u-((d.a:ℂ)*u-Complex.I*(d.b:ℂ)*ε) =
      (Complex.cosh (-(d.thetaB:ℂ)*Complex.I+(-(d.c₀:ℂ)*ε+(u:ℂ)*Complex.I))-
        (Real.cos d.thetaB:ℂ)+Complex.I*(d.a:ℂ)*(-(d.c₀:ℂ)*ε+(u:ℂ)*Complex.I))-
      ((ε^2/(1+ε):ℝ):ℂ)*((Real.cos d.theta:ℂ)-Complex.I*(Real.sin d.theta:ℂ)) := by
  have ha : (Real.cos d.thetaB:ℂ) = 2*(Real.cos d.theta:ℂ)-1 := by
    exact_mod_cast d.angle_relation
  rw [originalD,← branchDModel_eq d ε 0 u hε]
  unfold branchDModel radialTraceModel LocalBranchData.b LocalBranchData.a
  push_cast
  push_cast at ha
  rw [ha]
  have he : -(d.c₀:ℂ)*ε+(d.tau:ℂ)*0/2+(-(d.thetaB:ℂ)+(u:ℂ))*Complex.I =
      -(d.thetaB:ℂ)*Complex.I+(-(d.c₀:ℂ)*ε+(u:ℂ)*Complex.I) := by ring
  rw [he]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Explicit source Landau bound for the actual radial original branch. -/
theorem original_normal_form (d : LocalBranchData) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ ε u : ℝ,
      0 ≤ ε → ε < r → |u| < r →
      ‖originalD d ε u-((d.a:ℂ)*u-Complex.I*(d.b:ℂ)*ε)‖ ≤
        C*(u^2+ε*|u|+ε^2) := by
  obtain ⟨K,hK,hb⟩ := shifted_cosh_remainder d.thetaB
  obtain ⟨η,hη,hball⟩ := Metric.eventually_nhds_iff.mp hb
  let r := η/(2*(d.c₀+1))
  let C := 2*K*(d.c₀^2+1)+2
  have hc := d.c₀_pos
  refine ⟨C,r,by dsimp [C]; positivity,by dsimp [r]; positivity,?_⟩
  intro ε u hε hεr hur
  let w : ℂ := -(d.c₀:ℂ)*ε+(u:ℂ)*Complex.I
  have hn : ‖w‖ ≤ d.c₀*ε+|u| := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    rw [abs_of_pos hc,abs_of_nonneg hε]
  have hwr : ‖w‖ < η := by
    have hsmall : d.c₀*ε+|u| < (d.c₀+1)*r := by nlinarith
    have hrval : (d.c₀+1)*r = η/2 := by dsimp [r]; field_simp
    linarith
  have hcos := hball (show dist w 0 < η by simpa using hwr)
  have hcoef : ‖(Real.cos d.theta:ℂ)-Complex.I*(Real.sin d.theta:ℂ)‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    simpa only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      show (1:ℝ)+1=2 by norm_num] using
        add_le_add (Real.abs_cos_le_one d.theta) (Real.abs_sin_le_one d.theta)
  have hfrac : 0 ≤ ε^2/(1+ε) := by positivity
  have hfrac' : ε^2/(1+ε) ≤ ε^2 := div_le_self (sq_nonneg _) (by linarith)
  rw [original_remainder_identity d ε u (by linarith)]
  apply (norm_sub_le _ _).trans
  have hb₁ : ‖Complex.cosh (-(d.thetaB:ℂ)*Complex.I+w)-(Real.cos d.thetaB:ℂ)+
      Complex.I*(d.a:ℂ)*w‖ ≤ K*(d.c₀*ε+|u|)^2 :=
    hcos.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hK.le)
  have hb₂ : ‖((ε^2/(1+ε):ℝ):ℂ)*((Real.cos d.theta:ℂ)-Complex.I*(Real.sin d.theta:ℂ))‖ ≤ 2*ε^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hfrac]
    nlinarith [mul_le_mul hfrac' hcoef (norm_nonneg _) (sq_nonneg ε)]
  have hpoly : (d.c₀*ε+|u|)^2 ≤ 2*(d.c₀^2+1)*(u^2+ε*|u|+ε^2) := by
    nlinarith [sq_nonneg (d.c₀*ε-|u|),sq_abs u,
      mul_nonneg (sq_nonneg d.c₀) (sq_nonneg u),
      mul_nonneg (sq_nonneg d.c₀) (mul_nonneg hε (abs_nonneg u)),mul_nonneg hε (abs_nonneg u)]
  dsimp [C]
  nlinarith [mul_le_mul_of_nonneg_left hpoly hK.le,mul_nonneg hε (abs_nonneg u)]

end
end IsingBulk.Branch
