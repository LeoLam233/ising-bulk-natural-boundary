import IsingBulk.Anisotropic.NegativeNormalForm.NormalizedCorrectionBounds
import IsingBulk.Anisotropic.NegativeNormalForm.EquivariantQuantitativeInverse

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

 theorem mean_mul_analyticAt {n : ℕ} (e f : Config n → Config n) (w : Config n)
    (he : AnalyticAt ℂ e w) (hf : AnalyticAt ℂ f w) :
    AnalyticAt ℂ (fun x => mean (e x*f x)) w := by
  simpa only [Function.comp_def,meanCLM_apply] using
    ((meanCLM n).analyticAt (e w*f w)).comp (f := fun x => e x*f x) (he.mul hf)

 theorem normalizedMeanCorrection_analyticAt {n : ℕ} (e : Config n → Config n) (w : Config n)
    (he : AnalyticAt ℂ e w) (hc : AnalyticAt ℂ normalizedRankCoefficient (mean (e w*e w))) :
    AnalyticAt ℂ (fun x => normalizedMeanCorrection (e x) x) w :=
  analyticAt_id.add (((hc.comp (f := fun x => mean (e x*e x)) (mean_mul_analyticAt e e w he he)).mul
    (mean_mul_analyticAt id e w analyticAt_id he)).smul he)

 theorem normalizedMeanCorrection_hasFDerivAt {n : ℕ} (e : Config n → Config n)
    (he : AnalyticAt ℂ e 0) (he0 : e 0=0) :
    HasFDerivAt (fun x => normalizedMeanCorrection (e x) x) (ContinuousLinearMap.id ℂ (Config n)) 0 := by
  let a : Config n → ℂ := fun x => normalizedRankCoefficient (mean (e x*e x))*mean (x*e x)
  have hc : AnalyticAt ℂ normalizedRankCoefficient (mean (e 0*e 0)) := by
    simpa [he0,mean] using normalizedRankCoefficient_analyticAt
  have ha : AnalyticAt ℂ a 0 := (hc.comp (f := fun x => mean (e x*e x)) (mean_mul_analyticAt e e 0 he he)).mul
    (mean_mul_analyticAt id e 0 analyticAt_id he)
  have ha0 : a 0=0 := by simp [a,mean]
  have hh := (hasFDerivAt_id (𝕜 := ℂ) (0:Config n)).add
    (ha.differentiableAt.hasFDerivAt.smul he.differentiableAt.hasFDerivAt)
  convert! hh using 1
  ext v i
  simp [a,he0,mean]

/-- A single radius makes every dimension-normalized actual rank-one correction
an analytic 1/64-Lipschitz perturbation of the identity. -/
theorem exists_uniform_correction_radius (L : ℝ) (hL : 0<L) :
    ∃ R₀ : ℝ, 0<R₀ ∧ ∀ R : ℝ, 0<R → R≤R₀ → ∀ n : ℕ, n≠0 → ∀ e : Config n → Config n,
      AnalyticOnNhd ℂ e (ball 0 R) → e 0=0 →
      (∀ w z, ‖w‖≤R → ‖z‖≤R → ‖e w-e z‖≤L*‖w-z‖) →
      AnalyticOnNhd ℂ (fun w => normalizedMeanCorrection (e w) w) (ball 0 R) ∧
      LipschitzOnWith (1/64) (fun w => normalizedMeanCorrection (e w) w-w) (closedBall 0 R) := by
  obtain ⟨ρ,K,hρ,hK,hcoef,hcoefLip⟩ := normalizedRankCoefficient_uniform_analytic_lipschitz
  have hsmall : ∀ᶠ R : ℝ in 𝓝 0, (L*R)^2<ρ ∧
      (L*R)^2+2*R*(L*R)*L+2*K*R*(L*R)^3*L<1/64 := by
    have h1 : ContinuousAt (fun R : ℝ => (L*R)^2) 0 := by fun_prop
    have h2 : ContinuousAt (fun R : ℝ => (L*R)^2+2*R*(L*R)*L+2*K*R*(L*R)^3*L) 0 := by fun_prop
    exact (h1.eventually_lt_const (by simpa using hρ)).and
      (h2.eventually_lt_const (by norm_num))
  obtain ⟨a,ha,hs⟩ := Metric.mem_nhds_iff.mp hsmall
  let R₀ := a/2
  have hR₀ : 0<R₀ := by dsimp [R₀]; positivity
  refine ⟨R₀,hR₀,?_⟩
  intro R hR hRR n hn e he he0 heL
  have hRa : R<a := by dsimp [R₀] at hRR; linarith
  have hRs := hs (show R∈ball (0:ℝ) a by simpa [Real.norm_eq_abs,abs_of_pos hR] using hRa)
  have heB (w : Config n) (hw : ‖w‖≤R) : ‖e w‖≤L*R := by
    have hh := heL w 0 hw (by simpa using hR.le)
    simp only [he0,sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hw hL.le)
  refine ⟨?_,?_⟩
  · intro w hw
    have hw' : ‖w‖<R := by simpa using hw
    apply normalizedMeanCorrection_analyticAt e w (he w hw)
    apply hcoef
    exact (mean_product_norm_le hn (e w) (e w)).trans_lt
      ((mul_le_mul (heB w hw'.le) (heB w hw'.le) (norm_nonneg _) (by positivity)).trans_lt
        (by simpa only [pow_two] using hRs.1))
  · apply LipschitzOnWith.of_dist_le_mul
    intro w hw z hz
    have hw' : ‖w‖≤R := by simpa using hw
    have hz' : ‖z‖≤R := by simpa using hz
    have hc := normalizedRankCoefficient_field_difference hn (e w) (e z) (L*R) L K ρ ‖w-z‖
      (by positivity) hL.le hK.le (norm_nonneg _) (heB w hw') (heB z hz') (heL w z hw' hz') hRs.1 hcoefLip
    have hh := normalizedMeanCorrection_error_bound hn (e w) (e z) w z (L*R) R L K
      (by positivity) hR.le hL.le hK.le (heB w hw') (heB z hz') hz' (heL w z hw' hz') hc
    simpa only [dist_eq_norm,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using
      hh.trans (mul_le_mul_of_nonneg_right hRs.2.le (norm_nonneg _))

end
end IsingBulk.Anisotropic.NegativeNormalForm
