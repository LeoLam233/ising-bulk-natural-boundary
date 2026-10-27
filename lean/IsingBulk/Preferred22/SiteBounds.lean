import IsingBulk.Preferred22.SiteStrip

/-! Dimension-independent bounds for the actual translated site density. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set MeasureTheory
open scoped BigOperators

theorem gaugeKernel_common_radius_bound {N : ℕ} {q r : ℝ}
    (hq0 : 0≤q) (hq1 : q<1) (hr : 0<r) (y z : Fin N → ℂ)
    (hy : ∀ i,‖y i‖=r) (hz : ∀ i,‖z i‖≤q) (i j : Fin N) :
    ‖gaugeKernel y z i j‖≤kernelEnvelope q := by
  have hD : 0<1-q^2 := by nlinarith
  have hd := pair_denominator_lower hq0 (hz i) (hz j)
  have hg (k : Fin N) : ‖Complex.sqrt (z k/y k)‖≤Real.sqrt (1/r) := by
    have he : ‖Complex.sqrt (z k/y k)‖^2=‖z k‖/r := by
      rw [← norm_pow,complex_sqrt_sq,norm_div,hy k]
    have hb : ‖z k‖/r≤1/r := div_le_div_of_nonneg_right (le_trans (hz k) hq1.le) hr.le
    rw [← Real.sq_sqrt (by positivity : 0≤1/r),← he] at hb
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hb
  have hyy : ‖y i-y j‖≤2*r := by simpa only [hy i,hy j,two_mul] using norm_sub_le (y i) (y j)
  have hn : ‖Complex.sqrt (z i/y i)‖*‖Complex.sqrt (z j/y j)‖*‖y i-y j‖≤2 := by
    calc
      _ ≤ (Real.sqrt (1/r)*Real.sqrt (1/r))*(2*r) :=
        mul_le_mul (mul_le_mul (hg i) (hg j) (norm_nonneg _) (Real.sqrt_nonneg _))
          hyy (norm_nonneg _) (by positivity)
      _ = 2 := by rw [← pow_two,Real.sq_sqrt (by positivity : 0≤1/r)]; field_simp
  unfold gaugeKernel kernelEnvelope
  rw [norm_div]
  simp only [norm_mul,norm_neg,Complex.norm_I,one_mul]
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by norm_num) hD hd)

theorem complexCoordinatePeriodic_translate {N : ℕ} {F : (Fin N → ℂ) → ℂ}
    (hp : ComplexCoordinatePeriodic N F) (c : Fin N → ℂ) :
    IsingBulk.First.CoordinatePeriodic N (fun θ : Fin N → ℝ => F (fun i => (θ i:ℂ)+c i)) := by
  intro θ i
  have he : (fun j => (Function.update θ i (θ i+2*Real.pi) j:ℂ)+c j)=
      Function.update (fun j => (θ j:ℂ)+c j) i ((θ i:ℂ)+c i+2*(Real.pi:ℂ)) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp only [Function.update_self,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
      ring
    · rw [Function.update_of_ne hj,Function.update_of_ne hj]
  dsimp only
  rw [he]
  exact hp _ _

theorem actual_site_contour_shift (N : ℕ) {x h : ℝ} (hh : 0≤h)
    (hgap : Real.cosh h<x+x⁻¹-1) (a b : ℤ) (t : ℝ) (ht : |t|≤h) :
    siteCoefficient N a b (x:ℂ)=((N.factorial:ℂ)*(2*Real.pi:ℂ)^N)⁻¹ *
      ∫ θ in angularBox N,complexSiteDensity (x:ℂ) a b (fun i => (θ i:ℂ)+(t:ℂ)*I) := by
  let F : (Fin N → ℂ) → ℂ := complexSiteDensity (x:ℂ) a b
  have hF : ∀ w : Fin N → ℂ,(∀ i,|(w i).im|≤h) → AnalyticAt ℂ F w :=
    fun w hw => complexSiteDensity_analyticAt _ _ _ _ (fun i => real_strip_W_off_segment hh hgap (hw i))
  have hc (u : ℝ) (hu : |u|≤h) :
      Continuous (fun θ : Fin N → ℝ => F (fun i => (θ i:ℂ)+(u:ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact ((hF _ (by intro i; simpa using hu)).continuousAt.comp
      (continuous_pi (fun i => (Complex.continuous_ofReal.comp
        (continuous_apply i : Continuous (fun θ : Fin N → ℝ => θ i))).add
          continuous_const)).continuousAt)
  have hc₀ : Continuous (fun θ : Fin N → ℝ => F (fun i => (θ i:ℂ))) := by
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using hc 0 (by simpa using hh)
  have hp := complexSiteDensity_periodic N (x:ℂ) a b
  have hp₀ : IsingBulk.First.CoordinatePeriodic N (fun θ : Fin N → ℝ => F (fun i => (θ i:ℂ))) := by
    simpa only [add_zero] using complexCoordinatePeriodic_translate hp (fun _ => 0)
  have hp₁ := complexCoordinatePeriodic_translate hp (fun _ => (t:ℂ)*I)
  unfold siteCoefficient
  simp_rw [← complexSiteDensity_real]
  congr 1
  rw [angularBox_integral_eq_multiAngleIntegral _ hc₀ hp₀,
    angularBox_integral_eq_multiAngleIntegral _ (hc t ht) hp₁]
  exact multiAngleIntegral_complex_translation N h hh F hF hp (fun _ => t) (fun _ => ht)

theorem shifted_exponential_norm (N : ℕ) (a : ℤ) (t : ℝ) (θ : Fin N → ℝ) :
    ‖exp (I*(a:ℂ)*(∑ i,((θ i:ℂ)+(t:ℂ)*I)))‖=Real.exp (-(a:ℝ)*(N:ℝ)*t) := by
  rw [norm_exp]
  congr 1
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul]
  simp
  ring

theorem complexSiteDensity_shifted_bound {N : ℕ} (hN : 0<N) {x h q : ℝ}
    (hq0 : 0≤q) (hq1 : q<1)
    (hz : ∀ w : ℂ,|w.im|≤h → ‖physicalRoot (temperatureTrace (x:ℂ)-cos w)‖≤q)
    (a b : ℤ) (t : ℝ) (ht : |t|≤h) (θ : Fin N → ℝ) :
    ‖complexSiteDensity (x:ℂ) a b (fun i => (θ i:ℂ)+(t:ℂ)*I)‖≤
      (Real.sqrt N*(kernelEnvelope q)^2)^N *
        Real.exp (-(a:ℝ)*(N:ℝ)*t) * q^b.natAbs := by
  let w : Fin N → ℂ := fun i => (θ i:ℂ)+(t:ℂ)*I
  let y : Fin N → ℂ := fun i => complexAngleRoot (w i)
  let z : Fin N → ℂ := complexAngularRoots ((x:ℂ),w)
  have hzi : ∀ i,‖z i‖≤q := by
    intro i
    exact hz (w i) (by simpa [w] using ht)
  have hy : ∀ i,‖y i‖=Real.exp (-t) := by intro i; simp [y,w,complexAngleRoot,norm_exp]
  have hC : 0≤kernelEnvelope q := by
    unfold kernelEnvelope
    have : 0<1-q^2 := by nlinarith
    positivity
  have hd := determinant_bound hN (gaugeKernel y z) hC
    (gaugeKernel_common_radius_bound hq0 hq1 (Real.exp_pos (-t)) y z hy hzi)
  have hb : ‖∏ i,oneBody (z i)‖≤(kernelEnvelope q)^N := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N,kernelEnvelope q := Finset.prod_le_prod₀
        (fun i _ => norm_nonneg _) (fun i _ => oneBody_norm_bound hq0 hq1 (hzi i))
      _ = _ := by simp
  have hZ : ‖(∏ i,z i)^b.natAbs‖≤q^b.natAbs := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (product_norm_le_q hN hq0 hq1 z hzi) _
  have he : ‖exp (I*(a:ℂ)*(∑ i,w i))‖=Real.exp (-(a:ℝ)*(N:ℝ)*t) :=
    shifted_exponential_norm N a t θ
  have hpow : (Real.sqrt N*kernelEnvelope q)^N*(kernelEnvelope q)^N=
      (Real.sqrt N*(kernelEnvelope q)^2)^N := by
    rw [← mul_pow]
    congr 1
    ring
  change ‖exp (I*(a:ℂ)*(∑ i,w i))*(∏ i,z i)^b.natAbs*
    ((-I)^N*(∏ i,z i/y i)*(rationalKernel y z).det)*∏ i,oneBody (z i)‖≤_
  rw [← gaugeKernel_det_normalization]
  simp only [norm_mul,he]
  calc
    _ ≤ ((Real.exp (-(a:ℝ)*(N:ℝ)*t)*q^b.natAbs)*(Real.sqrt N*kernelEnvelope q)^N)*
        (kernelEnvelope q)^N :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le)
        hd (norm_nonneg _) (by positivity)) hb (norm_nonneg _) (by positivity)
    _ = (Real.exp (-(a:ℝ)*(N:ℝ)*t)*q^b.natAbs)*
        ((Real.sqrt N*kernelEnvelope q)^N*(kernelEnvelope q)^N) := by ring
    _ = _ := by rw [hpow]; ring

end
end IsingBulk.Preferred22
