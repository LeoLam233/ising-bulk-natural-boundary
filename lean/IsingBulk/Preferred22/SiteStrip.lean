import IsingBulk.Preferred22.StripTranslation
import IsingBulk.Preferred22.NormalConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! A fixed physical-temperature strip for the actual site integrand. The
strip width and interior-root bound precede the particle number and sites. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set Filter MeasureTheory
open scoped BigOperators Topology

def complexSiteDensity {N : ℕ} (s : ℂ) (a b : ℤ) (w : Fin N → ℂ) : ℂ :=
  let y := fun i => complexAngleRoot (w i)
  let z := complexAngularRoots (s,w)
  exp (I*(a:ℂ)*(∑ i,w i)) * (∏ i,z i)^b.natAbs *
    ((-I)^N * (∏ i,z i/y i) * (rationalKernel y z).det) * ∏ i,oneBody (z i)

theorem complexSiteDensity_real {N : ℕ} (s : ℂ) (a b : ℤ) (θ : Fin N → ℝ) :
    complexSiteDensity s a b (fun i => (θ i:ℂ)) =
      exp (I*(a:ℂ)*(∑ i,(θ i:ℂ))) * (∏ i,angularRoots s θ i)^b.natAbs *
        (gaugeKernel (fun i => angleRoot (θ i)) (angularRoots s θ)).det *
          ∏ i,oneBody (angularRoots s θ i) := by
  simp only [complexSiteDensity,complexAngularRoots_real,complexAngleRoot,angleRoot,
    gaugeKernel_det_normalization]

theorem complexSiteDensity_analyticAt {N : ℕ} (s : ℂ) (a b : ℤ) (w : Fin N → ℂ)
    (hW : ∀ i,OffRealSegment (temperatureTrace s-cos (w i))) :
    AnalyticAt ℂ (complexSiteDensity s a b) w := by
  let y := fun v : Fin N → ℂ => fun i => complexAngleRoot (v i)
  let z := fun v : Fin N → ℂ => complexAngularRoots (s,v)
  have hi (i : Fin N) : AnalyticAt ℂ (fun v : Fin N → ℂ => v i) w :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt w
  have hy (i : Fin N) : AnalyticAt ℂ (fun v => y v i) w :=
    (analyticAt_const.mul (hi i)).cexp
  have hz (i : Fin N) : AnalyticAt ℂ (fun v => z v i) w := by
    have hwi : AnalyticAt ℂ (fun v : Fin N → ℂ => temperatureTrace s-cos (v i)) w :=
      analyticAt_const.sub (Complex.analyticAt_cos.comp (hi i))
    exact (physicalRoot_analyticAt (hW i)).comp_of_eq hwi rfl
  have hzi (i : Fin N) : ‖z w i‖<1 := physicalRoot_inside (hW i)
  have hden (i j : Fin N) : 1-z w i*z w j≠0 := by
    intro he
    have hh : z w i*z w j=1 := (sub_eq_zero.mp he).symm
    have hnorm : ‖z w i*z w j‖<1 := by
      rw [norm_mul]
      nlinarith [hzi i,hzi j,norm_nonneg (z w i),norm_nonneg (z w j)]
    simp [hh] at hnorm
  have hR (i j : Fin N) : AnalyticAt ℂ
      (fun v => rationalKernel (y v) (z v) i j) w :=
    ((hy i).sub (hy j)).div (analyticAt_const.sub ((hz i).mul (hz j))) (hden i j)
  have hdet : AnalyticAt ℂ (fun v => (rationalKernel (y v) (z v)).det) w := by
    simp only [Matrix.det_apply']
    exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
      analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hR (σ i) i)))
  have hratio := Finset.univ.analyticAt_fun_prod (fun i _ =>
    (hz i).div (hy i) (Complex.exp_ne_zero _))
  have hbody : AnalyticAt ℂ (fun v => ∏ i,oneBody (z v i)) w := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (analyticAt_const.mul (hz i)).div (analyticAt_const.sub ((hz i).pow 2))
    change 1-(z w i)^2≠0
    simpa only [pow_two] using hden i i
  have hexp : AnalyticAt ℂ (fun v : Fin N → ℂ => exp (I*(a:ℂ)*(∑ i,v i))) w :=
    (analyticAt_const.mul (Finset.univ.analyticAt_fun_sum (fun i _ => hi i))).cexp
  exact ((hexp.mul ((Finset.univ.analyticAt_fun_prod (fun i _ => hz i)).pow b.natAbs)).mul
    ((analyticAt_const.mul hratio).mul hdet)).mul hbody

theorem complexSiteDensity_periodic (N : ℕ) (s : ℂ) (a b : ℤ) :
    ComplexCoordinatePeriodic N (complexSiteDensity s a b) := by
  intro w i
  have hy : (fun j => complexAngleRoot (Function.update w i (w i+2*(Real.pi:ℂ)) j))=
      fun j => complexAngleRoot (w j) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp only [Function.update_self,complexAngleRoot,mul_add,exp_add]
      rw [show I*(2*(Real.pi:ℂ))=2*(Real.pi:ℂ)*I by ring,exp_two_pi_mul_I,mul_one]
    · rw [Function.update_of_ne hj]
  have hz : complexAngularRoots (s,Function.update w i (w i+2*(Real.pi:ℂ)))=
      complexAngularRoots (s,w) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp only [complexAngularRoots,Function.update_self,Complex.cos_add_two_pi]
    · simp only [complexAngularRoots,Function.update_of_ne hj]
  have hsum : (∑ j,Function.update w i (w i+2*(Real.pi:ℂ)) j)=∑ j,w j+2*(Real.pi:ℂ) := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) w]
    ring
  have hyp (j : Fin N) := congrFun hy j
  simp only [complexSiteDensity,hyp,hz,hsum,mul_add,exp_add]
  rw [show I*(a:ℂ)*(2*(Real.pi:ℂ))=(a:ℂ)*(2*(Real.pi:ℂ)*I) by ring,
    exp_int_mul_two_pi_mul_I,mul_one]

theorem complex_cos_norm_le_cosh_im (z : ℂ) : ‖cos z‖≤Real.cosh z.im := by
  have hh := norm_add_le (exp (z*I)) (exp (-z*I))
  rw [← Complex.two_cos] at hh
  simp only [norm_mul,Complex.norm_ofNat,norm_exp,mul_re,I_re,I_im,mul_zero,mul_one,
    zero_sub,neg_im,neg_neg] at hh
  rw [Real.cosh_eq] 
  linarith

theorem real_temperature_strip_exists {x : ℝ} (hx : 1<x) :
    ∃ h : ℝ,0<h ∧ Real.cosh h<x+x⁻¹-1 := by
  have hx0 : 0<x := by linarith
  have htrace : 2<x+x⁻¹ := by
    have hh : 0<(x-1)^2 := sq_pos_of_ne_zero (by linarith)
    have hh' := (div_pos hh hx0)
    have he : (x-1)^2/x=x+x⁻¹-2 := by field_simp; ring
    rw [he] at hh'
    linarith
  have he : ∀ᶠ t : ℝ in 𝓝 0,Real.cosh t<x+x⁻¹-1 :=
    Real.continuous_cosh.continuousAt.eventually_lt continuousAt_const (by
      simp only [Real.cosh_zero]
      linarith)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ/2,by linarith,hsub ?_⟩
  simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos (by linarith : 0<δ/2)]
    using (show δ/2<δ by linarith)

theorem real_strip_W_off_segment {x h : ℝ} (hh : 0≤h)
    (hgap : Real.cosh h<x+x⁻¹-1) {w : ℂ} (hw : |w.im|≤h) :
    OffRealSegment (temperatureTrace (x:ℂ)-cos w) := by
  have hb : ‖cos w‖≤Real.cosh h :=
    (complex_cos_norm_le_cosh_im w).trans (Real.cosh_le_cosh.mpr (by simpa [abs_of_nonneg hh] using hw))
  right
  have hre : 1<(temperatureTrace (x:ℂ)-cos w).re := by
    simp only [temperatureTrace,sub_re,add_re,ofReal_re,← ofReal_inv] 
    have hr := Complex.re_le_norm (cos w)
    linarith
  exact hre.trans_le (le_abs_self _)

theorem real_strip_root_bound {x h : ℝ} (hh : 0≤h)
    (hgap : Real.cosh h<x+x⁻¹-1) :
    ∃ q : ℝ,0<q ∧ q<1 ∧ ∀ w : ℂ,|w.im|≤h →
      ‖physicalRoot (temperatureTrace (x:ℂ)-cos w)‖≤q := by
  let c : ℂ := ((x+x⁻¹:ℝ):ℂ)
  let K : Set ℂ := Metric.closedBall c (Real.cosh h)
  have hoff (W : ℂ) (hW : W∈K) : OffRealSegment W := by
    have hn : ‖c-W‖≤Real.cosh h := by
      simpa only [K,Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hW
    have hr := Complex.re_le_norm (c-W)
    simp only [sub_re,c,ofReal_re] at hr
    right
    have : 1<W.re := by linarith
    exact this.trans_le (le_abs_self _)
  have hc : ContinuousOn physicalRoot K := fun W hW =>
    (physicalRoot_analyticAt (hoff W hW)).continuousAt.continuousWithinAt
  have hK : IsCompact K := isCompact_closedBall _ _
  have hne : K.Nonempty := ⟨c,Metric.mem_closedBall_self (Real.cosh_pos h).le⟩
  obtain ⟨W,hW,hmax⟩ := hK.exists_isMaxOn hne hc.norm
  have hnorm := physicalRoot_inside (hoff W hW)
  refine ⟨(‖physicalRoot W‖+1)/2,by linarith [norm_nonneg (physicalRoot W)],by linarith,?_⟩
  intro w hw
  have hb : ‖cos w‖≤Real.cosh h :=
    (complex_cos_norm_le_cosh_im w).trans (Real.cosh_le_cosh.mpr (by simpa [abs_of_nonneg hh] using hw))
  have hmem : temperatureTrace (x:ℂ)-cos w∈K := by
    change dist (temperatureTrace (x:ℂ)-cos w) c≤Real.cosh h
    have he : temperatureTrace (x:ℂ)=c := by simp [temperatureTrace,c]
    rw [he,dist_eq_norm,sub_sub_cancel_left,norm_neg]
    exact hb
  exact (hmax hmem).trans (by linarith)

end
end IsingBulk.Preferred22
