import IsingBulk.First.MeanPrescribedLemma
import IsingBulk.First.MeanErrorShapeRegularity
import IsingBulk.First.MeanErrorShapeLimit

/-! The actual smooth mean decomposition is integrated on the fixed shape
cutoff before complex-s differentiation. Absolute integrability and local
holomorphy of both summands are proved source inputs. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex MeasureTheory Set Filter Metric
open scoped Topology

def intrinsicSmoothMeanIntegral {n : ℕ} (a : OrderedChartData) (chi : ShapeSpace n → ℂ)
    (eta : ℝ → ℂ) (rho delta : ℝ) (s : ℂ) : ℂ :=
  ∫ x : ShapeSpace n, chi x*(smoothMeanIntegral eta s rho a.alpha delta (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ))

def localizedSmoothMeanIntegral {n : ℕ} (a : OrderedChartData) (chi : ShapeSpace n → ℂ)
    (eta : ℝ → ℂ) (rho delta : ℝ) (s : ℂ) : ℂ :=
  ∫ t : Fin n → ℝ, chi (shapeCoordinateEquiv n (WithLp.toLp 2 t))*
    (smoothMeanIntegral eta s rho a.alpha delta t/((n+1).factorial:ℂ))

theorem localizedSmoothMeanIntegral_eq_intrinsic {n : ℕ} (a : OrderedChartData)
    (chi : ShapeSpace n → ℂ) (eta : ℝ → ℂ) (rho delta : ℝ) (s : ℂ) :
    localizedSmoothMeanIntegral a chi eta rho delta s =
      (Real.sqrt (n+1))⁻¹ • intrinsicSmoothMeanIntegral a chi eta rho delta s := by
  simpa only [localizedSmoothMeanIntegral,intrinsicSmoothMeanIntegral,
    intrinsicShapeCoordinates_shapeCoordinateEquiv] using integral_shapeExtend n (fun x =>
      chi x*(smoothMeanIntegral eta s rho a.alpha delta (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ)))

theorem localizedSmoothMeanIntegral_iteratedDeriv {n : ℕ} (a : OrderedChartData)
    (chi : ShapeSpace n → ℂ) (eta : ℝ → ℂ) (rho delta : ℝ) (j : ℕ) (s : ℂ) :
    (deriv^[j] (localizedSmoothMeanIntegral a chi eta rho delta)) s =
      (Real.sqrt (n+1))⁻¹ • (deriv^[j] (intrinsicSmoothMeanIntegral a chi eta rho delta)) s := by
  have he : localizedSmoothMeanIntegral a chi eta rho delta =
      fun z => (((Real.sqrt (n+1))⁻¹:ℝ):ℂ)*intrinsicSmoothMeanIntegral a chi eta rho delta z := by
    funext z
    rw [localizedSmoothMeanIntegral_eq_intrinsic,Complex.real_smul]
  rw [he,iterate_deriv_const_mul]
  rfl

theorem localizedPostMeanIntegral_iteratedDeriv {n : ℕ} (a : OrderedChartData)
    (chi : ShapeSpace n → ℂ) (j : ℕ) (s : ℂ) :
    (deriv^[j] (localizedPostMeanIntegral a chi)) s =
      (Real.sqrt (n+1))⁻¹ • (deriv^[j] (intrinsicPostMeanIntegral a chi)) s := by
  have he : localizedPostMeanIntegral a chi =
      fun z => (((Real.sqrt (n+1))⁻¹:ℝ):ℂ)*intrinsicPostMeanIntegral a chi z := by
    funext z
    rw [localizedPostMeanIntegral_eq_intrinsic,Complex.real_smul]
  rw [he,iterate_deriv_const_mul]
  rfl

theorem actual_integrated_mean_derivative_decomposition {n : ℕ} (a : OrderedChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ R epsilon₀ : ℝ, 0 < R ∧ 0 < epsilon₀ ∧
      ∀ eta : ℝ → ℂ, Continuous eta → (∀ v : ℝ, |v| ≤ delta → eta v=1) →
        ∀ chi : ShapeSpace n → ℂ, Continuous chi → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
          ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon₀ → ∀ j : ℕ,
          (deriv^[j] (localizedSmoothMeanIntegral a chi eta (-(Real.sin a.theta/4)*epsilon) delta))
            (radialParameter a.theta epsilon) =
          (deriv^[j] (localizedPostMeanIntegral a chi)) (radialParameter a.theta epsilon)+
          (deriv^[j] (localizedMeanErrorIntegral a chi eta (-(Real.sin a.theta/4)*epsilon) delta))
            (radialParameter a.theta epsilon) := by
  obtain ⟨Dp,hDp,hP⟩ := actual_physical_mean_prescribed_delta a n ha hb
  obtain ⟨De,hDe,hE⟩ := actual_mean_error_shape_regularity (n := n) a ha hb
  obtain ⟨Rp,hRp,hPost⟩ := actual_postMean_local_regularity (n := n) a ha hb
  refine ⟨min Dp De,lt_min hDp hDe,?_⟩
  intro delta hd hdD
  obtain ⟨Rg,eg,hRg,heg,hPhysical⟩ := hP delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨Re,hRe,hError⟩ := hE delta hd (hdD.trans (min_le_right _ _))
  let R := min Rp (min Re (Rg/4))
  have hR : 0 < R := lt_min hRp (lt_min hRe (by positivity))
  have hRRp : R ≤ Rp := min_le_left _ _
  have hRRe : R ≤ Re := (min_le_right _ _).trans (min_le_left _ _)
  have hRRg : R ≤ Rg/4 := (min_le_right _ _).trans (min_le_right _ _)
  let c₀ := Real.sin a.theta/4
  have hc₀ : 0 < c₀ := div_pos a.sin_theta_pos (by norm_num)
  let epsilon₀ := min eg (min Rp (Re/(c₀+1)))
  have he0 : 0 < epsilon₀ := lt_min heg (lt_min hRp (div_pos hRe (by positivity)))
  refine ⟨R,epsilon₀,hR,he0,?_⟩
  intro eta heta heta1 chi hchi hchis epsilon he he0' j
  have heg' : epsilon < eg := he0'.trans_le (min_le_left _ _)
  have heRp : epsilon < Rp := he0'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hem : epsilon*(c₀+1) < Re := (lt_div_iff₀ (show 0 < c₀+1 by positivity)).mp
    (he0'.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have heRe : epsilon < Re := by nlinarith
  have hrho : |(-c₀*epsilon)| ≤ Re := by
    rw [abs_of_neg (by nlinarith)]
    nlinarith
  let s₀ := radialParameter a.theta epsilon
  have hs₀ : ‖s₀-exp ((a.theta:ℂ)*I)‖ < Re := by
    rw [radialParameter_sub_center_norm,abs_of_pos he]
    exact heRe
  obtain ⟨hPa,ep,hep,hPi⟩ := hPost epsilon he heRp chi hchi
    (fun x hx => (hchis x hx).trans_le hRRp)
  have hEa := (hError eta heta chi hchi (fun x hx => (hchis x hx).trans_le hRRe)
    (-c₀*epsilon) hrho s₀ hs₀).1
  have hPhysical' := (hPhysical eta heta heta1).1
  have hEq : intrinsicSmoothMeanIntegral a chi eta (-c₀*epsilon) delta =ᶠ[𝓝 s₀]
      (fun s => intrinsicPostMeanIntegral a chi s+intrinsicMeanErrorIntegral a chi eta (-c₀*epsilon) delta s) := by
    have hsp : 0 < (Real.sin a.theta/16)*epsilon := mul_pos (div_pos a.sin_theta_pos (by norm_num)) he
    have hscenter : ∀ᶠ s : ℂ in 𝓝 s₀, ‖s-exp ((a.theta:ℂ)*I)‖ < Re :=
      (continuous_id.sub continuous_const).norm.continuousAt.eventually (eventually_lt_nhds hs₀)
    filter_upwards [ball_mem_nhds s₀ hsp,ball_mem_nhds s₀ hep,hscenter] with s hs hp hsRe
    have hPint := hPi s (by simpa only [mem_ball,dist_eq_norm] using hp)
    have hEint := (hError eta heta chi hchi (fun x hx => (hchis x hx).trans_le hRRe)
      (-c₀*epsilon) hrho s hsRe).2
    unfold intrinsicSmoothMeanIntegral intrinsicPostMeanIntegral intrinsicMeanErrorIntegral
    rw [← integral_add hPint hEint]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : chi x=0
      · simp only [hx,zero_mul,zero_add]
      · have ht (i : Fin (n+1)) : |shapeExtend (intrinsicShapeCoordinates x) i| < Rg/4 := by
          rw [shapeExtend_intrinsicShapeCoordinates]
          have hc := PiLp.norm_apply_le x.1 i
          rw [Real.norm_eq_abs] at hc
          exact hc.trans_lt ((hchis x hx).trans_le hRRg)
        rw [hPhysical' epsilon (intrinsicShapeCoordinates x) s he heg' ht
          (by simpa only [mem_ball,dist_eq_norm,s₀] using hs)]
        ring
  have hj := hEq.iteratedDeriv_eq j
  rw [iteratedDeriv_fun_add hPa.contDiffAt hEa.contDiffAt] at hj
  simp only [iteratedDeriv_eq_iterate] at hj
  rw [localizedSmoothMeanIntegral_iteratedDeriv,localizedPostMeanIntegral_iteratedDeriv,
    localizedMeanErrorIntegral_iteratedDeriv,hj,smul_add]

end
end IsingBulk.First
