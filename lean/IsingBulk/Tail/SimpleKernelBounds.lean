import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

/-! Actual one-phase kernel bounds. These are proved before coarea and
contain the logarithmic, rather than a power-law, attenuation cost. -/
namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory

def phaseDenominator (r t : ℝ) : ℝ :=
  ‖1-(r:ℂ)*Complex.exp (Complex.I*(t:ℂ))‖

theorem radial_deficit_le_phaseDenominator {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    1-r ≤ phaseDenominator r t := by
  have h := norm_sub_norm_le (1:ℂ) ((r:ℂ)*Complex.exp (Complex.I*(t:ℂ)))
  simpa [phaseDenominator,norm_mul,abs_of_nonneg hr] using h

theorem phase_chord_le_twice_denominator {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (t : ℝ) :
    ‖Complex.exp (Complex.I*(t:ℂ))-1‖ ≤ 2*phaseDenominator r t := by
  let E := Complex.exp (Complex.I*(t:ℂ))
  have he : ‖E‖=1 := by simp [E]
  have hn : ‖E-(r:ℂ)*E‖=1-r := by
    rw [show E-(r:ℂ)*E=(1-(r:ℂ))*E by ring,norm_mul,he,mul_one]
    norm_cast
    exact abs_of_nonneg (by linarith)
  have htri : ‖E-1‖ ≤ ‖E-(r:ℂ)*E‖+‖(r:ℂ)*E-1‖ := by
    convert norm_add_le (E-(r:ℂ)*E) ((r:ℂ)*E-1) using 1; congr 1; ring
  have hgap := radial_deficit_le_phaseDenominator hr t
  rw [hn,norm_sub_rev ((r:ℂ)*E) 1] at htri
  change ‖E-1‖ ≤ 2*phaseDenominator r t
  change ‖E-1‖ ≤ 1-r+phaseDenominator r t at htri
  linarith

theorem phase_distance_le_denominator {r t : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ht : |t| ≤ Real.pi) : |t| ≤ Real.pi*phaseDenominator r t := by
  have hsin := Real.mul_abs_le_abs_sin (x := t/2)
    (by rw [abs_div]; norm_num; linarith)
  have hsin' : |t|/Real.pi ≤ |Real.sin (t/2)| := by
    convert hsin using 1; rw [abs_div]; norm_num
  have hx := (div_le_iff₀ Real.pi_pos).mp hsin'
  have hchord := phase_chord_le_twice_denominator hr hr1 t
  rw [Complex.norm_exp_I_mul_ofReal_sub_one] at hchord
  norm_num only [Real.norm_eq_abs,abs_mul] at hchord
  nlinarith [Real.pi_pos]

theorem attenuation_le_denominator {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a ≤ Real.exp 1*phaseDenominator (Real.exp (-a)) t := by
  have he := Real.add_one_le_exp a
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-a)).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hm
  have hr : Real.exp (-1) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hr ha
  have hgap := radial_deficit_le_phaseDenominator (Real.exp_pos (-a)).le t
  have hb : a*Real.exp (-1) ≤ phaseDenominator (Real.exp (-a)) t := by nlinarith
  rw [Real.exp_neg,← div_eq_mul_inv] at hb
  have hh := (div_le_iff₀ (Real.exp_pos 1)).mp hb
  linarith

theorem simple_kernel_pointwise {a t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : |t| ≤ Real.pi) :
    (phaseDenominator (Real.exp (-a)) t)⁻¹ ≤ (Real.exp 1+Real.pi)/(a+|t|) := by
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgap := radial_deficit_le_phaseDenominator (Real.exp_pos (-a)).le t
  have hd : 0 < phaseDenominator (Real.exp (-a)) t := by linarith
  have ht' := phase_distance_le_denominator (Real.exp_pos (-a)).le hr1.le ht
  have ha' := attenuation_le_denominator ha.le ha1 (t := t)
  rw [← one_div]
  apply (div_le_div_iff₀ hd (by positivity : 0 < a+|t|)).mpr
  nlinarith

theorem shifted_reciprocal_integral {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    (∫ t : ℝ in 0..R, (a+t)⁻¹) = Real.log (a+R)-Real.log a := by
  have hz (t : ℝ) (ht : t ∈ uIcc 0 R) : a+t ≠ 0 := by
    rw [uIcc_of_le hR] at ht
    linarith [ht.1]
  have hi : IntervalIntegrable (fun t : ℝ => (a+t)⁻¹) volume 0 R :=
    (continuousOn_const.add continuousOn_id).inv₀ hz |>.intervalIntegrable
  have hd (t : ℝ) (ht : t ∈ uIcc 0 R) :
      HasDerivAt (fun x : ℝ => Real.log (a+x)) ((a+t)⁻¹) t := by
    convert! (Real.hasDerivAt_log (hz t ht)).comp t ((hasDerivAt_id t).const_add a) using 1; simp
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

theorem simple_kernel_half_period_integral {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ t : ℝ in 0..Real.pi, (phaseDenominator (Real.exp (-a)) t)⁻¹) ≤
      (Real.exp 1+Real.pi)*(Real.log (a+Real.pi)-Real.log a) := by
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden (t : ℝ) : phaseDenominator (Real.exp (-a)) t ≠ 0 := by
    have hgap := radial_deficit_le_phaseDenominator (Real.exp_pos (-a)).le t
    linarith
  have hcont : Continuous (fun t : ℝ => (phaseDenominator (Real.exp (-a)) t)⁻¹) := by
    apply Continuous.inv₀ _ hden
    unfold phaseDenominator
    fun_prop
  have hz (t : ℝ) (ht : t ∈ uIcc 0 Real.pi) : a+t ≠ 0 := by
    rw [uIcc_of_le Real.pi_pos.le] at ht
    linarith [ht.1]
  have hbound : IntervalIntegrable (fun t : ℝ => (Real.exp 1+Real.pi)*(a+t)⁻¹)
      volume 0 Real.pi :=
    continuousOn_const.mul ((continuousOn_const.add continuousOn_id).inv₀ hz) |>.intervalIntegrable
  calc
    _ ≤ ∫ t : ℝ in 0..Real.pi, (Real.exp 1+Real.pi)*(a+t)⁻¹ := by
      apply intervalIntegral.integral_mono_on Real.pi_pos.le (hcont.intervalIntegrable 0 Real.pi) hbound
      intro t ht
      have h := simple_kernel_pointwise ha ha1 (show |t| ≤ Real.pi by simpa [abs_of_nonneg ht.1] using ht.2)
      simpa [abs_of_nonneg ht.1,div_eq_mul_inv] using h
    _ = _ := by rw [intervalIntegral.integral_const_mul,shifted_reciprocal_integral ha Real.pi_pos.le]

theorem phaseDenominator_neg (r t : ℝ) : phaseDenominator r (-t)=phaseDenominator r t := by
  have he : (starRingEnd ℂ) (1-(r:ℂ)*Complex.exp (Complex.I*(t:ℂ))) =
      1-(r:ℂ)*Complex.exp (Complex.I*((-t:ℝ):ℂ)) := by
    rw [map_sub,map_one,map_mul,Complex.conj_ofReal,← Complex.exp_conj]
    simp
  unfold phaseDenominator
  rw [← he]
  exact norm_star _

theorem phaseDenominator_periodic (r : ℝ) :
    Function.Periodic (phaseDenominator r) (2*Real.pi) := by
  intro t
  unfold phaseDenominator
  rw [show Complex.I*((t+2*Real.pi:ℝ):ℂ)=Complex.I*(t:ℂ)+2*(Real.pi:ℂ)*Complex.I by
    push_cast; ring,Complex.exp_periodic]

theorem simple_kernel_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (fun t : ℝ => (phaseDenominator (Real.exp (-a)) t)⁻¹) := by
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  apply Continuous.inv₀
  · unfold phaseDenominator
    fun_prop
  · intro t
    have h := radial_deficit_le_phaseDenominator (Real.exp_pos (-a)).le t
    linarith

theorem simple_kernel_centered_period_integral {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ t : ℝ in -Real.pi..Real.pi, (phaseDenominator (Real.exp (-a)) t)⁻¹) ≤
      2*(Real.exp 1+Real.pi)*(Real.log (a+Real.pi)-Real.log a) := by
  let f := fun t : ℝ => (phaseDenominator (Real.exp (-a)) t)⁻¹
  have hc : Continuous f := simple_kernel_continuous ha
  have he : (∫ t : ℝ in -Real.pi..0, f t) = ∫ t : ℝ in 0..Real.pi, f t := by
    have h := intervalIntegral.integral_comp_neg f (a := (0:ℝ)) (b := Real.pi)
    simpa only [neg_zero,f,phaseDenominator_neg] using h.symm
  change (∫ t : ℝ in -Real.pi..Real.pi, f t) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-Real.pi) 0) (hc.intervalIntegrable 0 Real.pi),he]
  have h := simple_kernel_half_period_integral ha ha1
  change (∫ t in 0..Real.pi, f t) ≤ _ at h
  linarith

def simpleKernelConstant : ℝ :=
  2*(Real.exp 1+Real.pi)*(|Real.log (1+Real.pi)|+1)

theorem simpleKernelConstant_pos : 0 < simpleKernelConstant := by
  unfold simpleKernelConstant
  positivity

/-- Actual full-period L1 bound, uniform in the position of the interval.
This is the logarithmic kernel estimate used by the sector/coarea arguments
and by the weighted Pfaffian convolution. -/
theorem simple_kernel_period_integral {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (t₀ : ℝ) :
    (∫ t : ℝ in t₀..t₀+2*Real.pi, (phaseDenominator (Real.exp (-a)) t)⁻¹) ≤
      simpleKernelConstant*(1+|Real.log a|) := by
  have hp : Function.Periodic (fun t : ℝ => (phaseDenominator (Real.exp (-a)) t)⁻¹)
      (2*Real.pi) := by
    intro t
    exact congrArg (fun x : ℝ => x⁻¹) (phaseDenominator_periodic (Real.exp (-a)) t)
  rw [hp.intervalIntegral_add_eq t₀ (-Real.pi),show -Real.pi+2*Real.pi=Real.pi by ring]
  apply (simple_kernel_centered_period_integral ha ha1).trans
  have hlog : Real.log (a+Real.pi) ≤ Real.log (1+Real.pi) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog' : Real.log (a+Real.pi)-Real.log a ≤ |Real.log (1+Real.pi)|+|Real.log a| := by
    linarith [le_abs_self (Real.log (1+Real.pi)),neg_le_abs (Real.log a)]
  have hmajor : |Real.log (1+Real.pi)|+|Real.log a| ≤
      (|Real.log (1+Real.pi)|+1)*(1+|Real.log a|) := by
    nlinarith [mul_nonneg (abs_nonneg (Real.log (1+Real.pi))) (abs_nonneg (Real.log a))]
  have hm := mul_le_mul_of_nonneg_left (hlog'.trans hmajor)
    (show 0 ≤ 2*(Real.exp 1+Real.pi) by positivity)
  simpa [simpleKernelConstant,mul_assoc] using hm

/-- Literal original y-Schur denominator majorant for radius exp(-c0 eps).
The numerator bound two is included; the normalized angular measure can be
applied afterward by the convolution/Fredholm caller. -/
theorem original_y_kernel_period_integral {c₀ eps : ℝ} (hc : 0 < c₀) (heps : 0 < eps)
    (hsmall : 2*c₀*eps ≤ 1) (t₀ : ℝ) :
    (∫ t : ℝ in t₀..t₀+2*Real.pi,
      2/phaseDenominator ((Real.exp (-c₀*eps))^2) t) ≤
      2*simpleKernelConstant*(1+|Real.log (2*c₀*eps)|) := by
  have he : (Real.exp (-c₀*eps))^2 = Real.exp (-(2*c₀*eps)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (simple_kernel_period_integral (by positivity : 0 < 2*c₀*eps) hsmall t₀)
      (by norm_num : (0:ℝ)≤2)
  simpa [mul_assoc] using h

/-- A variable attenuation bounded below may be replaced by the fixed floor
with an absolute factor two. No monotonicity of the complex chord in r is
incorrectly assumed. -/
theorem simple_kernel_radius_floor {r r₀ t : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r₀)
    (hr₀ : r₀ < 1) :
    (phaseDenominator r t)⁻¹ ≤ 2*(phaseDenominator r₀ t)⁻¹ := by
  let E := Complex.exp (Complex.I*(t:ℂ))
  have he : ‖E‖=1 := by simp [E]
  have hdiff : ‖((r-r₀:ℝ):ℂ)*E‖=r₀-r := by
    rw [norm_mul,he,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    ring
  have htri : phaseDenominator r₀ t ≤ phaseDenominator r t + (r₀-r) := by
    have h := norm_add_le (1-(r:ℂ)*E) (((r-r₀:ℝ):ℂ)*E)
    rw [show (1-(r:ℂ)*E)+((r-r₀:ℝ):ℂ)*E=1-(r₀:ℂ)*E by push_cast; ring,hdiff] at h
    exact h
  have hgap := radial_deficit_le_phaseDenominator hr t
  have hgap₀ := radial_deficit_le_phaseDenominator (hr.trans hrr) t
  have hd : 0 < phaseDenominator r t := by linarith
  have hd₀ : 0 < phaseDenominator r₀ t := by linarith
  rw [← one_div,← div_eq_mul_inv]
  apply (div_le_div_iff₀ hd hd₀).mpr
  nlinarith

/-- Explicit period counts for unwrapped coarea intervals. They are not
mistaken for the multiplicity of the two-dimensional phase map. -/
theorem simple_kernel_interval_integral {a x y : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (n : ℕ) (hxy : x ≤ y) (hlen : y ≤ x+(n:ℝ)*(2*Real.pi)) :
    (∫ t : ℝ in x..y, (phaseDenominator (Real.exp (-a)) t)⁻¹) ≤
      (n:ℝ)*simpleKernelConstant*(1+|Real.log a|) := by
  let f := fun t : ℝ => (phaseDenominator (Real.exp (-a)) t)⁻¹
  have hp : Function.Periodic f (2*Real.pi) := by
    intro t
    exact congrArg (fun v : ℝ => v⁻¹) (phaseDenominator_periodic (Real.exp (-a)) t)
  have hc : Continuous f := simple_kernel_continuous ha
  have hz : (∫ t : ℝ in x..x+(n:ℝ)*(2*Real.pi), f t) =
      (n:ℝ)*(∫ t : ℝ in x..x+2*Real.pi, f t) := by
    simpa only [zsmul_eq_mul,Int.cast_natCast] using
      hp.intervalIntegral_add_zsmul_eq (n:ℤ) x (fun b c => hc.intervalIntegrable b c)
  change (∫ t : ℝ in x..y, f t) ≤ _
  calc
    _ ≤ ∫ t : ℝ in x..x+(n:ℝ)*(2*Real.pi), f t :=
      intervalIntegral.integral_mono_interval le_rfl hxy hlen
        (Filter.Eventually.of_forall (fun t => inv_nonneg.mpr (norm_nonneg _)))
        (hc.intervalIntegrable _ _)
    _ = _ := hz
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (simple_kernel_period_integral ha ha1 x)
        (show (0:ℝ) ≤ n by positivity)
      simpa only [mul_assoc] using h

end
end IsingBulk.Tail
