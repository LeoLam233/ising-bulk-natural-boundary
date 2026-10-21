import IsingBulk.HT.First.OddRadialPrimitive
import IsingBulk.HT.First.OddShapeIntegrability
import IsingBulk.First.FirstCoefficient
import IsingBulk.First.SwappedChartCoefficient
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Exact odd constrained-period evaluation using the rational primitive, reusing
LT's actual shape space, coordinate measure, sphere integral, and weighted
polar formula. This is the period calculation, not the localized-contour limit.
-/
namespace IsingBulk.HT.First
noncomputable section
open MeasureTheory Set Filter IsingBulk.First
open scoped Topology

private theorem odd_quadratic_primitive_hasDerivAt (m : ℕ) {Q d : ℝ}
    (hQ : 0 < Q) (hd : d ≠ 0) (r : ℝ) :
    HasDerivAt (fun x : ℝ =>
      ((-Complex.I*d)*(x:ℂ)^2/((Q:ℂ)+(-Complex.I*d)*(x:ℂ)^2))^(m+1))
      (2*((m+1:ℕ):ℂ)*(Q:ℂ)*(-Complex.I*d)^(m+1)*
        ((r:ℂ)^(2*m+1)/shapeQuadratic Q (-Complex.I*d) r^(m+2))) r := by
  have hden : (Q:ℂ)+(-Complex.I*d)*(r:ℂ)^2 ≠ 0 :=
    odd_shapeQuadratic_ne_zero hQ hd r
  have h := (odd_radial_primitive_hasDerivAt m (Q:ℂ) (-Complex.I*d) ((r:ℂ)^2) hden).comp
    (r:ℂ) ((hasDerivAt_id (r:ℂ)).pow 2)
  convert h.comp_ofReal using 1
  · rfl
  · change 2*((m+1:ℕ):ℂ)*(Q:ℂ)*(-Complex.I*d)^(m+1)*
        ((r:ℂ)^(2*m+1)/((Q:ℂ)+(-Complex.I*d)*(r:ℂ)^2)^(m+2)) =
      ((m+1:ℕ):ℂ)*(Q:ℂ)*(-Complex.I*d)^(m+1)*((r:ℂ)^2)^m/
        ((Q:ℂ)+(-Complex.I*d)*(r:ℂ)^2)^(m+2)*((2:ℂ)*(r:ℂ)^1*1)
    simp only [pow_add,pow_mul,pow_one]
    ring

private theorem odd_quadratic_primitive_tendsto (m : ℕ) {Q d : ℝ}
    (hQ : 0 < Q) (hd : d ≠ 0) :
    Tendsto (fun r : ℝ =>
      ((-Complex.I*d)*(r:ℂ)^2/((Q:ℂ)+(-Complex.I*d)*(r:ℂ)^2))^(m+1))
      atTop (𝓝 1) := by
  let c : ℂ := -Complex.I*d
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hd)
  have hi : Tendsto (fun r : ℝ => (r:ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
  have ht : Tendsto (fun r : ℝ => c/((Q:ℂ)*((r:ℂ)⁻¹)^2+c)) atTop (𝓝 1) := by
    have hdlim := (hi.pow 2).const_mul (Q:ℂ)
    have hraw := (tendsto_const_nhds : Tendsto (fun _ : ℝ => c) atTop (𝓝 c)).div
      (hdlim.add_const c) (by simpa using hc)
    have hh : Tendsto (fun r : ℝ => c/((Q:ℂ)*((r:ℂ)⁻¹)^2+c))
        atTop (𝓝 (c/((Q:ℂ)*(0:ℂ)^2+c))) := by
      convert! hraw using 1
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, div_self hc] using hh
  have he : (fun r : ℝ => c*(r:ℂ)^2/((Q:ℂ)+c*(r:ℂ)^2))
      =ᶠ[atTop] (fun r : ℝ => c/((Q:ℂ)*((r:ℂ)⁻¹)^2+c)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    have hrC : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hden : (Q:ℂ)+c*(r:ℂ)^2 ≠ 0 := odd_shapeQuadratic_ne_zero hQ hd r
    have hden' : (Q:ℂ)*((r:ℂ)⁻¹)^2+c ≠ 0 := by
      have hh : (Q:ℂ)*((r:ℂ)⁻¹)^2+c = ((Q:ℂ)+c*(r:ℂ)^2)/(r:ℂ)^2 := by
        field_simp
      rw [hh]
      exact div_ne_zero hden (pow_ne_zero _ hrC)
    field_simp
  have hbase := ht.congr' he.symm
  simpa only [one_pow] using hbase.pow (m+1)

/-- Exact HT radial integral for k=m+1, on both curvature signs. -/
theorem odd_radial_integral (m : ℕ) {Q d : ℝ} (hQ : 0 < Q) (hd : d ≠ 0) :
    (∫ r : ℝ in Ioi 0, (r:ℂ)^(2*m+1)/shapeQuadratic Q (-Complex.I*d) r^(m+2)) =
      (2*((m+1:ℕ):ℂ)*(Q:ℂ)*(-Complex.I*d)^(m+1))⁻¹ := by
  let C : ℂ := 2*((m+1:ℕ):ℂ)*(Q:ℂ)*(-Complex.I*d)^(m+1)
  have hc : C ≠ 0 := by
    dsimp [C]
    apply mul_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Nat.succ_ne_zero m))
        (Complex.ofReal_ne_zero.mpr hQ.ne')
    · exact pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr hd))
  have hi := ((odd_radial_kernel_integrable m hQ hd).const_mul C).integrableOn (s := Ioi 0)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r (_hr : r ∈ Ici (0:ℝ)) => odd_quadratic_primitive_hasDerivAt m hQ hd r)
    hi (odd_quadratic_primitive_tendsto m hQ hd)
  have he : C*(∫ r : ℝ in Ioi 0,
      (r:ℂ)^(2*m+1)/shapeQuadratic Q (-Complex.I*d) r^(m+2)) = 1 := by
    simpa [C,integral_const_mul] using hFTC
  apply mul_left_cancel₀ hc
  rw [he,mul_inv_cancel₀ hc]

/-- LT polar infrastructure with the genuine HT radial exponent. -/
theorem odd_shapePeriod_eq_radial {n m : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*m+1) (Q : ℝ) (c : ℂ) :
    shapePeriod n (m+1) Q c = (shapeAngularConstant n:ℂ)*
      (∫ r : ℝ in Ioi 0, (r:ℂ)^(2*m+1)/shapeQuadratic Q c r^(m+2)) := by
  rw [shapePeriod_eq_intrinsic]
  have h := integral_shapeVandermonde_polar hn
    (fun r => (((Q:ℂ)+c*(r:ℂ)^2)^(m+2))⁻¹)
  rw [hdegree] at h
  have hi : shapePeriodIntrinsic n (m+1) Q c = shapeSphereIntegral n •
      (∫ r : ℝ in Ioi 0, (r:ℂ)^(2*m+1)/shapeQuadratic Q c r^(m+2)) := by
    simpa only [shapePeriodIntrinsic,shapeQuadratic,Complex.real_smul,
      Complex.ofReal_pow,div_eq_mul_inv,show m+1+1=m+2 by omega] using h
  rw [hi,smul_smul]
  rfl

/-- The manuscript's actual constrained shape period is nonzero at each odd
order p≥3, for Q>0 and either nonzero sign of d. -/
theorem odd_shapePeriod_ne_zero {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    {Q d : ℝ} (hQ : 0 < Q) (hd : d ≠ 0) :
    shapePeriod (p-1) (derivativeOrder p) Q (-Complex.I*d) ≠ 0 := by
  have hk := derivativeOrder_pos hp hp3
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hdeg : (p-1)-1+(p-1+1)*(p-1) = 2*m+1 := by
    have h := odd_shape_radial_exponent hp hp3
    rw [show p-1+1=p by omega]
    omega
  rw [hm,show Nat.succ m=m+1 by rfl,odd_shapePeriod_eq_radial (by omega) hdeg,
    odd_radial_integral m hQ hd]
  apply mul_ne_zero (Complex.ofReal_ne_zero.mpr (shapeAngularConstant_pos (by omega)).ne')
  apply inv_ne_zero
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Nat.succ_ne_zero m))
      (Complex.ofReal_ne_zero.mpr hQ.ne')
  · exact pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hd))

/-- The HT odd chart coefficient includes the phase -i absent from the even
LT density. The integral used here is the established actual shapePeriod. -/
def oddLocalLeadingCoefficient (a : OrderedChartData) (p : ℕ) : ℂ :=
  -Complex.I*localLeadingCoefficient a (p-1) (derivativeOrder p)

theorem oddLocalLeadingCoefficient_ne_zero (a : OrderedChartData)
    {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) : oddLocalLeadingCoefficient a p ≠ 0 := by
  apply mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
  apply localLeadingCoefficient_ne_zero_of_period
  exact odd_shapePeriod_ne_zero hp hp3 (a.Q_pos (by omega)) a.d_pos.ne'

theorem oddLocalLeadingCoefficient_swap (a : OrderedChartData) (p : ℕ) :
    oddLocalLeadingCoefficient a.swap p = oddLocalLeadingCoefficient a p := by
  unfold oddLocalLeadingCoefficient
  rw [localLeadingCoefficient_swap]

end
end IsingBulk.HT.First
