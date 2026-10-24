import IsingBulk.First.ShapeRadialAnalytic

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace IsingBulk.Anisotropic.RegularEdges

def oddRadialKernel (m : ℕ) (Q c : ℂ) (r : ℝ) : ℂ :=
  (r:ℂ)^(2*m+1)/(Q+c*(r:ℂ)^2)^(m+2)

theorem oddQuadratic_lower {Q c : ℂ} (_hQ : 0<Q.re) (_hc : 0<c.re) (r : ℝ) :
    min Q.re c.re*(1+r^2) ≤ ‖Q+c*(r:ℂ)^2‖ := by
  have hr : (Q+c*(r:ℂ)^2).re=Q.re+c.re*r^2 := by simp [← Complex.ofReal_pow,Complex.mul_re]
  calc
    _ ≤ Q.re+c.re*r^2 := by
      have h1 := min_le_left Q.re c.re
      have h2 := mul_le_mul_of_nonneg_right (min_le_right Q.re c.re) (sq_nonneg r)
      nlinarith
    _ = (Q+c*(r:ℂ)^2).re := hr.symm
    _ ≤ _ := Complex.re_le_norm _

theorem oddQuadratic_ne_zero {Q c : ℂ} (hQ : 0<Q.re) (hc : 0<c.re) (r : ℝ) :
    Q+c*(r:ℂ)^2≠0 := by
  apply norm_pos_iff.mp
  exact (mul_pos (lt_min hQ hc) (by positivity)).trans_le (oddQuadratic_lower hQ hc r)

theorem oddRadialKernel_bound (m : ℕ) {Q c : ℂ} (hQ : 0<Q.re) (hc : 0<c.re) (r : ℝ) :
    ‖oddRadialKernel m Q c r‖ ≤ ((min Q.re c.re)^(m+2))⁻¹*(1+r^2)⁻¹ := by
  let a := min Q.re c.re
  have ha : 0<a := lt_min hQ hc
  have hr : 0<1+r^2 := by positivity
  have habs : |r|≤1+r^2 := by nlinarith [sq_nonneg (|r|-1),sq_abs r]
  have hnum : |r|^(2*m+1) ≤ (1+r^2)^(m+1) := by
    rw [pow_succ,pow_mul, sq_abs, pow_succ]
    exact mul_le_mul (pow_le_pow_left₀ (sq_nonneg r) (show r^2≤1+r^2 by linarith) m) habs
      (abs_nonneg r) (pow_nonneg hr.le m)
  have hden := pow_le_pow_left₀ (mul_nonneg ha.le hr.le) (oddQuadratic_lower hQ hc r) (m+2)
  rw [oddRadialKernel,norm_div,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ (1+r^2)^(m+1)/(a*(1+r^2))^(m+2) :=
      div_le_div₀ (by positivity) hnum (pow_pos (mul_pos ha hr) _) hden
    _ = _ := by
      change (1+r^2)^(m+1)/(a*(1+r^2))^(m+2) = (a^(m+2))⁻¹*(1+r^2)⁻¹
      rw [mul_pow]
      field_simp [ha.ne',hr.ne']
      simp only [show m+2=(m+1)+1 by omega,pow_succ]
      ring

theorem oddRadialKernel_integrable (m : ℕ) {Q c : ℂ} (hQ : 0<Q.re) (hc : 0<c.re) :
    Integrable (oddRadialKernel m Q c) := by
  refine (integrable_inv_one_add_sq.const_mul (((min Q.re c.re)^(m+2))⁻¹)).mono' ?_
    (Eventually.of_forall (oddRadialKernel_bound m hQ hc))
  apply Continuous.aestronglyMeasurable
  unfold oddRadialKernel
  exact (by fun_prop : Continuous (fun r : ℝ => (r:ℂ)^(2*m+1))).div
    (by fun_prop) (fun r => pow_ne_zero _ (oddQuadratic_ne_zero hQ hc r))

end IsingBulk.Anisotropic.RegularEdges
