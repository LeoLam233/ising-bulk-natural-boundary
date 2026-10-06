import IsingBulk.First.NearInfinityBulkSeries
import IsingBulk.Algebra.SelectedPoint

/-! The E2 expression has an internally verified nonvanishing holomorphic
branch at every nonaxis unit point. No physical identity is postulated here. -/
namespace IsingBulk.Final
noncomputable section
open Filter Set
open scoped Topology

theorem unit_inverse_power_argument_re_pos {z : ℂ} (hz : ‖z‖ = 1)
    (hfour : z^(4:ℕ) ≠ 1) : 0 < (1-(z^(4:ℕ))⁻¹).re := by
  have hn : ‖(z^(4:ℕ))⁻¹‖ = 1 := by rw [norm_inv,norm_pow,hz]; norm_num
  have hle : ((z^(4:ℕ))⁻¹).re ≤ 1 := by simpa only [hn] using Complex.re_le_norm ((z^(4:ℕ))⁻¹)
  have hne : ((z^(4:ℕ))⁻¹).re ≠ 1 := by
    intro heq
    have hi : ((z^(4:ℕ))⁻¹).im = 0 := Complex.abs_re_eq_norm.mp (by rw [heq,hn]; norm_num)
    have hone : (z^(4:ℕ))⁻¹ = 1 := Complex.ext (by simpa using heq) (by simpa using hi)
    exact hfour (inv_eq_one.mp hone)
  simpa only [Complex.sub_re,Complex.one_re] using sub_pos.mpr (lt_of_le_of_ne hle hne)

theorem magnetizationSquared_ne_zero_at_unit_nonaxis {z : ℂ} (hz : ‖z‖ = 1)
    (hfour : z^(4:ℕ) ≠ 1) : IsingBulk.First.magnetizationSquared z ≠ 0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  left
  intro heq
  have h := unit_inverse_power_argument_re_pos hz hfour
  rw [heq] at h
  norm_num at h

theorem magnetizationSquared_analyticAt_unit_nonaxis {z : ℂ} (hz : ‖z‖ = 1)
    (hfour : z^(4:ℕ) ≠ 1) : AnalyticAt ℂ IsingBulk.First.magnetizationSquared z := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have ha : AnalyticAt ℂ (fun s : ℂ => 1-(s^(4:ℕ))⁻¹) z :=
    analyticAt_const.sub ((analyticAt_id.pow 4).inv (pow_ne_zero 4 hz0))
  have hp : (1-(z^(4:ℕ))⁻¹) ∈ Complex.slitPlane :=
    Or.inl (unit_inverse_power_argument_re_pos hz hfour)
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have he := ha.eventually_analyticAt
  have hs := ha.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hp)
  filter_upwards [he,hs] with s has hsp
  exact has.differentiableAt.cpow_const hsp

theorem first_quadrant_pow_four_ne_one {z : ℂ} (hr : 0 < z.re) (hi : 0 < z.im) :
    z^(4:ℕ) ≠ 1 := by
  intro h
  have hp : (z-1)*(z+1)*(z-Complex.I)*(z+Complex.I) = 0 := by
    calc
      _ = (z^2-1)*(z^2-Complex.I^2) := by ring
      _ = z^4-1 := by rw [Complex.I_sq]; ring
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hp with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · have := congrArg Complex.im (sub_eq_zero.mp h)
        simp only [Complex.one_im] at this
        linarith
      · have := congrArg Complex.im (eq_neg_of_add_eq_zero_left h)
        norm_num at this
        linarith
    · have := congrArg Complex.re (sub_eq_zero.mp h)
      simp only [Complex.I_re] at this
      linarith
  · have := congrArg Complex.re (eq_neg_of_add_eq_zero_left h)
    norm_num at this
    linarith

theorem selectedPoint_magnetization_regular {p : ℕ} {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) :
    AnalyticAt ℂ IsingBulk.First.magnetizationSquared (IsingBulk.PrimeFamily.selectedPoint p a b) ∧
    IsingBulk.First.magnetizationSquared (IsingBulk.PrimeFamily.selectedPoint p a b) ≠ 0 := by
  have hc := IsingBulk.PrimeFamily.cosineAverage_bounds ha hb
  have hr : 0 < (IsingBulk.PrimeFamily.selectedPoint p a b).re := by
    rw [IsingBulk.PrimeFamily.selectedPoint,Complex.exp_ofReal_mul_I_re,Real.cos_arccos]
    · exact hc.1
    · linarith
    · exact hc.2.le
  have hi : 0 < (IsingBulk.PrimeFamily.selectedPoint p a b).im := by
    rw [IsingBulk.PrimeFamily.selectedPoint,Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hc.2)
      (Real.arccos_lt_pi.mpr (by linarith))
  have hz : ‖IsingBulk.PrimeFamily.selectedPoint p a b‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have h4 := first_quadrant_pow_four_ne_one hr hi
  exact ⟨magnetizationSquared_analyticAt_unit_nonaxis hz h4,
    magnetizationSquared_ne_zero_at_unit_nonaxis hz h4⟩

end
end IsingBulk.Final
