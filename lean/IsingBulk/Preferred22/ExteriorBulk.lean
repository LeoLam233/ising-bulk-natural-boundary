import IsingBulk.Preferred22.NormalConvergence
import IsingBulk.Preferred22.EvenSymmetry
import IsingBulk.Preferred22.Prefactors
import IsingBulk.Preferred22.BoundaryPropagation
import IsingBulk.Preferred22.NonCancellation

/-! Exterior holomorphy and both symmetries of the literal complete bulk
function. The boundary assembly below keeps every unproved analytic obligation
visible as a premise, including the actual absolute infinite tail. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Filter Set
open scoped Topology

theorem exterior_inverse_power_argument_re_pos {s : ℂ} (hs : 1 < ‖s‖) :
    0 < (1-(s^(4:ℕ))⁻¹).re := by
  have hp : 1 < ‖s‖^4 := by
    have hs2 : 1 < ‖s‖^2 := by nlinarith [norm_nonneg s]
    nlinarith [sq_nonneg (‖s‖^2-1)]
  have hn : ‖(s^(4:ℕ))⁻¹‖ < 1 := by
    rw [norm_inv,norm_pow]
    exact inv_lt_one_of_one_lt₀ hp
  have hr := (Complex.re_le_norm ((s^(4:ℕ))⁻¹)).trans_lt hn
  simpa only [Complex.sub_re,Complex.one_re] using sub_pos.mpr hr

theorem magnetizationSquared_analyticAt_exterior {s : ℂ} (hs : 1 < ‖s‖) :
    AnalyticAt ℂ magnetizationSquared s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have ha : AnalyticAt ℂ (fun t : ℂ => 1-(t^(4:ℕ))⁻¹) s :=
    analyticAt_const.sub ((analyticAt_id.pow 4).inv (pow_ne_zero 4 hs0))
  have hp : (1-(s^(4:ℕ))⁻¹) ∈ Complex.slitPlane :=
    Or.inl (exterior_inverse_power_argument_re_pos hs)
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [ha.eventually_analyticAt,
    ha.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hp)] with t ht htp
  exact ht.differentiableAt.cpow_const htp

theorem magnetizationSquared_ne_zero_exterior {s : ℂ} (hs : 1 < ‖s‖) :
    magnetizationSquared s ≠ 0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  left
  intro heq
  have h := exterior_inverse_power_argument_re_pos hs
  rw [heq] at h
  norm_num at h

theorem magnetizationSquared_even (s : ℂ) : magnetizationSquared (-s)=magnetizationSquared s := by
  norm_num [magnetizationSquared,neg_pow]

theorem magnetizationSquared_conj {s : ℂ} (hs : 1 < ‖s‖) :
    magnetizationSquared (star s)=star (magnetizationSquared s) := by
  have hp : (1-(s^(4:ℕ))⁻¹) ∈ Complex.slitPlane :=
    Or.inl (exterior_inverse_power_argument_re_pos hs)
  have h := Complex.conj_cpow (1-(s^(4:ℕ))⁻¹) (1/4:ℂ) (Complex.slitPlane_arg_ne_pi hp)
  simpa [magnetizationSquared,Complex.star_def,map_ofNat] using h

theorem bulkFunction_analyticAt {s : ℂ} (hs : 1 < ‖s‖) : AnalyticAt ℂ bulkFunction s :=
  (magnetizationSquared_analyticAt_exterior hs).mul (evenSeries_analyticAt hs)

theorem bulkFunction_even {s : ℂ} (hs : 1 < ‖s‖) : bulkFunction (-s)=bulkFunction s := by
  simp only [bulkFunction,magnetizationSquared_even,evenSeries_even hs]

theorem bulkFunction_conj {s : ℂ} (hs : 1 < ‖s‖) : bulkFunction (star s)=star (bulkFunction s) := by
  simp only [bulkFunction,magnetizationSquared_conj hs,evenSeries_conj hs,star_mul]
  ring

/-- These are the exact still-required first, finite-complement, and higher-tail
claims for every selected prime root. No proof of this proposition is asserted. -/
def PreferredSelectedAnalyticObligations : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ a : ℤ, IsingBulk.PrimeFamily.Admissible p a →
    PreferredFirstSingularityStatement (IsingBulk.PrimeFamily.angleRoot p a) (2*p) ((2*p)^2/2-1) ∧
    PreferredFiniteComplementStatement (IsingBulk.PrimeFamily.angleRoot p a) (p-1) ((2*p)^2/2-1) ∧
    PreferredAbsoluteTailStatement (IsingBulk.PrimeFamily.angleRoot p a) (2*p) ((2*p)^2/2-1)

/-- Conditional assembly only: all points, including axes, follow once the
three concrete selected-point obligations are established by the Preferred chain. -/
theorem bulkFunction_boundary_of_selected_obligations
    (hselected : PreferredSelectedAnalyticObligations) :
    ∀ ζ : ℂ, ‖ζ‖=1 → ¬ HasExteriorExtension bulkFunction ζ := by
  apply unit_circle_no_extension_of_selected
    (fun _ hs => bulkFunction_even hs) (fun _ hs => bulkFunction_conj hs)
  rintro ζ ⟨p,a,hp,hp5,ha,rfl⟩
  obtain ⟨hf,hl,ht⟩ := hselected p hp hp5 a ha
  have hN : 2*(p-1+1)=2*p := by omega
  have hζ : ‖IsingBulk.PrimeFamily.angleRoot p a‖=1 := Complex.norm_exp_ofReal_mul_I _
  have he := evenSeries_no_extension_of_obligations hζ (p-1) ((2*p)^2/2-1)
    (by simpa only [hN] using hf) hl (by simpa only [hN] using ht)
  have hr : 0 < (IsingBulk.PrimeFamily.angleRoot p a).re := by
    simpa [IsingBulk.PrimeFamily.angleRoot,Complex.exp_mul_I,Complex.cos_ofReal_re] using
      Real.cos_pos_of_mem_Ioo ⟨by linarith [ha.1,Real.pi_pos],ha.2⟩
  have hi : 0 < (IsingBulk.PrimeFamily.angleRoot p a).im := by
    simpa [IsingBulk.PrimeFamily.angleRoot,Complex.exp_mul_I,Complex.sin_ofReal_re] using
      Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2,Real.pi_pos])
  have hfour := first_quadrant_pow_four_ne_one hr hi
  exact no_extension_mul_analytic_factor (magnetizationSquared_analyticAt_unit_nonaxis hζ hfour)
    (magnetizationSquared_ne_zero_at_unit_nonaxis hζ hfour) he

end
end IsingBulk.Preferred22
