import IsingBulk.HT.Final.InteriorFullGerm
import IsingBulk.HT.Final.PhysicalTemperature
import IsingBulk.Final.AnalyticFactorTransfer

/-! The actual full susceptibility germ, with its physical inverse-temperature
factor. The real representation identifies this independently constructed germ. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.Final Set

/-- Physical chi, including beta, on the complete high-temperature disk. -/
def interiorPhysicalSusceptibility (J : ℝ) (s : ℂ) : ℂ :=
  inverseTemperatureBranch J s * interiorFullBulk s

/-- The same physical germ in the exterior coordinate. -/
def exteriorPhysicalSusceptibility (J : ℝ) (t : ℂ) : ℂ :=
  inverseTemperatureBranch J (t⁻¹) * exteriorFullBulk t

theorem interiorPhysicalSusceptibility_analyticOn {J : ℝ} (hJ : 0 < J) :
    AnalyticOnNhd ℂ (interiorPhysicalSusceptibility J) {s : ℂ | ‖s‖ < 1} := by
  intro s hs
  exact (inverseTemperatureBranch_analyticAt_disk hJ hs).mul
    (interiorFullBulk_analyticOn s hs)

theorem exteriorPhysicalSusceptibility_analyticOn {J : ℝ} (hJ : 0 < J) :
    AnalyticOnNhd ℂ (exteriorPhysicalSusceptibility J) {t : ℂ | 1 < ‖t‖} := by
  intro t ht
  change 1 < ‖t‖ at ht
  have ht0 : t ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hi : ‖t⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ ht
  exact ((inverseTemperatureBranch_analyticAt_disk hJ hi).comp
    (analyticAt_id.inv ht0)).mul (exteriorFullBulk_analyticOn t ht)

theorem interiorPhysicalSusceptibility_eq_exterior {J : ℝ} {s : ℂ} (hs : s ≠ 0) :
    interiorPhysicalSusceptibility J s = exteriorPhysicalSusceptibility J (s⁻¹) := by
  simp only [interiorPhysicalSusceptibility, exteriorPhysicalSusceptibility, inv_inv,
    interiorFullBulk_eq_exterior hs]

/-- The only physical input is the explicit real full-lattice expansion. -/
theorem physicalSusceptibility_real_germ {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} (hrep : PhysicalSusceptibilityRepresentation J chi)
    {x : ℝ} (hx : 0 < x) (hxsmall : x < 1/16) :
    chi (x:ℂ) = interiorPhysicalSusceptibility J (x:ℂ) := by
  have he := interiorFullBulk_physical_real_germ hrep hx hxsmall
  have hb := (inverseTemperatureBranch_regular
    (show 0 < (x:ℂ).re by simpa only [Complex.ofReal_re] using hx) hJ).2
  have hid := (div_eq_iff hb).mp he
  simpa only [interiorPhysicalSusceptibility, mul_comm] using hid

/-- Local physical beta transfer at either selected nonimaginary unit point.
This support theorem assumes only the indicated obstruction for the actual
constructed bulk; it does not claim that the pending FIRST/TAIL assembly ran. -/
theorem no_exterior_physical_extension_of_bulk {J : ℝ} (hJ : 0 < J)
    {t : ℂ} (ht : ‖t‖ = 1) (hre : (t⁻¹).re ≠ 0)
    (hbulk : ¬ HasExteriorExtension exteriorFullBulk t) :
    ¬ HasExteriorExtension (exteriorPhysicalSusceptibility J) t := by
  have ht0 : t ≠ 0 := norm_ne_zero_iff.mp (by rw [ht]; norm_num)
  have hi : ‖t⁻¹‖ = 1 := by rw [norm_inv, ht, inv_one]
  obtain ⟨ha, hn⟩ := inverseTemperatureBranch_regular_unit_nonimaginary hJ hi hre
  exact no_extension_mul_analytic_factor (ha.comp (analyticAt_id.inv ht0)) hn hbulk

end
end IsingBulk.HT.Final
