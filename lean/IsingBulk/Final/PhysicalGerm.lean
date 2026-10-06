import IsingBulk.Final.ConditionalNaturalBoundary
import IsingBulk.Final.InverseTemperature
import IsingBulk.Final.AnalyticFactorTransfer

/-! The actual physical susceptibility germ on the right-half-plane chart.
The real PT/Yang inputs identify its real restriction. No globally single-
valued inverse temperature or physical susceptibility is asserted here. -/
namespace IsingBulk.Final
noncomputable section
open Set IsingBulk.First IsingBulk.Tail

def rightPhysicalBulk (J : ℝ) (s : ℂ) : ℂ :=
  inverseTemperatureBranch J s * exteriorNormalizedBulk s

def PhysicalSusceptibilityE1 (J : ℝ) (chi : ℂ → ℂ) (M : ℝ → ℂ) : Prop :=
  RealFredholmE1 (fun s => chi s/inverseTemperatureBranch J s) M

theorem rightPhysicalBulk_analyticOn {J : ℝ} (hJ : 0 < J) :
    AnalyticOnNhd ℂ (rightPhysicalBulk J) {s : ℂ | 1 < ‖s‖ ∧ 0 < s.re} := by
  intro s hs
  exact (inverseTemperatureBranch_regular hs.2 hJ).1.mul
    (exteriorNormalizedBulk_analyticOn s hs.1)

theorem physical_real_germ_identification {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} {M : ℝ → ℂ}
    (hE1 : PhysicalSusceptibilityE1 J chi M) (hE2 : YangMagnetizationE2 M) :
    AnalyticOnNhd ℂ (rightPhysicalBulk J) {s : ℂ | 1 < ‖s‖ ∧ 0 < s.re} ∧
      ∀ x : ℝ, 16 < x → chi (x:ℂ)=rightPhysicalBulk J (x:ℂ) := by
  refine ⟨rightPhysicalBulk_analyticOn hJ,?_⟩
  intro x hx
  have hrep := (physical_exterior_germ_identification hE1 hE2).2 x hx
  have hb0 := (inverseTemperatureBranch_regular
    (show 0 < (x:ℂ).re by simpa only [Complex.ofReal_re] using (show 0 < x by linarith)) hJ).2
  dsimp only [rightPhysicalBulk]
  have hh := (div_eq_iff hb0).mp hrep
  simpa only [mul_comm] using hh

theorem local_physical_branch_nonextension {beta : ℂ → ℂ} {z : ℂ}
    (hb : AnalyticAt ℂ beta z) (hb0 : beta z ≠ 0)
    (hX : ¬ HasExteriorExtension exteriorNormalizedBulk z) :
    ¬ HasExteriorExtension (fun s => beta s*exteriorNormalizedBulk s) z := by
  exact no_extension_mul_analytic_factor hb hb0 hX

theorem rightPhysicalBulk_nonextension {J : ℝ} (hJ : 0 < J) {z : ℂ}
    (hz : 0 < z.re) (hX : ¬ HasExteriorExtension exteriorNormalizedBulk z) :
    ¬ HasExteriorExtension (rightPhysicalBulk J) z := by
  obtain ⟨hb,hb0⟩ := inverseTemperatureBranch_regular hz hJ
  exact local_physical_branch_nonextension hb hb0 hX

end
end IsingBulk.Final
