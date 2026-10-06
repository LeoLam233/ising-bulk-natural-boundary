import IsingBulk.Final.PhysicalGerm

/-! Source normalization regression: manuscript line78 is X=chi/beta. -/
namespace IsingBulk.Final
open IsingBulk.Tail

example (J : ℝ) (s : ℂ) :
    rightPhysicalBulk J s = inverseTemperatureBranch J s*exteriorNormalizedBulk s := rfl

example (J : ℝ) (chi : ℂ → ℂ) (M : ℝ → ℂ) :
    PhysicalSusceptibilityE1 J chi M ↔
      RealFredholmE1 (fun s => chi s/inverseTemperatureBranch J s) M := Iff.rfl

example {J : ℝ} (hJ : 0 < J) {s : ℂ} (hs : 0 < s.re) :
    rightPhysicalBulk J s / inverseTemperatureBranch J s = exteriorNormalizedBulk s := by
  exact mul_div_cancel_left₀ _ (inverseTemperatureBranch_regular hs hJ).2

#print axioms rightPhysicalBulk_analyticOn
#print axioms physical_real_germ_identification
#print axioms rightPhysicalBulk_nonextension

end IsingBulk.Final
