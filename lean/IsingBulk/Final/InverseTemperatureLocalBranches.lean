import IsingBulk.Final.InverseTemperature

/-! Actual local inverse-temperature branches, with no global single-valued
beta assumption. The two imaginary axis branch points are explicitly excluded
from this construction. -/
namespace IsingBulk.Final
noncomputable section
open Complex Filter Set
open scoped Topology

def inverseTemperatureLeft (J : ℝ) (s : ℂ) : ℂ :=
  -inverseTemperatureBranch J (-s)

theorem inverseTemperatureLeft_regular {s : ℂ} (hs : s.re < 0)
    {J : ℝ} (hJ : 0 < J) :
    AnalyticAt ℂ (inverseTemperatureLeft J) s ∧ inverseTemperatureLeft J s ≠ 0 := by
  have hneg : 0 < (-s).re := by simpa only [Complex.neg_re] using neg_pos.mpr hs
  obtain ⟨ha,hn⟩ := inverseTemperatureBranch_regular hneg hJ
  constructor
  · exact (ha.comp (f := fun t : ℂ => -t) analyticAt_id.neg).neg
  · exact neg_ne_zero.mpr hn

theorem inverseTemperatureLeft_relation {s : ℂ} (hs : s.re < 0)
    {J : ℝ} (hJ : 0 < J) :
    Complex.sinh (2*(J:ℂ)*inverseTemperatureLeft J s)=s := by
  have hneg : 0 < (-s).re := by simpa only [Complex.neg_re] using neg_pos.mpr hs
  have h := inverseTemperatureBranch_relation hneg hJ
  simp only [inverseTemperatureLeft,mul_neg,Complex.sinh_neg,h,neg_neg]

/-- Nonvanishing belongs to every genuine branch, not just our chosen formula. -/
theorem inverseTemperature_nonzero_of_relation {s beta : ℂ} {J : ℝ}
    (hs : s ≠ 0) (hrel : Complex.sinh (2*(J:ℂ)*beta)=s) : beta ≠ 0 := by
  intro hb
  rw [hb,mul_zero,Complex.sinh_zero] at hrel
  exact hs hrel.symm

/-- A local branch is internally constructed at every point off the imaginary
axis. The relation holds on a full open neighborhood, not merely at its center. -/
theorem local_inverseTemperature_exists {s : ℂ} (hs : s.re ≠ 0)
    {J : ℝ} (hJ : 0 < J) :
    ∃ beta : ℂ → ℂ, AnalyticAt ℂ beta s ∧ beta s ≠ 0 ∧
      ∀ᶠ t : ℂ in 𝓝 s, Complex.sinh (2*(J:ℂ)*beta t)=t := by
  rcases lt_or_gt_of_ne hs with hleft | hright
  · refine ⟨inverseTemperatureLeft J,(inverseTemperatureLeft_regular hleft hJ).1,
      (inverseTemperatureLeft_regular hleft hJ).2,?_⟩
    filter_upwards [Complex.continuous_re.continuousAt.eventually (Iio_mem_nhds hleft)] with t ht
    exact inverseTemperatureLeft_relation ht hJ
  · refine ⟨inverseTemperatureBranch J,(inverseTemperatureBranch_regular hright hJ).1,
      (inverseTemperatureBranch_regular hright hJ).2,?_⟩
    filter_upwards [Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds hright)] with t ht
    exact inverseTemperatureBranch_relation ht hJ

theorem unit_nonbranch_real_ne_zero {s : ℂ} (hs : ‖s‖=1)
    (hI : s ≠ Complex.I) (hnI : s ≠ -Complex.I) : s.re ≠ 0 := by
  intro hr
  have hsq : s.im^2=1 := by
    have h := Complex.sq_norm s
    simp only [hs,one_pow,Complex.normSq_apply,hr,zero_mul,zero_add] at h
    nlinarith
  rcases sq_eq_one_iff.mp hsq with hi | hi
  · apply hI
    apply Complex.ext <;> simp [hr,hi]
  · apply hnI
    apply Complex.ext <;> simp [hr,hi]

/-- All unit-circle points except the actual inverse-sinh branch points have
an explicitly constructed analytic nonzero inverse-temperature germ. -/
theorem unit_local_inverseTemperature_exists {s : ℂ} (hs : ‖s‖=1)
    (hI : s ≠ Complex.I) (hnI : s ≠ -Complex.I) {J : ℝ} (hJ : 0 < J) :
    ∃ beta : ℂ → ℂ, AnalyticAt ℂ beta s ∧ beta s ≠ 0 ∧
      ∀ᶠ t : ℂ in 𝓝 s, Complex.sinh (2*(J:ℂ)*beta t)=t :=
  local_inverseTemperature_exists (unit_nonbranch_real_ne_zero hs hI hnI) hJ

end
end IsingBulk.Final
