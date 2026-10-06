import IsingBulk.Final.ConditionalPhysicalBoundary

/-! Non-vacuity and source normalization checks for the actual physical
boundary-continuation predicate. No final audit-round status is implied. -/
namespace IsingBulk.Final
open Set Filter
open scoped Topology

example {J : ℝ} (hJ : 0 < J) :
    HasPhysicalBoundaryExtension J (fun _ : ℂ => 1) (1:ℂ) := by
  have hbeta := (inverseTemperatureBranch_regular (s := (1:ℂ)) (by norm_num) hJ).1
  have hrel : ∀ᶠ s : ℂ in 𝓝 (1:ℂ),
      Complex.sinh (2*(J:ℂ)*inverseTemperatureBranch J s)=s := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually
      (Ioi_mem_nhds (show 0 < (1:ℂ).re by norm_num))] with s hs
    exact inverseTemperatureBranch_relation hs hJ
  apply physical_boundary_extension_of_chart (by norm_num) hbeta hrel
  refine ⟨{s : ℂ | 0 < s.re},isOpen_lt continuous_const Complex.continuous_re,
    (by norm_num),fun s => inverseTemperatureBranch J s*1,?_,?_⟩
  · intro s hs
    exact (inverseTemperatureBranch_regular hs hJ).1.mul analyticAt_const
  · intro s hs
    rfl

#print axioms physical_no_boundary_extension
#print axioms theorem_conditional_physical
#check theorem_conditional_physical

end IsingBulk.Final
