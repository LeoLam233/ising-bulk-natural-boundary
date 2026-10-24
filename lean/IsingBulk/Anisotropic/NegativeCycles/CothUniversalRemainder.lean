import IsingBulk.Anisotropic.NegativeNormalForm.SimplePoleResidue

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric Filter NegativeNormalForm
open scoped Topology

/-- One fixed scalar analytic remainder, chosen before any particle number. -/
theorem exists_uniform_coth_remainder :
    ∃ (R : ℂ → ℂ) (r M : ℝ), 0<r ∧ 0<M ∧
      AnalyticOnNhd ℂ R (ball 0 r) ∧ (∀ z∈ball 0 r, ‖R z‖≤M) ∧
      ∀ z : ℂ, z≠0 → cothHalf id z=2/z+R z := by
  obtain ⟨R,hR,hEq⟩ := exists_analytic_coth_subtraction (F := id) (N := fun _ => (1:ℂ))
    (T := 0) analyticAt_id analyticAt_const rfl (by simp)
  have hev : ∀ᶠ z : ℂ in 𝓝 0, AnalyticAt ℂ R z ∧ ‖R z‖<‖R 0‖+1 :=
    hR.eventually_analyticAt.and (hR.continuousAt.norm.eventually_lt_const (by linarith))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨R,r,‖R 0‖+1,hr,by positivity,fun z hz => (hball hz).1,
    fun z hz => (hball hz).2.le,?_⟩
  intro z hz
  have hd : deriv (id : ℂ → ℂ) 0=1 := (hasDerivAt_id (0:ℂ)).deriv
  simpa only [one_mul,mul_one,hd,div_one,sub_zero] using hEq z hz

end
end IsingBulk.Anisotropic.NegativeCycles
