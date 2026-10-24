import IsingBulk.Anisotropic.Final.Target
import IsingBulk.Anisotropic.Final.RealPrefactors
import IsingBulk.Anisotropic.FormFactors.PhysicalCovariance

namespace IsingBulk.Anisotropic
noncomputable section
open FormFactors

theorem lt_criticalPoint_of_product_lt_one {lam x : ℝ} (hlam : 0<lam)
    (hx : 0≤x) (hp : realProduct lam x<1) : x<criticalPoint lam := by
  by_contra hn
  have hh := (real_product_strictMonoOn hlam).monotoneOn
    (criticalPoint_pos hlam).le hx (le_of_not_gt hn)
  rw [sinh_product_criticalPoint hlam] at hh
  exact (not_le_of_gt hp) hh

/-- The genuine full covariance sums, including all lattice sites and every
particle order, identify the actual complex functions on both real phases. -/
theorem realPhysicalIdentification_of_published (J : ℝ) {lam : ℝ} (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    RealPhysicalIdentification J lam corrH corrL := by
  constructor
  · intro x hx hp
    obtain ⟨hs,he⟩ := high_covariance_sum hlam hx hp hphys
    have hxc := lt_criticalPoint_of_product_lt_one hlam hx.le hp
    have h : highNormalizedBulk lam (x:ℂ) = (highCovarianceSum corrH x:ℂ) := by
      rw [he,highNormalizedBulk,highPrefactor_real hlam hx.le hxc]
      rfl
    exact ⟨hs,h,highPhysicalBulk_real_of_covariance h⟩
  · intro x hx hp
    obtain ⟨hs,he⟩ := low_covariance_sum hlam hx hp hphys
    have hxc := (criticalPoint_lt_iff_product_gt_one hlam hx.le).mpr hp
    have h : lowNormalizedBulk lam (x:ℂ) = (lowCovarianceSum lam corrL x:ℂ) := by
      rw [he,lowNormalizedBulk,lowPrefactor_real hlam hxc]
    exact ⟨hs,h,lowPhysicalBulk_real_of_covariance h⟩

end
end IsingBulk.Anisotropic
