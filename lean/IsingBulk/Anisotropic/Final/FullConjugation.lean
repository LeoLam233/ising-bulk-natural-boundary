import IsingBulk.Anisotropic.Final.ConjugateTransport
import IsingBulk.Anisotropic.Final.ActualHolomorphy
import IsingBulk.Anisotropic.Final.PhysicalIdentification
import IsingBulk.Anisotropic.Geometry.DomainSymmetries

namespace IsingBulk.Anisotropic
noncomputable section
open Set FormFactors

theorem highNormalizedBulk_conjugate {lam : ℝ} (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    EqOn (fun z => star (highNormalizedBulk lam (star z))) (highNormalizedBulk lam) (omegaH lam) := by
  apply reflection_eqOn_of_real_interval (highNormalizedBulk_analyticOnNhd hlam)
    (omegaH_isPreconnected hlam) (omegaH_conj_iff lam) (criticalPoint_pos hlam)
    (fun x hx => real_mem_omegaH_of_nonneg_lt_critical hlam hx.1.le hx.2)
  intro x hx
  have hp := real_product_strictMonoOn hlam hx.1.le (criticalPoint_pos hlam).le hx.2
  dsimp only at hp
  rw [sinh_product_criticalPoint hlam] at hp
  have he := ((realPhysicalIdentification_of_published 1 hlam hphys).high x hx.1 hp).2.1
  rw [he]
  simp

theorem lowNormalizedBulk_conjugate {lam : ℝ} (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    EqOn (fun z => star (lowNormalizedBulk lam (star z))) (lowNormalizedBulk lam) (omegaL lam) := by
  apply reflection_eqOn_of_real_interval (lowNormalizedBulk_analyticOnNhd hlam)
    (omegaL_isPreconnected hlam) (omegaL_conj_iff lam)
    (a := criticalPoint lam+1) (b := criticalPoint lam+2) (by linarith)
    (fun x hx => (real_mem_omegaL_iff hlam x).mpr (by linarith [hx.1]))
  intro x hx
  have hxc : criticalPoint lam<x := by linarith [hx.1]
  have hx0 : 0<x := (criticalPoint_pos hlam).trans hxc
  have hp := (criticalPoint_lt_iff_product_gt_one hlam hx0.le).mp hxc
  have he := ((realPhysicalIdentification_of_published 1 hlam hphys).low x hx0 hp).2.1
  rw [he]
  simp

end
end IsingBulk.Anisotropic
