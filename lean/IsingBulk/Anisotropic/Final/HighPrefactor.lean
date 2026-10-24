import IsingBulk.Anisotropic.Final.NormalizedRoot
import IsingBulk.Anisotropic.FormFactors.ComplexContours
import IsingBulk.Anisotropic.Geometry.HighTopology
import IsingBulk.Anisotropic.Geometry.DomainNonvanishing

namespace IsingBulk.Anisotropic
noncomputable section
open Set

theorem spectralProduct_analytic (lam : ℝ) (z : ℂ) :
    AnalyticAt ℂ (spectralProduct lam) z := by
  exact Complex.analyticAt_sinh.mul
    (Complex.analyticAt_sinh.comp (analyticAt_const.mul analyticAt_id))

theorem exists_highBranch {lam : ℝ} (hlam : 0 < lam) :
    ∃ f, FormFactors.HighBranch lam f := by
  apply exists_normalized_analytic_fourth_root (omegaH_isSimplyConnected hlam)
    (omegaH_isOpen hlam)
  · intro z _
    exact analyticAt_const.sub ((spectralProduct_analytic lam z).pow 2)
  · intro z hz he
    exact omegaH_product_sq_ne_one hlam hz (sub_eq_zero.mp he).symm
  · exact zero_mem_omegaH hlam
  · simp [spectralProduct,spectralS,spectralT]

theorem highPrefactor_actual_spec {lam : ℝ} (hlam : 0 < lam) :
    FormFactors.HighBranch lam (FormFactors.highPrefactor lam) :=
  FormFactors.highPrefactor_spec (exists_highBranch hlam)

theorem highBranch_unique {lam : ℝ} (hlam : 0 < lam) {f g : ℂ → ℂ}
    (hf : FormFactors.HighBranch lam f) (hg : FormFactors.HighBranch lam g) :
    EqOn f g (omegaH lam) := by
  apply analytic_fourth_roots_eqOn (omegaH_isOpen hlam)
    (omegaH_isSimplyConnected hlam).isPathConnected.isConnected.isPreconnected hf.1 hg.1
    (fun z hz => (hf.2.1 z hz).trans (hg.2.1 z hz).symm)
    (zero_mem_omegaH hlam) (hf.2.2.trans hg.2.2.symm)
  rw [hf.2.2]
  exact one_ne_zero

end
end IsingBulk.Anisotropic
