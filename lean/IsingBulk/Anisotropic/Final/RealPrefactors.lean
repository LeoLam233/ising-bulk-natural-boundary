import IsingBulk.Anisotropic.Final.LowPrefactor
import IsingBulk.Anisotropic.FormFactors.PublishedRealInput
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace IsingBulk.Anisotropic
noncomputable section
open Set

theorem rpow_quarter_pow_four {t : ℝ} (ht : 0≤t) : (t^(1/4:ℝ))^4=t := by
  rw [← Real.rpow_natCast,← Real.rpow_mul ht]
  norm_num

theorem lowPrefactor_real {lam x : ℝ} (hlam : 0<lam) (hx : criticalPoint lam<x) :
    FormFactors.lowPrefactor lam (x:ℂ) = (FormFactors.realMagnetizationSq lam x:ℂ) := by
  have hx0 : 0<x := lt_trans (criticalPoint_pos hlam) hx
  have hp := (criticalPoint_lt_iff_product_gt_one hlam hx0.le).mp hx
  have hs := lowPrefactor_actual_spec hlam
  have ht := lowRealRadicand_pos hlam hx
  apply positive_real_fourth_roots_eq (hs.2.2 x hx0 hp)
  · exact ⟨Complex.ofReal_im _,Real.rpow_pos_of_pos ht _⟩
  · rw [hs.2.1 _ ((real_mem_omegaL_iff hlam x).mpr hx),lowRadicand_real]
    symm
    dsimp [FormFactors.realMagnetizationSq,FormFactors.realProduct]
    exact_mod_cast rpow_quarter_pow_four ht.le

theorem highRealRadicand_pos {lam x : ℝ} (hlam : 0<lam)
    (hx0 : 0≤x) (hx : x<criticalPoint lam) : 0<1-(FormFactors.realProduct lam x)^2 := by
  have hp := real_product_strictMonoOn hlam hx0 (criticalPoint_pos hlam).le hx
  dsimp only at hp
  rw [sinh_product_criticalPoint hlam] at hp
  have hn : 0≤FormFactors.realProduct lam x :=
    mul_nonneg (Real.sinh_nonneg_iff.mpr hx0) (Real.sinh_nonneg_iff.mpr (mul_nonneg hlam.le hx0))
  change FormFactors.realProduct lam x<1 at hp
  nlinarith

theorem real_mem_omegaH_of_nonneg_lt_critical {lam x : ℝ} (hlam : 0<lam)
    (hx0 : 0≤x) (hx : x<criticalPoint lam) : (x:ℂ)∈omegaH lam := by
  have hh : sliceH lam 0=criticalPoint lam := by
    simp [sliceH,sliceQInv_one hlam,criticalPoint]
  change |(x:ℂ).im|<sliceY lam ∧ |(x:ℂ).re|<sliceH lam (x:ℂ).im
  simpa only [Complex.ofReal_im,Complex.ofReal_re,abs_zero,abs_of_nonneg hx0,hh] using
    And.intro (sliceY_pos hlam) hx

theorem highPrefactor_real {lam x : ℝ} (hlam : 0<lam)
    (hx0 : 0≤x) (hx : x<criticalPoint lam) :
    FormFactors.highPrefactor lam (x:ℂ) = Complex.ofReal (Real.rpow (1-FormFactors.realProduct lam x^2) (1/4)) := by
  let q : ℝ → ℂ := fun t => Complex.ofReal (Real.rpow (1-FormFactors.realProduct lam t^2) (1/4))
  have hs := highPrefactor_actual_spec hlam
  have hq : Continuous q := by
    dsimp [q]
    apply Complex.continuous_ofReal.comp
    apply (Real.continuous_rpow_const (by norm_num : (0:ℝ)≤1/4)).comp
    exact continuous_const.sub ((Real.continuous_sinh.mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).pow 2)
  have hqne : ∀ t∈Ico 0 (criticalPoint lam), q t≠0 := by
    intro t ht
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt
      (Real.rpow_pos_of_pos (highRealRadicand_pos hlam ht.1 ht.2) _))
  have heq : EqOn (fun t : ℝ => FormFactors.highPrefactor lam (t:ℂ)) q
      (Ico 0 (criticalPoint lam)) := by
    apply continuous_fourth_roots_eqOn isPreconnected_Ico
      (hs.1.continuousOn.comp Complex.continuous_ofReal.continuousOn
        (fun t ht => real_mem_omegaH_of_nonneg_lt_critical hlam ht.1 ht.2))
      hq.continuousOn hqne
    · intro t ht
      change FormFactors.highPrefactor lam (t:ℂ)^4=q t^4
      rw [hs.2.1 _ (real_mem_omegaH_of_nonneg_lt_critical hlam ht.1 ht.2)]
      have hp := rpow_quarter_pow_four (highRealRadicand_pos hlam ht.1 ht.2).le
      dsimp [q]
      rw [← Complex.ofReal_pow,hp]
      simp [spectralProduct,spectralS,spectralT,FormFactors.realProduct]
    · exact ⟨le_refl 0,criticalPoint_pos hlam⟩
    · simpa [q,FormFactors.realProduct] using hs.2.2
  exact heq ⟨hx0,hx⟩

end
end IsingBulk.Anisotropic
