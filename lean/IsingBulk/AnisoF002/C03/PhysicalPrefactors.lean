import IsingBulk.AnisoF002.C03.PhysicalFourthRoots
import IsingBulk.AnisoF002.C03.PhysicalPrefactorGeometry

/-!
# Genuine branches for the original physical susceptibility prefactors

The literal `HighBranch` and `LowBranch` predicates are proved on F002's
entire exact physical domains.  The selected original prefactor functions
are then justified by unfolding their definitions, including their otherwise
unusable zero fallbacks.  Positive-real normalization is proved at every
physical temperature, with the quarter powers unchanged.
-/

namespace IsingBulk.AnisoF002.Physical
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open Geometry Set

theorem exists_highBranch {lam : ℝ} (hlam : 0 < lam) : ∃ f, HighBranch lam f := by
  have he := exists_analytic_fourth_root_at (omegaHF002_isSimplyConnected hlam)
    (isOpen_omegaHF002 hlam)
    ((highRadicand_analytic lam).mono (subset_univ _))
    (fun _ hz => highRadicand_ne_zero hlam hz) (zero_mem_omegaHF002 hlam)
    (show (1 : ℂ) ^ 4 = 1 - spectralProduct lam 0 ^ 2 by
      simp [spectralProduct, spectralS, spectralT])
  exact he

theorem highPrefactor_spec {lam : ℝ} (hlam : 0 < lam) :
    HighBranch lam (highPrefactor lam) := by
  have he := exists_highBranch hlam
  simp only [highPrefactor, dite_eq_left he]
  exact Classical.choose_spec he

theorem highBranch_real_normalization {lam : ℝ} (hlam : 0 < lam) {f : ℂ → ℂ}
    (hf : HighBranch lam f) {x : ℝ} (hx : 0 ≤ x) (hxc : x < criticalPointF002 lam) :
    f (x : ℂ) = ((1 - realProduct lam x ^ 2) ^ (1 / 4 : ℝ) : ℝ) := by
  let q : ℝ → ℂ := fun y => ((1 - realProduct lam y ^ 2) ^ (1 / 4 : ℝ) : ℝ)
  have hqpow : ∀ y ∈ Ico (0 : ℝ) (criticalPointF002 lam),
      q y ^ 4 = ((1 - realProduct lam y ^ 2 : ℝ) : ℂ) := by
    intro y hy
    dsimp only [q]
    exact_mod_cast positive_real_fourth_power (high_real_radicand_pos hlam hy.1 hy.2).le
  have hqne : ∀ y ∈ Ico (0 : ℝ) (criticalPointF002 lam), q y ≠ 0 := by
    intro y hy
    exact Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (high_real_radicand_pos hlam hy.1 hy.2) _).ne'
  have hqc : Continuous q := Complex.continuous_ofReal.comp
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4)).comp
      (continuous_const.sub ((realProduct_continuous lam).pow 2)))
  have hfc : ContinuousOn (fun y : ℝ => f (y : ℂ)) (Ico 0 (criticalPointF002 lam)) :=
    hf.1.continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun y hy => nonnegative_real_mem_high hlam hy.1 hy.2)
  have he : EqOn (fun y : ℝ => f (y : ℂ)) q (Ico 0 (criticalPointF002 lam)) := by
    apply continuousFourthRoots_unique isPreconnected_Ico hfc hqc.continuousOn hqne
    · intro y hy
      rw [hf.2.1 _ (nonnegative_real_mem_high hlam hy.1 hy.2), hqpow y hy,
        spectralProduct_real]
      norm_cast
    · exact ⟨le_rfl, criticalPointF002_pos hlam⟩
    · simpa [q, realProduct] using hf.2.2
  exact he ⟨hx, hxc⟩

theorem highPrefactor_real_normalization {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ} (hx : 0 ≤ x) (hxc : x < criticalPointF002 lam) :
    highPrefactor lam (x : ℂ) = ((1 - realProduct lam x ^ 2) ^ (1 / 4 : ℝ) : ℝ) :=
  highBranch_real_normalization hlam (highPrefactor_spec hlam) hx hxc

theorem low_real_radicand_continuousOn {lam : ℝ} (hlam : 0 < lam) :
    ContinuousOn (fun x => 1 - (realProduct lam x)⁻¹ ^ 2) (Ioi (criticalPointF002 lam)) := by
  apply continuousOn_const.sub
  apply ContinuousOn.pow
  apply ContinuousOn.inv₀ (realProduct_continuous lam).continuousOn
  intro x hx
  exact (realProduct_pos hlam (lt_trans (criticalPointF002_pos hlam) hx)).ne'

theorem exists_lowBranch {lam : ℝ} (hlam : 0 < lam) : ∃ f, LowBranch lam f := by
  let q : ℝ → ℂ := fun x => ((1 - (realProduct lam x)⁻¹ ^ 2) ^ (1 / 4 : ℝ) : ℝ)
  let x₀ := criticalPointF002 lam + 1
  have hx₀ : criticalPointF002 lam < x₀ := by dsimp [x₀]; linarith
  have hqpow : ∀ x ∈ Ioi (criticalPointF002 lam),
      q x ^ 4 = 1 - (spectralProduct lam (x : ℂ))⁻¹ ^ 2 := by
    intro x hx
    rw [spectralProduct_real]
    have hp := positive_real_fourth_power (low_real_radicand_pos hlam hx).le
    dsimp only [q]
    exact_mod_cast hp
  have hqne : ∀ x ∈ Ioi (criticalPointF002 lam), q x ≠ 0 := by
    intro x hx
    exact Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (low_real_radicand_pos hlam hx) _).ne'
  have hqc : ContinuousOn q (Ioi (criticalPointF002 lam)) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4)).comp_continuousOn
        (low_real_radicand_continuousOn hlam))
  obtain ⟨g, hg, hp, hg₀⟩ := exists_analytic_fourth_root_at
    (omegaLF002_isSimplyConnected hlam) (isOpen_omegaLF002 hlam)
    (lowRadicand_analytic hlam) (fun _ hz => lowRadicand_ne_zero hlam hz)
    ((real_mem_omegaLF002_iff hlam).mpr hx₀) (hqpow x₀ hx₀)
  have hgc : ContinuousOn (fun x : ℝ => g (x : ℂ)) (Ioi (criticalPointF002 lam)) :=
    hg.continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun _ hx => (real_mem_omegaLF002_iff hlam).mpr hx)
  have he : EqOn (fun x : ℝ => g (x : ℂ)) q (Ioi (criticalPointF002 lam)) := by
    apply continuousFourthRoots_unique isPreconnected_Ioi hgc hqc hqne
    · intro x hx
      exact (hp _ ((real_mem_omegaLF002_iff hlam).mpr hx)).trans (hqpow x hx).symm
    · exact hx₀
    · exact hg₀
  refine ⟨g, hg, hp, ?_⟩
  intro x hx hprod
  have hxc := (critical_lt_iff_realProduct_gt_one hlam hx.le).mpr hprod
  have heq : g (x : ℂ) = q x := he hxc
  rw [heq]
  exact ⟨Complex.ofReal_im _, Real.rpow_pos_of_pos (low_real_radicand_pos hlam hxc) _⟩

theorem lowPrefactor_spec {lam : ℝ} (hlam : 0 < lam) : LowBranch lam (lowPrefactor lam) := by
  have he := exists_lowBranch hlam
  simp only [lowPrefactor, dite_eq_left he]
  exact Classical.choose_spec he

theorem lowBranch_real_normalization {lam : ℝ} (hlam : 0 < lam) {f : ℂ → ℂ}
    (hf : LowBranch lam f) {x : ℝ} (hx : criticalPointF002 lam < x) :
    f (x : ℂ) = (realMagnetizationSq lam x : ℂ) := by
  have hx0 := lt_trans (criticalPointF002_pos hlam) hx
  have hp := (critical_lt_iff_realProduct_gt_one hlam hx0.le).mp hx
  apply positive_real_fourth_root_unique (hf.2.2 x hx0 hp) (low_real_radicand_pos hlam hx)
  rw [hf.2.1 _ ((real_mem_omegaLF002_iff hlam).mpr hx), spectralProduct_real]
  norm_cast

theorem lowPrefactor_real_normalization {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ} (hx : criticalPointF002 lam < x) :
    lowPrefactor lam (x : ℂ) = (realMagnetizationSq lam x : ℂ) :=
  lowBranch_real_normalization hlam (lowPrefactor_spec hlam) hx

theorem highPrefactor_analytic_nonzero {lam : ℝ} (hlam : 0 < lam) :
    AnalyticOnNhd ℂ (highPrefactor lam) (omegaH lam) ∧
      ∀ z ∈ omegaH lam, highPrefactor lam z ≠ 0 := by
  refine ⟨(highPrefactor_spec hlam).1, ?_⟩
  intro z hz he
  have hp := (highPrefactor_spec hlam).2.1 z hz
  rw [he, zero_pow (by decide : (4 : ℕ) ≠ 0)] at hp
  exact highRadicand_ne_zero hlam hz hp.symm

theorem lowPrefactor_analytic_nonzero {lam : ℝ} (hlam : 0 < lam) :
    AnalyticOnNhd ℂ (lowPrefactor lam) (omegaL lam) ∧
      ∀ z ∈ omegaL lam, lowPrefactor lam z ≠ 0 := by
  refine ⟨(lowPrefactor_spec hlam).1, ?_⟩
  intro z hz he
  have hp := (lowPrefactor_spec hlam).2.1 z hz
  rw [he, zero_pow (by decide : (4 : ℕ) ≠ 0)] at hp
  exact lowRadicand_ne_zero hlam hz hp.symm

end
end IsingBulk.AnisoF002.Physical
