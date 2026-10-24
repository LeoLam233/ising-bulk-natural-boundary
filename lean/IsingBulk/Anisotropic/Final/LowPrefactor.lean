import IsingBulk.Anisotropic.Final.HighPrefactor
import IsingBulk.Anisotropic.Final.PositiveFourthRoot
import IsingBulk.Anisotropic.Geometry.LowTopology
import IsingBulk.Anisotropic.Geometry.PhysicalAxis

namespace IsingBulk.Anisotropic
noncomputable section
open Set

theorem lowRadicand_analytic {lam : ℝ} (hlam : 0 < lam) :
    AnalyticOnNhd ℂ (fun z => 1-(spectralProduct lam z)⁻¹^2) (omegaL lam) := by
  intro z hz
  exact analyticAt_const.sub (((spectralProduct_analytic lam z).inv
    (omegaL_product_ne_zero hlam hz)).pow 2)

theorem lowRadicand_ne_zero {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ omegaL lam) : 1-(spectralProduct lam z)⁻¹^2 ≠ 0 := by
  intro he
  have hh : (spectralProduct lam z)⁻¹^2 = 1 := (sub_eq_zero.mp he).symm
  rw [ inv_pow, inv_eq_one] at hh
  exact omegaL_product_sq_ne_one hlam hz hh

theorem exists_low_analytic_fourth_root {lam : ℝ} (hlam : 0 < lam) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (omegaL lam) ∧
      ∀ z ∈ omegaL lam, g z^4 = 1-(spectralProduct lam z)⁻¹^2 :=
  exists_analytic_fourth_root (omegaL_isSimplyConnected hlam) (omegaL_isOpen hlam)
    (lowRadicand_analytic hlam) (fun _ hz => lowRadicand_ne_zero hlam hz)

def lowRealRadicand (lam x : ℝ) : ℝ :=
  1-(Real.sinh x * Real.sinh (lam*x))⁻¹^2

theorem lowRadicand_real (lam x : ℝ) :
    1-(spectralProduct lam (x:ℂ))⁻¹^2 = (lowRealRadicand lam x:ℂ) := by
  simp [spectralProduct,spectralS,spectralT,lowRealRadicand]

theorem lowRealRadicand_pos {lam x : ℝ} (hlam : 0<lam) (hx : criticalPoint lam<x) :
    0<lowRealRadicand lam x := by
  have hx0 : 0<x := lt_trans (criticalPoint_pos hlam) hx
  have hp := (criticalPoint_lt_iff_product_gt_one hlam hx0.le).mp hx
  have hi : 0<(Real.sinh x*Real.sinh (lam*x))⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hp)
  have hi1 : (Real.sinh x*Real.sinh (lam*x))⁻¹<1 := (inv_lt_one₀ (lt_trans zero_lt_one hp)).mpr hp
  unfold lowRealRadicand
  nlinarith

theorem lowRealRadicand_continuousOn {lam : ℝ} (hlam : 0<lam) :
    ContinuousOn (lowRealRadicand lam) (Ioi (criticalPoint lam)) := by
  apply continuousOn_const.sub
  apply ContinuousOn.pow
  apply ContinuousOn.inv₀
  · exact (Real.continuous_sinh.mul (Real.continuous_sinh.comp
      (continuous_const.mul continuous_id))).continuousOn
  · intro x hx
    have hx0 := lt_trans (criticalPoint_pos hlam) hx
    exact ne_of_gt (lt_trans zero_lt_one ((criticalPoint_lt_iff_product_gt_one hlam hx0.le).mp hx))

theorem exists_lowBranch {lam : ℝ} (hlam : 0<lam) :
    ∃ f, FormFactors.LowBranch lam f := by
  let x₀ := criticalPoint lam + 1
  have hx₀ : criticalPoint lam < x₀ := by dsimp [x₀]; linarith
  let q : ℝ → ℂ := fun x => (positiveFourthRoot (lowRealRadicand lam x):ℂ)
  have hqpow : ∀ x∈Ioi (criticalPoint lam), q x^4 = (lowRealRadicand lam x:ℂ) := by
    intro x hx
    dsimp [q]
    exact_mod_cast positiveFourthRoot_pow_four (lowRealRadicand_pos hlam hx).le
  have hqne : ∀ x∈Ioi (criticalPoint lam), q x≠0 := by
    intro x hx
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (positiveFourthRoot_pos (lowRealRadicand_pos hlam hx)))
  have hqc : ContinuousOn q (Ioi (criticalPoint lam)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (positiveFourthRoot_continuous.comp_continuousOn (lowRealRadicand_continuousOn hlam))
  obtain ⟨g,hg,hgp,hg0⟩ := exists_analytic_fourth_root_with_value
    (omegaL_isSimplyConnected hlam) (omegaL_isOpen hlam)
    (lowRadicand_analytic hlam) (fun _ hz => lowRadicand_ne_zero hlam hz)
    ((real_mem_omegaL_iff hlam x₀).mpr hx₀)
    ((hqpow x₀ hx₀).trans (lowRadicand_real lam x₀).symm)
  have hgeq : EqOn (fun x : ℝ => g (x:ℂ)) q (Ioi (criticalPoint lam)) := by
    apply continuous_fourth_roots_eqOn isPreconnected_Ioi
      (hg.continuousOn.comp Complex.continuous_ofReal.continuousOn
        (fun x hx => (real_mem_omegaL_iff hlam x).mpr hx)) hqc hqne
    · intro x hx
      exact (hgp (x:ℂ) ((real_mem_omegaL_iff hlam x).mpr hx)).trans
        ((lowRadicand_real lam x).trans (hqpow x hx).symm)
    · exact hx₀
    · exact hg0
  refine ⟨g,hg,hgp,?_⟩
  intro x hx hp
  have hxc := (criticalPoint_lt_iff_product_gt_one hlam hx.le).mpr hp
  have heq : g (x:ℂ) = q x := hgeq hxc
  rw [heq]
  exact ⟨Complex.ofReal_im _, positiveFourthRoot_pos (lowRealRadicand_pos hlam hxc)⟩

theorem lowPrefactor_actual_spec {lam : ℝ} (hlam : 0<lam) :
    FormFactors.LowBranch lam (FormFactors.lowPrefactor lam) :=
  FormFactors.lowPrefactor_spec (exists_lowBranch hlam)

theorem positive_real_fourth_roots_eq {a b : ℂ}
    (ha : a.im=0 ∧ 0<a.re) (hb : b.im=0 ∧ 0<b.re) (hp : a^4=b^4) : a=b := by
  have hae : a=(a.re:ℂ) := by apply Complex.ext <;> simp [ha.1]
  have hbe : b=(b.re:ℂ) := by apply Complex.ext <;> simp [hb.1]
  rw [hae,hbe] at hp ⊢
  have hr : a.re^4=b.re^4 := by exact_mod_cast hp
  exact congrArg Complex.ofReal ((pow_left_inj₀ ha.2.le hb.2.le (by decide : 4≠0)).mp hr)

theorem lowBranch_unique {lam : ℝ} (hlam : 0<lam) {f g : ℂ → ℂ}
    (hf : FormFactors.LowBranch lam f) (hg : FormFactors.LowBranch lam g) :
    EqOn f g (omegaL lam) := by
  let x := criticalPoint lam+1
  have hxc : criticalPoint lam<x := by dsimp [x]; linarith
  have hx0 : 0<x := lt_trans (criticalPoint_pos hlam) hxc
  have hxp := (criticalPoint_lt_iff_product_gt_one hlam hx0.le).mp hxc
  have hx : (x:ℂ)∈omegaL lam := (real_mem_omegaL_iff hlam x).mpr hxc
  have hfpos := hf.2.2 x hx0 hxp
  have hgpos := hg.2.2 x hx0 hxp
  have hp : ∀ z∈omegaL lam, f z^4=g z^4 :=
    fun z hz => (hf.2.1 z hz).trans (hg.2.1 z hz).symm
  apply analytic_fourth_roots_eqOn (omegaL_isOpen hlam)
    (omegaL_isSimplyConnected hlam).isPathConnected.isConnected.isPreconnected
    hf.1 hg.1 hp hx (positive_real_fourth_roots_eq hfpos hgpos (hp _ hx))
  intro he
  simp [he] at hfpos

end
end IsingBulk.Anisotropic
