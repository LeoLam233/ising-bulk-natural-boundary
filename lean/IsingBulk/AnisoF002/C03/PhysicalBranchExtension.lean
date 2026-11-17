import IsingBulk.AnisoF002.C03.PhysicalPrefactors
import IsingBulk.AnisoF002.C03.GlobalTransfer

/-!
# Nonzero analytic prefactor extensions across actual regular boundaries

A continuous fourth root is continued across a nonzero analytic radicand
using a connected overlap in an actual local graph chart.  This explicitly
matches the selected physical branch; choosing an unrelated local root would
not suffice for susceptibility nonextension transfer.
-/

namespace IsingBulk.AnisoF002.Physical
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open Geometry Set Filter
open scoped Topology

theorem fourthRoot_local_extension_of_flattening {D : Set ℂ} {f r : ℂ → ℂ} {z : ℂ}
    (hf : ContinuousOn f D) (hp : ∀ w ∈ D, f w ^ 4 = r w)
    (hr : AnalyticAt ℂ r z) (hr0 : r z ≠ 0) (hz : z ∈ closure D)
    (e : ℂ ≃ₜ ℂ) {S : Set ℂ} (hS : Convex ℝ S)
    (hD : ∀ᶠ w in 𝓝 z, w ∈ D ↔ e w ∈ S) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, w ∈ D → g w = f w := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (hr.eventually_analyticAt.and (hr.continuousAt.eventually_ne hr0))
  have hlocal : ∀ᶠ v in 𝓝 (e z),
      e.symm v ∈ Metric.ball z ε ∧ (e.symm v ∈ D ↔ v ∈ S) := by
    have hb : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball z ε := Metric.ball_mem_nhds z hε
    have hes : Tendsto e.symm (𝓝 (e z)) (𝓝 z) := by
      simpa only [ContinuousAt, e.symm_apply_apply] using
        (e.symm.continuous.continuousAt (x := e z))
    have hh := hes.eventually (hb.and hD)
    simpa only [e.apply_symm_apply] using hh
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hlocal
  let U : Set ℂ := e ⁻¹' Metric.ball (e z) δ
  have hU : IsOpen U := Metric.isOpen_ball.preimage e.continuous
  have hzU : z ∈ U := Metric.mem_ball_self hδ
  have hUb : U ⊆ Metric.ball z ε := by
    intro w hw
    simpa only [e.symm_apply_apply] using (hδsub hw).1
  have hUD : U ∩ D = e ⁻¹' (Metric.ball (e z) δ ∩ S) := by
    ext w
    constructor
    · rintro ⟨hw, hd⟩
      exact ⟨hw, ((hδsub hw).2).mp (by simpa only [e.symm_apply_apply] using hd)⟩
    · rintro ⟨hw, hs⟩
      exact ⟨hw, by simpa only [e.symm_apply_apply] using ((hδsub hw).2).mpr hs⟩
  have hUDc : IsPreconnected (U ∩ D) := by
    rw [hUD, e.isPreconnected_preimage]
    exact ((convex_ball (e z) δ).inter hS).isPreconnected
  obtain ⟨w₀, hw₀U, hw₀D⟩ := mem_closure_iff.mp hz U hU hzU
  have hball : IsSimplyConnected (Metric.ball z ε) := by
    change SimplyConnectedSpace _
    exact @SimplyConnectedSpace.ofContractible _ _
      ((convex_ball z ε).contractibleSpace ⟨z, Metric.mem_ball_self hε⟩)
  obtain ⟨g, hg, hgp, hg₀⟩ := exists_analytic_fourth_root_at hball Metric.isOpen_ball
    (fun _ hw => (hεsub hw).1) (fun _ hw => (hεsub hw).2)
    (hUb hw₀U) (hp w₀ hw₀D)
  have hgn : ∀ w ∈ Metric.ball z ε, g w ≠ 0 := by
    intro w hw he
    have hh := hgp w hw
    rw [he, zero_pow (by decide : (4 : ℕ) ≠ 0)] at hh
    exact (hεsub hw).2 hh.symm
  have heq : EqOn f g (U ∩ D) := by
    apply continuousFourthRoots_unique hUDc (hf.mono inter_subset_right)
      (hg.continuousOn.mono (inter_subset_left.trans hUb))
      (fun _ hw => hgn _ (hUb hw.1))
    · intro w hw
      exact (hp w hw.2).trans (hgp w (hUb hw.1)).symm
    · exact ⟨hw₀U, hw₀D⟩
    · exact hg₀.symm
  refine ⟨g, hg z (Metric.mem_ball_self hε), hgn z (Metric.mem_ball_self hε), ?_⟩
  filter_upwards [hU.mem_nhds hzU] with w hw hd
  exact (heq ⟨hw, hd⟩).symm

theorem local_nonzero_extension_hasDomainExtension {D : Set ℂ} {f g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (he : ∀ᶠ w in 𝓝 z, w ∈ D → g w = f w) :
    HasDomainExtension D f z := by
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp (hg.eventually_analyticAt.and he)
  exact ⟨U, hUopen, hzU, g, fun _ hw => (hUsub hw).1,
    fun _ hw => (hUsub hw.1).2 hw.2⟩

/-- A global shear associated with any continuous real graph. -/
def graphShear (p : ℝ → ℝ) (hp : Continuous p) : ℂ ≃ₜ ℂ where
  toFun z := z - (p z.im : ℂ)
  invFun z := z + (p z.im : ℂ)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_id.sub (Complex.continuous_ofReal.comp
    (hp.comp Complex.continuous_im))
  continuous_invFun := continuous_id.add (Complex.continuous_ofReal.comp
    (hp.comp Complex.continuous_im))

theorem lowPrefactor_local_nonzero_extension {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaL lam)) (hp0 : spectralProduct lam z ≠ 0)
    (hp1 : spectralProduct lam z ^ 2 ≠ 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, w ∈ omegaL lam → g w = lowPrefactor lam w := by
  have hr : AnalyticAt ℂ (fun w => 1 - (spectralProduct lam w)⁻¹ ^ 2) z :=
    analyticAt_const.sub (((spectralProduct_analytic lam z).inv hp0).pow 2)
  have hr0 : 1 - (spectralProduct lam z)⁻¹ ^ 2 ≠ 0 := by
    intro he
    have hh := (sub_eq_zero.mp he).symm
    rw [inv_pow, inv_eq_one] at hh
    exact hp1 hh
  apply fourthRoot_local_extension_of_flattening
    (lowPrefactor_spec hlam).1.continuousOn (lowPrefactor_spec hlam).2.1
    hr hr0 hz.1 (lowShearF002 hlam)
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap)
  filter_upwards [] with w
  change lowProfileF002 lam w.im < w.re ↔
    0 < (w - (lowProfileF002 lam w.im : ℂ)).re
  simp only [Complex.sub_re, Complex.ofReal_re, sub_pos]

theorem high_frontier_nonzero_re_strip {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaH lam)) (hx : z.re ≠ 0) :
    |z.im| < highStripWidthF002 lam := by
  have hz' : |z.im| ≤ highStripWidthF002 lam ∧
      |z.re| = highProfileF002 lam z.im := by
    have hh : z ∈ frontier (omegaHF002 lam) := hz
    simpa only [frontier_omegaHF002 hlam, Set.mem_ofPred_eq] using hh
  rcases lt_or_eq_of_le hz'.1 with hlt | heq
  · exact hlt
  · have htip := highProfile_tip_zero hlam heq
    exact False.elim (hx (abs_eq_zero.mp (hz'.2.trans htip)))

theorem highPrefactor_local_nonzero_extension {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaH lam)) (hx : z.re ≠ 0)
    (hp1 : spectralProduct lam z ^ 2 ≠ 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, w ∈ omegaH lam → g w = highPrefactor lam w := by
  have hr := highRadicand_analytic lam z (mem_univ z)
  have hr0 : 1 - spectralProduct lam z ^ 2 ≠ 0 := by
    intro he
    exact hp1 (sub_eq_zero.mp he).symm
  have hy := high_frontier_nonzero_re_strip hlam hz hx
  have hstrip : ∀ᶠ w in 𝓝 z, |w.im| < highStripWidthF002 lam :=
    (Complex.continuous_im.abs.continuousAt).eventually (Iio_mem_nhds hy)
  rcases lt_or_gt_of_ne hx with hx | hx
  · apply fourthRoot_local_extension_of_flattening
      (highPrefactor_spec hlam).1.continuousOn (highPrefactor_spec hlam).2.1
      hr hr0 hz.1 (graphShear (fun y => -highProfileF002 lam y)
        (highProfile_continuous hlam).neg)
      ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap)
    have hsign : ∀ᶠ w in 𝓝 z, w.re < 0 :=
      Complex.continuous_re.continuousAt.eventually (Iio_mem_nhds hx)
    filter_upwards [hstrip, hsign] with w hw hs
    change (|w.im| < highStripWidthF002 lam ∧ |w.re| < highProfileF002 lam w.im) ↔
      0 < (w - ((-highProfileF002 lam w.im : ℝ) : ℂ)).re
    simp only [hw, true_and, abs_of_neg hs, Complex.sub_re, Complex.ofReal_re]
    constructor <;> intro h <;> linarith
  · apply fourthRoot_local_extension_of_flattening
      (highPrefactor_spec hlam).1.continuousOn (highPrefactor_spec hlam).2.1
      hr hr0 hz.1 (graphShear (highProfileF002 lam) (highProfile_continuous hlam))
      ((convex_Iio (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap)
    have hsign : ∀ᶠ w in 𝓝 z, 0 < w.re :=
      Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds hx)
    filter_upwards [hstrip, hsign] with w hw hs
    change (|w.im| < highStripWidthF002 lam ∧ |w.re| < highProfileF002 lam w.im) ↔
      (w - (highProfileF002 lam w.im : ℂ)).re < 0
    simp only [hw, true_and, abs_of_pos hs, Complex.sub_re, Complex.ofReal_re, sub_neg]

end
end IsingBulk.AnisoF002.Physical
