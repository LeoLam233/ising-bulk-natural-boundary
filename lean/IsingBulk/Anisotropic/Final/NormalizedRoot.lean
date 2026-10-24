import IsingBulk.Anisotropic.Final.ContinuousBranch
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic

namespace IsingBulk.Anisotropic
noncomputable section
open Set Filter
open scoped Topology

theorem exists_normalized_analytic_fourth_root {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hU : IsOpen U) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hn : ∀ z ∈ U, f z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hf₀ : f z₀ = 1) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, g z ^ 4 = f z) ∧ g z₀ = 1 := by
  obtain ⟨g,hg,hpow⟩ := exists_analytic_fourth_root hUc hU hf hn
  have hbase : g z₀ ^ 4 = 1 := (hpow z₀ hz₀).trans hf₀
  have hg0 : g z₀ ≠ 0 := by intro h; simp [h] at hbase
  refine ⟨fun z => g z / g z₀,fun z hz => (hg z hz).div_const,?_,div_self hg0⟩
  intro z hz
  rw [div_pow,hpow z hz,hbase,div_one]

/-- Local uniqueness follows from the inverse theorem for w↦w^4 at a nonzero
root; hence equality at one point fixes the root on a connected domain. -/
theorem analytic_fourth_roots_eqOn {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hpow : ∀ z ∈ U, f z ^ 4 = g z ^ 4)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hbase : f z₀ = g z₀) (hn : f z₀ ≠ 0) :
    EqOn f g U := by
  have hd : deriv (fun w : ℂ => w^4) (f z₀) ≠ 0 := by
    rw [(hasDerivAt_pow 4 (f z₀)).deriv]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hn)
  obtain ⟨ψ,_,_,_,hleft⟩ := exists_analytic_local_inverse (analyticAt_id.pow 4) hd
  have hfl : ∀ᶠ z in 𝓝 z₀, ψ (f z ^ 4) = f z :=
    (hf z₀ hz₀).continuousAt.eventually hleft
  have hgl : ∀ᶠ z in 𝓝 z₀, ψ (g z ^ 4) = g z := by
    have hc : Tendsto g (𝓝 z₀) (𝓝 (f z₀)) := by
      simpa only [hbase] using (hg z₀ hz₀).continuousAt.tendsto
    exact hc.eventually hleft
  have heq : f =ᶠ[𝓝 z₀] g := by
    filter_upwards [hfl,hgl,hU.mem_nhds hz₀] with z h1 h2 hz
    rw [← h1,← h2,hpow z hz]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn hz₀ heq

theorem exists_analytic_fourth_root_with_value {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hU : IsOpen U) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hn : ∀ z ∈ U, f z ≠ 0) {z₀ c : ℂ} (hz₀ : z₀ ∈ U) (hc : c^4=f z₀) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, g z^4=f z) ∧ g z₀=c := by
  obtain ⟨g,hg,hpow⟩ := exists_analytic_fourth_root hUc hU hf hn
  have hg0 : g z₀ ≠ 0 := by
    intro he
    have hh := hpow z₀ hz₀
    rw [he,zero_pow (by decide : 4≠0)] at hh
    exact hn z₀ hz₀ hh.symm
  refine ⟨fun z => g z*c/g z₀,fun z hz => ((hg z hz).mul analyticAt_const).div_const,?_,?_⟩
  · intro z hz
    rw [div_pow,mul_pow,hpow z hz,hpow z₀ hz₀,hc]
    exact mul_div_cancel_right₀ _ (hn z₀ hz₀)
  · exact mul_div_cancel_left₀ c hg0

end
end IsingBulk.Anisotropic
