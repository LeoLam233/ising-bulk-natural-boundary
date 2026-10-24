import IsingBulk.Anisotropic.FormFactors.NormalConvergence
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem analyticAt_iteratedDeriv_complex {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (j : ℕ) : AnalyticAt ℂ (iteratedDeriv j f) z := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem hasSum_iteratedDeriv_of_summable_envelope {f : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) U)
    {C : ℕ → ℝ} (hC : Summable C) (hb : ∀ n z, z∈U → ‖f n z‖≤C n)
    (j : ℕ) {z : ℂ} (hz : z∈U) :
    HasSum (fun n => iteratedDeriv j (f n) z) (iteratedDeriv j (fun w => ∑' n, f n w) z) := by
  have ha (I : Finset ℕ) (w : ℂ) (hw : w∈U) : AnalyticAt ℂ (fun v => ∑ n∈I, f n v) w :=
    I.analyticAt_fun_sum (fun n _ => hf n w hw)
  have hlim : ∀ k : ℕ, TendstoLocallyUniformlyOn
      (fun I : Finset ℕ => iteratedDeriv k (fun w => ∑ n∈I, f n w))
      (iteratedDeriv k (fun w => ∑' n, f n w)) atTop U := by
    intro k
    induction k with
    | zero => exact (tendstoUniformlyOn_tsum hC hb).tendstoLocallyUniformlyOn
    | succ k ih =>
      have hd : ∀ᶠ I : Finset ℕ in atTop,
          DifferentiableOn ℂ (iteratedDeriv k (fun w => ∑ n∈I, f n w)) U :=
        Filter.Eventually.of_forall (fun I w hw =>
          (analyticAt_iteratedDeriv_complex (ha I w hw) k).differentiableAt.differentiableWithinAt)
      simpa only [iteratedDeriv_succ,Function.comp_def] using ih.deriv hd hU
  change Tendsto (fun I : Finset ℕ => ∑ n∈I, iteratedDeriv j (f n) z)
    atTop (𝓝 (iteratedDeriv j (fun w => ∑' n, f n w) z))
  convert (hlim j).tendsto_at hz using 1
  funext I
  exact (iteratedDeriv_fun_sum (fun n _ => (hf n z hz).contDiffAt)).symm

end
end IsingBulk.Anisotropic.FormFactors
