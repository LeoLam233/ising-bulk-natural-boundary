import IsingBulk.Anisotropic.Final.AnalyticInverse
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Analytic.Composition

namespace IsingBulk.Anisotropic
noncomputable section
open Set Filter
open scoped Topology

/-- A continuous branch of an analytic local diffeomorphism is analytic.
This upgrades covering-space branches without assuming the desired regularity. -/
theorem analyticAt_of_analytic_composition {f g : ℂ → ℂ} {z : ℂ}
    (hg : ContinuousAt g z) (hf : AnalyticAt ℂ f (g z))
    (hd : deriv f (g z) ≠ 0) (hc : AnalyticAt ℂ (f ∘ g) z) :
    AnalyticAt ℂ g z := by
  obtain ⟨ψ,hψ,_,_,hl⟩ := exists_analytic_local_inverse hf hd
  have he : ∀ᶠ w in 𝓝 z, ψ (f (g w)) = g w := hg.eventually hl
  exact (hψ.comp (f := f ∘ g) hc).congr he

/-- An actual continuous fourth-root branch of a nonvanishing analytic function
is analytic on its open domain. -/
theorem analyticOnNhd_continuous_fourth_root {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : ContinuousOn g U)
    (hpow : ∀ z ∈ U, g z ^ 4 = f z) (hn : ∀ z ∈ U, f z ≠ 0) :
    AnalyticOnNhd ℂ g U := by
  intro z hz
  have hg0 : g z ≠ 0 := by
    intro h
    have hp := hpow z hz
    simp only [h,zero_pow (by decide : 4 ≠ 0)] at hp
    exact hn z hz hp.symm
  have hd : deriv (fun w : ℂ => w^4) (g z) ≠ 0 := by
    rw [(hasDerivAt_pow 4 (g z)).deriv]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hg0)
  apply analyticAt_of_analytic_composition (hg.continuousAt (hU.mem_nhds hz))
    (analyticAt_id.pow 4) hd
  apply (hf z hz).congr
  filter_upwards [hU.mem_nhds hz] with w hw
  exact (hpow w hw).symm

/-- Existence of a holomorphic fourth root on a simply connected nonzero domain.
Normalization is deliberately separate, to be fixed by the physical real germ. -/
theorem exists_analytic_fourth_root {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hU : IsOpen U) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hn : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ ∀ z ∈ U, g z ^ 4 = f z := by
  have hnimage : 0 ∉ f '' U := by
    rintro ⟨z,hz,he⟩
    exact hn z hz he
  obtain ⟨g,hg,hpow⟩ := Complex.exists_continuousOn_pow_eq hUc hU hf.continuousOn
    hnimage (by decide : (4:ℕ) ≠ 0)
  exact ⟨g,analyticOnNhd_continuous_fourth_root hU hf hg (fun z _ => hpow z) hn,
    fun z _ => hpow z⟩

end
end IsingBulk.Anisotropic
