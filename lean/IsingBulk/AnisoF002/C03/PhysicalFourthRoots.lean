import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic

/-!
# F002 construction and normalization of analytic fourth roots

Only generic Mathlib covering-space and inverse-function theorems are used.
Continuous covering lifts are upgraded to analytic functions by the local
inverse of the fourth-power map, and the physical branch is fixed by one
actual value.  No historical ANISO branch theorem is invoked.
-/

namespace IsingBulk.AnisoF002.Physical
noncomputable section
open Set Filter
open scoped Topology

theorem continuousBranch_analyticAt {f g : ℂ → ℂ} {z : ℂ}
    (hg : ContinuousAt g z) (hf : AnalyticAt ℂ f (g z))
    (hd : deriv f (g z) ≠ 0) (hc : AnalyticAt ℂ (f ∘ g) z) :
    AnalyticAt ℂ g z := by
  let ψ := hf.hasStrictDerivAt.localInverse f (deriv f (g z)) (g z) hd
  have hψ : AnalyticAt ℂ ψ (f (g z)) := hf.analyticAt_localInverse hd
  have hl : ∀ᶠ w in 𝓝 (g z), ψ (f w) = w :=
    hf.hasStrictDerivAt.eventually_left_inverse hd
  exact (hψ.comp (f := f ∘ g) hc).congr (hg.eventually hl)

theorem continuousFourthRoot_analytic {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : ContinuousOn g U)
    (hp : ∀ z ∈ U, g z ^ 4 = f z) (hn : ∀ z ∈ U, f z ≠ 0) :
    AnalyticOnNhd ℂ g U := by
  intro z hz
  have hg0 : g z ≠ 0 := by
    intro he
    have heq := hp z hz
    rw [he, zero_pow (by decide : (4 : ℕ) ≠ 0)] at heq
    exact hn z hz heq.symm
  have hd : deriv (fun w : ℂ => w ^ 4) (g z) ≠ 0 := by
    rw [(hasDerivAt_pow 4 (g z)).deriv]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hg0)
  apply continuousBranch_analyticAt (hg.continuousAt (hU.mem_nhds hz))
    (analyticAt_id.pow 4) hd
  apply (hf z hz).congr
  filter_upwards [hU.mem_nhds hz] with w hw
  exact (hp w hw).symm

theorem exists_analytic_fourth_root {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hU : IsOpen U) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hn : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ ∀ z ∈ U, g z ^ 4 = f z := by
  have hnimage : 0 ∉ f '' U := by
    rintro ⟨z, hz, he⟩
    exact hn z hz he
  obtain ⟨g, hg, hp⟩ := Complex.exists_continuousOn_pow_eq hUc hU hf.continuousOn
    hnimage (by decide : (4 : ℕ) ≠ 0)
  exact ⟨g, continuousFourthRoot_analytic hU hf hg (fun z _ => hp z) hn,
    fun z _ => hp z⟩

theorem exists_analytic_fourth_root_at {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hU : IsOpen U) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hn : ∀ z ∈ U, f z ≠ 0) {z₀ c : ℂ} (hz₀ : z₀ ∈ U) (hc : c ^ 4 = f z₀) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, g z ^ 4 = f z) ∧ g z₀ = c := by
  obtain ⟨g, hg, hp⟩ := exists_analytic_fourth_root hUc hU hf hn
  have hg0 : g z₀ ≠ 0 := by
    intro he
    have heq := hp z₀ hz₀
    rw [he, zero_pow (by decide : (4 : ℕ) ≠ 0)] at heq
    exact hn z₀ hz₀ heq.symm
  refine ⟨fun z => g z * c / g z₀,
    fun z hz => ((hg z hz).mul analyticAt_const).div_const, ?_, ?_⟩
  · intro z hz
    rw [div_pow, mul_pow, hp z hz, hp z₀ hz₀, hc]
    exact mul_div_cancel_right₀ _ (hn z₀ hz₀)
  · exact mul_div_cancel_left₀ c hg0

theorem fourthRootsOne_finite : Set.Finite {z : ℂ | z ^ 4 = 1} := by
  have hp : (Polynomial.X ^ 4 - 1 : Polynomial ℂ) ≠ 0 := by
    intro he
    have hv := congrArg (Polynomial.eval (0 : ℂ)) he
    norm_num at hv
  simpa [Polynomial.IsRoot, sub_eq_zero] using Polynomial.finite_setOfPred_isRoot hp

theorem continuousFourthRoots_unique {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsPreconnected U) {f g : X → ℂ} (hf : ContinuousOn f U)
    (hg : ContinuousOn g U) (hn : ∀ x ∈ U, g x ≠ 0)
    (hp : ∀ x ∈ U, f x ^ 4 = g x ^ 4) {x₀ : X} (hx₀ : x₀ ∈ U)
    (hb : f x₀ = g x₀) : EqOn f g U := by
  have hc : ContinuousOn (fun x => f x / g x) U := hf.div hg hn
  have hm : MapsTo (fun x => f x / g x) U {z : ℂ | z ^ 4 = 1} := by
    intro x hx
    change (f x / g x) ^ 4 = 1
    rw [div_pow, hp x hx, div_self (pow_ne_zero _ (hn x hx))]
  intro x hx
  have he := hU.constant_of_mapsTo fourthRootsOne_finite.isDiscrete hc hm hx hx₀
  rw [hb, div_self (hn x₀ hx₀)] at he
  exact (div_eq_one_iff_eq (hn x hx)).mp he

theorem positive_real_fourth_power {r : ℝ} (hr : 0 ≤ r) :
    (r ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = r := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  norm_num

theorem positive_real_fourth_root_unique {a : ℂ} {r : ℝ}
    (ha : a.im = 0 ∧ 0 < a.re) (hr : 0 < r) (hp : a ^ 4 = (r : ℂ)) :
    a = (r ^ (1 / 4 : ℝ) : ℝ) := by
  have hae : a = (a.re : ℂ) := by apply Complex.ext <;> simp [ha.1]
  have he : a.re ^ (4 : ℕ) = (r ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
    rw [positive_real_fourth_power hr.le]
    exact_mod_cast hae ▸ hp
  have heq := (pow_left_inj₀ ha.2.le (Real.rpow_nonneg hr.le _) (by decide : (4 : ℕ) ≠ 0)).mp he
  rw [hae, heq]

end
end IsingBulk.AnisoF002.Physical
