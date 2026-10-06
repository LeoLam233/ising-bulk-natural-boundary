import IsingBulk.Final.InverseTemperatureLocalBranches
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Local inverse-sinh sheet rigidity. Every sheet is handled, without assuming
that unrelated canonical half-plane branches are one global continuation. -/
namespace IsingBulk.Final
noncomputable section
open Complex Set Filter
open scoped Topology

theorem sinh_inverse_derivative {U : Set ℂ} (hU : IsOpen U) (b : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ b U) (hrel : ∀ s∈U, Complex.sinh (b s)=s)
    {s : ℂ} (hs : s∈U) : Complex.cosh (b s)*deriv b s=1 := by
  have he : (fun t => Complex.sinh (b t)) =ᶠ[𝓝 s] (fun t => t) := by
    filter_upwards [hU.mem_nhds hs] with t ht
    exact hrel t ht
  exact ((Complex.hasDerivAt_sinh (b s)).comp s (hb s hs).differentiableAt.hasDerivAt).unique
    ((hasDerivAt_id s).congr_of_eventuallyEq he)

theorem sinh_inverse_cosh_nonzero {U : Set ℂ} (hU : IsOpen U) (b : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ b U) (hrel : ∀ s∈U, Complex.sinh (b s)=s)
    {s : ℂ} (hs : s∈U) : Complex.cosh (b s) ≠ 0 := by
  have h := sinh_inverse_derivative hU b hb hrel hs
  intro hz
  rw [hz,zero_mul] at h
  exact zero_ne_one h

theorem sinh_inverse_cosh_sheet {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (b b0 : ℂ → ℂ) (hb : AnalyticOnNhd ℂ b U) (hb0 : AnalyticOnNhd ℂ b0 U)
    (hrel : ∀ s∈U, Complex.sinh (b s)=s) (hrel0 : ∀ s∈U, Complex.sinh (b0 s)=s)
    {s0 σ : ℂ} (hs0 : s0∈U) (hσ : σ=1 ∨ σ= -1)
    (hseed : Complex.cosh (b s0)=σ*Complex.cosh (b0 s0)) :
    ∀ s∈U, Complex.cosh (b s)=σ*Complex.cosh (b0 s) := by
  have hf : AnalyticOnNhd ℂ (fun s => Complex.cosh (b s)) U := by
    intro s hs
    exact (Complex.differentiable_cosh.analyticAt _).comp (hb s hs)
  have hg : AnalyticOnNhd ℂ (fun s => σ*Complex.cosh (b0 s)) U := by
    intro s hs
    exact analyticAt_const.mul ((Complex.differentiable_cosh.analyticAt _).comp (hb0 s hs))
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl|rfl <;> norm_num
  have hσsq : σ^2=1 := by rcases hσ with rfl|rfl <;> norm_num
  have hc0 := sinh_inverse_cosh_nonzero hU b0 hb0 hrel0 hs0
  have hsum : Complex.cosh (b s0)+σ*Complex.cosh (b0 s0) ≠ 0 := by
    rw [hseed,← two_mul]
    exact mul_ne_zero (by norm_num) (mul_ne_zero hσ0 hc0)
  have he : (fun s => Complex.cosh (b s)) =ᶠ[𝓝 s0] (fun s => σ*Complex.cosh (b0 s)) := by
    filter_upwards [hU.mem_nhds hs0,
      ((hf s0 hs0).add (hg s0 hs0)).continuousAt.eventually_ne hsum] with s hs hn
    have hsq : Complex.cosh (b s)^2=(σ*Complex.cosh (b0 s))^2 := by
      rw [mul_pow,hσsq,one_mul,Complex.cosh_sq,Complex.cosh_sq,hrel s hs,hrel0 s hs]
    have hp : (Complex.cosh (b s)-σ*Complex.cosh (b0 s))*
        (Complex.cosh (b s)+σ*Complex.cosh (b0 s))=0 := by
      linear_combination hsq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hn)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn hs0 he

theorem sinh_inverse_sheet_affine {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (b b0 : ℂ → ℂ) (hb : AnalyticOnNhd ℂ b U) (hb0 : AnalyticOnNhd ℂ b0 U)
    (hrel : ∀ s∈U, Complex.sinh (b s)=s) (hrel0 : ∀ s∈U, Complex.sinh (b0 s)=s)
    {s0 : ℂ} (hs0 : s0∈U) :
    ∃ σ : ℂ, (σ=1 ∨ σ= -1) ∧
      EqOn b (fun s => σ*b0 s+(b s0-σ*b0 s0)) U := by
  have hsq : Complex.cosh (b s0)^2=Complex.cosh (b0 s0)^2 := by
    rw [Complex.cosh_sq,Complex.cosh_sq,hrel s0 hs0,hrel0 s0 hs0]
  have hchoice : ∃ σ : ℂ, (σ=1 ∨ σ= -1) ∧
      Complex.cosh (b s0)=σ*Complex.cosh (b0 s0) := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h|h
    · exact ⟨1,Or.inl rfl,by simpa using h⟩
    · exact ⟨-1,Or.inr rfl,by simpa using h⟩
  obtain ⟨σ,hσ,hseed⟩ := hchoice
  have hcosh := sinh_inverse_cosh_sheet hU hconn b b0 hb hb0 hrel hrel0 hs0 hσ hseed
  have hσsq : σ^2=1 := by rcases hσ with rfl|rfl <;> norm_num
  let g := fun s => σ*b0 s+(b s0-σ*b0 s0)
  have hg : AnalyticOnNhd ℂ g U := by
    intro s hs
    exact (analyticAt_const.mul (hb0 s hs)).add analyticAt_const
  refine ⟨σ,hσ,?_⟩
  apply hU.eqOn_of_deriv_eq hconn hb.differentiableOn hg.differentiableOn _ hs0
    (by dsimp [g]; ring)
  intro s hs
  have hd := sinh_inverse_derivative hU b hb hrel hs
  have hd0 := sinh_inverse_derivative hU b0 hb0 hrel0 hs
  have hc0 := sinh_inverse_cosh_nonzero hU b0 hb0 hrel0 hs
  rw [hcosh s hs] at hd
  have he : Complex.cosh (b0 s)*(deriv b s-σ*deriv b0 s)=0 := by
    linear_combination σ*hd-σ*hd0-(Complex.cosh (b0 s)*deriv b s)*hσsq
  have hderiv : deriv b s=σ*deriv b0 s := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hc0)
  have hgd := (((hb0 s hs).differentiableAt.hasDerivAt.const_mul σ).add_const (b s0-σ*b0 s0)).deriv
  exact hderiv.trans hgd.symm

/-- Every inverse-sinh sheet on U extends across a larger canonical-branch
region V. The extension's genuine relation on V is proved by analytic identity. -/
theorem sinh_inverse_sheet_extension {U V : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (hne : U.Nonempty) (hUV : U ⊆ V)
    (hVconn : IsPreconnected V) (b b0 : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ b U) (hb0 : AnalyticOnNhd ℂ b0 V)
    (hrel : ∀ s∈U, Complex.sinh (b s)=s) (hrel0 : ∀ s∈V, Complex.sinh (b0 s)=s) :
    ∃ bExt : ℂ → ℂ, AnalyticOnNhd ℂ bExt V ∧ EqOn bExt b U ∧
      ∀ s∈V, Complex.sinh (bExt s)=s := by
  obtain ⟨s0,hs0⟩ := hne
  obtain ⟨σ,hσ,heq⟩ := sinh_inverse_sheet_affine hU hconn b b0 hb (hb0.mono hUV)
    hrel (fun s hs => hrel0 s (hUV hs)) hs0
  let g := fun s => σ*b0 s+(b s0-σ*b0 s0)
  have hg : AnalyticOnNhd ℂ g V := by
    intro s hs
    exact (analyticAt_const.mul (hb0 s hs)).add analyticAt_const
  have hEq : EqOn g b U := heq.symm
  refine ⟨g,hg,hEq,?_⟩
  have hgsinh : AnalyticOnNhd ℂ (fun s => Complex.sinh (g s)) V := by
    intro s hs
    exact (Complex.differentiable_sinh.analyticAt _).comp (hg s hs)
  have he : (fun s => Complex.sinh (g s)) =ᶠ[𝓝 s0] (fun s => s) := by
    filter_upwards [hU.mem_nhds hs0] with s hs
    rw [hEq hs]
    exact hrel s hs
  exact hgsinh.eqOn_of_preconnected_of_eventuallyEq
    (fun _ _ => analyticAt_id) hVconn (hUV hs0) he

/-- Scaled physical-temperature version. U and V are actual open/connected
source domains supplied by geometry, not assumed extension conclusions. -/
theorem inverseTemperature_sheet_extension {U V : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (hne : U.Nonempty) (hUV : U ⊆ V)
    (hVconn : IsPreconnected V) {J : ℝ} (hJ : 0 < J) (beta beta0 : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ beta U) (hb0 : AnalyticOnNhd ℂ beta0 V)
    (hrel : ∀ s∈U, Complex.sinh (2*(J:ℂ)*beta s)=s)
    (hrel0 : ∀ s∈V, Complex.sinh (2*(J:ℂ)*beta0 s)=s) :
    ∃ betaExt : ℂ → ℂ, AnalyticOnNhd ℂ betaExt V ∧ EqOn betaExt beta U ∧
      (∀ s∈V, Complex.sinh (2*(J:ℂ)*betaExt s)=s) ∧
      (∀ s∈V, s ≠ 0 → betaExt s ≠ 0) := by
  have hj0 : 2*(J:ℂ) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hJ.ne')
  have hba : AnalyticOnNhd ℂ (fun s => 2*(J:ℂ)*beta s) U := by
    intro s hs
    exact analyticAt_const.mul (hb s hs)
  have hba0 : AnalyticOnNhd ℂ (fun s => 2*(J:ℂ)*beta0 s) V := by
    intro s hs
    exact analyticAt_const.mul (hb0 s hs)
  obtain ⟨g,hg,heq,hgrel⟩ := sinh_inverse_sheet_extension hU hconn hne hUV hVconn
    (fun s => 2*(J:ℂ)*beta s) (fun s => 2*(J:ℂ)*beta0 s) hba hba0 hrel hrel0
  let betaExt := fun s => g s/(2*(J:ℂ))
  have hExt : AnalyticOnNhd ℂ betaExt V := by
    intro s hs
    exact (hg s hs).div analyticAt_const hj0
  have hEq : EqOn betaExt beta U := by
    intro s hs
    dsimp [betaExt]
    rw [heq hs]
    field_simp [Complex.ofReal_ne_zero.mpr hJ.ne']
  have hRel : ∀ s∈V, Complex.sinh (2*(J:ℂ)*betaExt s)=s := by
    intro s hs
    dsimp [betaExt]
    rw [mul_div_cancel₀ _ hj0]
    exact hgrel s hs
  exact ⟨betaExt,hExt,hEq,hRel,fun s hs hs0 => inverseTemperature_nonzero_of_relation hs0 (hRel s hs)⟩

end
end IsingBulk.Final
