import IsingBulk.Tail.MixedRegularPullback
import IsingBulk.Tail.MixedKernelTransport

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def mixedDensityNormalization {N : ℕ} (f : SelectorFunctions) (τ lam : ℝ) (background : Fin N → ℝ) : ℂ :=
  (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*(angularJacobian f τ lam background).det

def mixedAnalyticDensityModel {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ)
    (C : ℂ) (F : MixedActiveSpace N → ℂ) (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  C*mixedSimpleKernel f r τ lam t (mixedFreeze (insert q J) background x)*
    mixedRegularPullback J q f r τ lam s background F t x

theorem mixedFrozenDensityModel_eq_analytic {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ) :
    mixedFrozenDensityModel J q f r τ lam s background=
      mixedAnalyticDensityModel J q f r τ lam s background (mixedDensityNormalization f τ lam background)
        (mixedActiveRegularAmplitude J q s (fun i => mixedContourPhase f r τ lam s background i)
          (deformedPoint f r τ lam background)) := by
  funext t x
  simp only [mixedFrozenDensityModel,mixedAnalyticDensityModel,mixedDensityNormalization,
    mixedRegularPullback,mixedSimpleKernel,div_eq_mul_inv,mul_inv_rev]
  ring

theorem mixedAnalyticDensityModel_differentiable {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hΩ : (t,mixedFreeze (insert q J) background x)∈mixedSeparatedDomain J j q f r τ lam)
    (C : ℂ) (F : MixedActiveSpace N → ℂ)
    (hF : DifferentiableAt ℂ F (mixedSourceDisplacement J q f r τ lam s background t x)) :
    DifferentiableAt ℂ (fun z => mixedAnalyticDensityModel J q f r τ lam s background C F z x) t ∧
    DifferentiableAt ℝ (mixedAnalyticDensityModel J q f r τ lam s background C F t) x := by
  have hA := mixedRegularPullback_differentiable J j q f hr τ lam s background t x hp hm hΩ F hF
  have hK := mixedSeparated_kernel_smooth hN J j q f hr τ lam hp hm
  have hKx := (hK.angular_differentiableAt hΩ).comp x
    ((mixedFreeze_contDiff (insert q J) background).differentiable (by simp) x)
  exact ⟨((hK _ hΩ).2.const_mul C).mul hA.1,(hKx.const_mul C).mul hA.2⟩

/-- Attach the literal two simple kernels and the fixed normalization to a
regular-density step. No derivative of either global kernel is discarded. -/
theorem mixed_density_kernel_attach {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j∈J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (background : Fin (n+1) → ℝ) (t : ℂ) (x : Fin (n+1) → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ i∈insert q J,deriv f.p (mixedFreeze (insert q J) background x i)=0 ∧
      deriv f.m (mixedFreeze (insert q J) background x i)=0)
    (hΩ : (t,mixedFreeze (insert q J) background x)∈mixedSeparatedDomain J j q f r τ lam)
    (C : ℂ) (F G : MixedActiveSpace (n+1) → ℂ)
    (hF : DifferentiableAt ℂ F (mixedSourceDisplacement J q f r τ lam s background t x))
    (hstep : IsingBulk.Lie.lieStep
      (fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) background a))
      (mixedRegularPullback J q f r τ lam s background F) t x=
      mixedRegularPullback J q f r τ lam s background G t x) :
    IsingBulk.Lie.lieStep
      (fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) background a))
      (mixedAnalyticDensityModel J q f r τ lam s background C F) t x=
      mixedAnalyticDensityModel J q f r τ lam s background C G t x := by
  let V := fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) background a)
  let K := fun z a => mixedSimpleKernel f r τ lam z (mixedFreeze (insert q J) background a)
  have hfz := (mixedFreeze_contDiff (insert q J) background).differentiable (by simp) x
  have hK := mixedSeparated_kernel_smooth (Nat.succ_pos n) J j q f hr τ lam hp hm
  have hKs : DifferentiableAt ℂ (fun z => K z x) t := (hK _ hΩ).2
  have hKx : DifferentiableAt ℝ (K t) x := by
    have hh := (hK.angular_differentiableAt hΩ).comp x hfz
    exact hh
  have hV (i : Fin (n+1)) : DifferentiableAt ℝ (fun a => V t a i) x := by
    have hh := (mixedSeparated_velocity_smooth J j q f hr τ lam hp hm i).angular_differentiableAt hΩ |>.comp x hfz
    exact hh
  have hA := mixedRegularPullback_differentiable J j q f hr τ lam s background t x hp hm hΩ F hF
  have hfreeze : IsingBulk.Lie.transport V K t x=0 := by
    rw [← mixedCoordinateTransport_eq_lie V K t x hKx,mixedCoordinateTransport_freeze
      (insert q J) background _ _ (mixed_velocity_active_support J j q f r τ lam hj)]
    exact mixed_actual_kernel_frozen J j q f hr τ lam t _ hj hp hm
      (fun i hi => hplateau i (by rcases hi with hi | hi; exact Finset.mem_insert_of_mem hi; simp [hi])) hΩ
  have hCK : IsingBulk.Lie.transport V (fun z a => C*K z a) t x=0 := by
    rw [IsingBulk.Lie.transport_mul V (fun _ _ => C) K t x (differentiableAt_const _) hKs
      (differentiableAt_const _) hKx,hfreeze]
    simp [IsingBulk.Lie.transport]
  exact (IsingBulk.Lie.lieStep_mul_frozen V (fun z a => C*K z a) _ t x
    (hKs.const_mul C) hA.1 (hKx.const_mul C) hA.2 hV hCK).trans (congrArg (fun z => C*K t x*z) hstep)

end
end IsingBulk.Tail
