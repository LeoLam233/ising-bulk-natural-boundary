import IsingBulk.Tail.MixedDensityLieGerm
import IsingBulk.Tail.MixedSeparatedLieStages

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Freeze restriction commutes with finite Lie iteration on the actual
open smoothness domain. No regularity at a kernel pole is assumed. -/
theorem lieStep_iterate_mixedFreeze {n : ℕ} (S : Finset (Fin (n+1))) (background : Fin (n+1) → ℝ)
    (V : ℂ → (Fin (n+1) → ℝ) → Fin (n+1) → ℂ) (A : ℂ → (Fin (n+1) → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin (n+1) → ℝ))) (hΩ : IsOpen Ω)
    (hV : ∀ i,i∉S → ∀ s x,V s x i=0)
    (hVs : ∀ i,ParameterSmoothOn Ω (fun s x => V s x i))
    (hAs : ∀ k,ParameterSmoothOn Ω ((IsingBulk.Lie.lieStep V)^[k] A)) (k : ℕ)
    (s : ℂ) (x : Fin (n+1) → ℝ) (hsx : (s,mixedFreeze S background x)∈Ω) :
    ((IsingBulk.Lie.lieStep (fun t y => V t (mixedFreeze S background y)))^[k]
      (fun t y => A t (mixedFreeze S background y))) s x=
    ((IsingBulk.Lie.lieStep V)^[k] A) s (mixedFreeze S background x) := by
  let H := fun p : ℂ × (Fin (n+1) → ℝ) => (p.1,mixedFreeze S background p.2)
  have hH : Continuous H := continuous_fst.prodMk ((mixedFreeze_continuous S background).comp continuous_snd)
  induction k generalizing s x with
  | zero => rfl
  | succ k ih =>
    have he : Function.uncurry ((IsingBulk.Lie.lieStep (fun t y => V t (mixedFreeze S background y)))^[k]
        (fun t y => A t (mixedFreeze S background y))) =ᶠ[𝓝 (s,x)]
        Function.uncurry (fun t y => ((IsingBulk.Lie.lieStep V)^[k] A) t (mixedFreeze S background y)) := by
      have hnear : ∀ᶠ p in 𝓝 (s,x),H p∈Ω := hH.continuousAt.eventually (hΩ.mem_nhds hsx)
      filter_upwards [hnear] with p hp
      exact ih p.1 p.2 hp
    rw [Function.iterate_succ_apply',lieStep_congr_joint_germ _ s x he,
      lieStep_mixedFreeze S background V _ hV s x (fun i =>
        ((hVs i).angular_differentiableAt hsx).mul ((hAs k).angular_differentiableAt hsx)),
      Function.iterate_succ_apply']

theorem mixed_actual_weighted_iterate_freeze {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j∈J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (w : (Fin (n+1) → ℝ) → ℂ) (hw : ContDiff ℝ ∞ w)
    (s : ℂ) (θ : Fin (n+1) → ℝ) (hΩ : (s,θ)∈mixedSeparatedDomain J j q f r τ lam) (k : ℕ) :
    ((IsingBulk.Lie.lieStep (fun t x => mixedContourVelocity J j q f r τ lam t (mixedFreeze (insert q J) θ x)))^[k]
      (fun t x => w (mixedFreeze (insert q J) θ x)*pulledDensity f r τ lam t (mixedFreeze (insert q J) θ x))) s θ=
    ((IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam))^[k]
      (fun t x => w x*pulledDensity f r τ lam t x)) s θ := by
  have hh := lieStep_iterate_mixedFreeze (insert q J) θ (mixedContourVelocity J j q f r τ lam)
    (fun t x => w x*pulledDensity f r τ lam t x) (mixedSeparatedDomain J j q f r τ lam)
    (mixedSeparatedDomain_isOpen J j q f hr τ lam hp hm) (mixed_velocity_active_support J j q f r τ lam hj)
    (fun i => mixedSeparated_velocity_smooth J j q f hr τ lam hp hm i)
    (fun a => mixedSeparated_weighted_lie_stages J j q f hr τ lam hp hm w hw a) k s θ
    (by simpa only [mixedFreeze_self] using hΩ)
  simpa only [mixedFreeze_self] using hh

end
end IsingBulk.Tail
