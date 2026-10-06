import IsingBulk.Tail.MixedSeparatedDensity

namespace IsingBulk.Tail
noncomputable section
open Set
open scoped Topology ContDiff

theorem mixedSeparated_weighted_lie_stages {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (w : (Fin (n+1) → ℝ) → ℂ) (hw : ContDiff ℝ ∞ w) (k : ℕ) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      ((IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam))^[k]
        (fun s θ => w θ*pulledDensity f r τ lam s θ)) := by
  have hΩ := mixedSeparatedDomain_isOpen J j q f hr τ lam hp hm
  have hD := mixedSeparated_density_smooth (Nat.succ_pos n) J j q f hr τ lam hp hm
  have hWeight := ParameterSmoothOn.angular (mixedSeparatedDomain J j q f r τ lam) w hw
  exact (hWeight.mul hD).iterate_lieStep hΩ (mixedContourVelocity J j q f r τ lam) _
    (fun i => mixedSeparated_velocity_smooth J j q f hr τ lam hp hm i) k

theorem mixedSeparated_weighted_lie_stage_analytic {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (w : (Fin (n+1) → ℝ) → ℂ) (hw : ContDiff ℝ ∞ w) (k : ℕ)
    {p : ℂ × (Fin (n+1) → ℝ)} (hpΩ : p∈mixedSeparatedDomain J j q f r τ lam) :
    AnalyticAt ℂ (fun s => ((IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam))^[k]
        (fun s θ => w θ*pulledDensity f r τ lam s θ)) s p.2) p.1 :=
  (mixedSeparated_weighted_lie_stages J j q f hr τ lam hp hm w hw k).parameter_analyticAt
    (mixedSeparatedDomain_isOpen J j q f hr τ lam hp hm) hpΩ

theorem mixedSeparated_weighted_lie_stage_continuous {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (w : (Fin (n+1) → ℝ) → ℂ) (hw : ContDiff ℝ ∞ w) (k : ℕ) :
    ContinuousOn (Function.uncurry
      ((IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam))^[k]
        (fun s θ => w θ*pulledDensity f r τ lam s θ))) (mixedSeparatedDomain J j q f r τ lam) :=
  (mixedSeparated_weighted_lie_stages J j q f hr τ lam hp hm w hw k).continuousOn

end
end IsingBulk.Tail
