import IsingBulk.Tail.PeriodicSectorLie
import IsingBulk.Tail.MixedFrozenPhase

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Lie
open scoped BigOperators

theorem update_period_eq_add_single {N : ℕ} (x : Fin N → ℝ) (i : Fin N) :
    Function.update x i (x i+2*Real.pi)=x+Pi.single i (2*Real.pi) := by
  funext j
  by_cases h : j=i
  · subst j; simp
  · simp [Function.update_of_ne h,Pi.single_eq_of_ne h]

theorem coordinatePeriodic_fderiv_direction {N : ℕ} (f : (Fin N → ℝ) → ℂ)
    (hp : CoordinatePeriodic N f) (v : Fin N → ℝ) :
    CoordinatePeriodic N (fun x => fderiv ℝ f x v) := by
  intro x i
  have he : (fun y => f (y+Pi.single i (2*Real.pi)))=f := by
    funext y
    simpa only [← update_period_eq_add_single] using hp y i
  dsimp only
  rw [update_period_eq_add_single,← fderiv_comp_add_right,he]

theorem coordinatePeriodic_mul {N : ℕ} {f g : (Fin N → ℝ) → ℂ}
    (hf : CoordinatePeriodic N f) (hg : CoordinatePeriodic N g) :
    CoordinatePeriodic N (fun x => f x*g x) := fun x i => by
  dsimp only
  rw [hf x i,hg x i]

theorem coordinatePeriodic_parameter_deriv {N : ℕ} (A : ℂ → (Fin N → ℝ) → ℂ)
    (hA : ∀ s,CoordinatePeriodic N (A s)) (s : ℂ) :
    CoordinatePeriodic N (fun x => deriv (fun t => A t x) s) := by
  intro x i
  have he : (fun t => A t (Function.update x i (x i+2*Real.pi)))=(fun t => A t x) :=
    funext (fun t => hA t x i)
  dsimp only
  rw [he]

theorem coordinatePeriodic_lieStep {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (hV : ∀ s i,CoordinatePeriodic (n+1) (fun x => V s x i))
    (hA : ∀ s,CoordinatePeriodic (n+1) (A s)) (s : ℂ) :
    CoordinatePeriodic (n+1) (lieStep V A s) := by
  have hd := coordinatePeriodic_parameter_deriv A hA s
  have hflux (i : Fin (n+1)) := coordinatePeriodic_mul (hV s i) (hA s)
  intro x q
  unfold lieStep divergence
  dsimp only
  have hdx := hd x q
  dsimp only at hdx
  rw [hdx]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact coordinatePeriodic_fderiv_direction _ (hflux i) (Pi.single i 1) x q

theorem coordinatePeriodic_iterate_lieStep {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (hV : ∀ s i,CoordinatePeriodic (n+1) (fun x => V s x i))
    (hA : ∀ s,CoordinatePeriodic (n+1) (A s)) (k : ℕ) :
    ∀ s,CoordinatePeriodic (n+1) (((lieStep V)^[k] A) s) := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact coordinatePeriodic_lieStep V _ hV ih

theorem mixedContourVelocity_periodic {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (hf : RegularSelector f) (r τ lam : ℝ) (s : ℂ) (i : Fin N) :
    CoordinatePeriodic N (fun θ => mixedContourVelocity J j q f r τ lam s θ i) := by
  intro θ k
  unfold mixedContourVelocity
  dsimp only
  rw [deformedPoint_periodic f hf]

end
end IsingBulk.Tail
