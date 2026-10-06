import IsingBulk.First.AngularFubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Exact shifts of the angular fundamental box. Coordinatewise periodicity
is used at the integral level, with no boundary or orientation factor lost. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory

def CoordinatePeriodic (N : ℕ) (f : (Fin N → ℝ) → ℂ) : Prop :=
  ∀ x i, f (Function.update x i (x i+2*Real.pi)) = f x

theorem coordinatePeriodic_cons_zero {n : ℕ} {f : (Fin (n+1) → ℝ) → ℂ}
    (hf : CoordinatePeriodic (n+1) f) (x : Fin n → ℝ) :
    Function.Periodic (fun u : ℝ => f ((Fin.cons u x : Fin (n+1) → ℝ))) (2*Real.pi) := by
  intro u
  have he : Function.update ((Fin.cons u x : Fin (n+1) → ℝ)) 0 (u+2*Real.pi) = (Fin.cons (u+2*Real.pi) x : Fin (n+1) → ℝ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hh := hf ((Fin.cons u x : Fin (n+1) → ℝ)) 0
  simpa only [Fin.cons_zero, he] using hh

theorem coordinatePeriodic_cons_integral {n : ℕ} {f : (Fin (n+1) → ℝ) → ℂ}
    (hf : CoordinatePeriodic (n+1) f) :
    CoordinatePeriodic n (fun x => ∫ u : ℝ in 0..2*Real.pi, f ((Fin.cons u x : Fin (n+1) → ℝ))) := by
  intro x i
  apply intervalIntegral.integral_congr
  intro u _
  have he : (Fin.cons u (Function.update x i (x i+2*Real.pi)) : Fin (n+1) → ℝ) =
      Function.update ((Fin.cons u x : Fin (n+1) → ℝ)) i.succ (((Fin.cons u x : Fin (n+1) → ℝ)) i.succ+2*Real.pi) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    · simp only [Fin.cons_succ]
      by_cases hk : k=i
      · subst k; simp
      · have hs : k.succ ≠ i.succ := fun h => hk (Fin.succ_inj.mp h)
        simp [Function.update_of_ne hk, Function.update_of_ne hs]
  dsimp only
  rw [he]
  exact hf _ _

theorem multiAngleIntegral_shift (N : ℕ) (f : (Fin N → ℝ) → ℂ)
    (hf : CoordinatePeriodic N f) (c : Fin N → ℝ) :
    multiAngleIntegral N (fun x => f (fun i => x i+c i)) = multiAngleIntegral N f := by
  induction N with
  | zero =>
    simp only [multiAngleIntegral]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    have hi (x : Fin n → ℝ) :
        (∫ u : ℝ in 0..2*Real.pi, f (fun i => (Fin.cons u x : Fin (n+1) → ℝ) i+c i)) =
          ∫ u : ℝ in 0..2*Real.pi, f ((Fin.cons u (fun i => x i+c i.succ) : Fin (n+1) → ℝ)) := by
      have he (u : ℝ) : (fun i => (Fin.cons u x : Fin (n+1) → ℝ) i+c i) =
          (Fin.cons (u+c 0) (fun i => x i+c i.succ) : Fin (n+1) → ℝ) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      simp_rw [he]
      rw [intervalIntegral.integral_comp_add_right
        (fun v : ℝ => f (Fin.cons v (fun i => x i+c i.succ))) (c 0)]
      simpa only [zero_add, add_comm (2*Real.pi) (c 0)] using
        (coordinatePeriodic_cons_zero hf (fun i => x i+c i.succ)).intervalIntegral_add_eq (c 0) 0
    simp only [multiAngleIntegral]
    simp_rw [hi]
    exact ih _ (coordinatePeriodic_cons_integral hf) (fun i => c i.succ)

theorem angleBox_integral_shift (N : ℕ) (f : (Fin N → ℝ) → ℂ)
    (hc : Continuous f) (hf : CoordinatePeriodic N f) (c : Fin N → ℝ) :
    (∫ x in angleBox N, f (fun i => x i+c i)) = ∫ x in angleBox N, f x := by
  have hshift : Continuous (fun x : Fin N → ℝ => f (fun i => x i+c i)) :=
    hc.comp (continuous_pi (fun i => (continuous_apply i).add continuous_const))
  rw [← multiAngleIntegral_eq_box N _ hshift, ← multiAngleIntegral_eq_box N f hc]
  exact multiAngleIntegral_shift N f hf c

end
end IsingBulk.First
