import IsingBulk.First.PeriodicBump
import IsingBulk.First.ContourIntegrability
import Mathlib.Algebra.Ring.Periodic

/-! Exact invariance of any coordinatewise periodic function under the
principal-angle lift. The target may be real, complex, or another type. -/
namespace IsingBulk.First
noncomputable section
open Complex Set

theorem periodicAngle_eq_add_int_period (u : ℝ) :
    ∃ k : ℤ, periodicAngle u = u+(k:ℝ)*(2*Real.pi) := by
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp (periodicAngle_exp u)
  refine ⟨k,?_⟩
  have hi := congrArg Complex.im hk
  simpa [Complex.mul_im,Complex.mul_re] using hi

theorem coordinatePeriodic_update_int {N : ℕ} {A : Type*} (F : (Fin N → ℝ) → A)
    (hF : ∀ x i, F (Function.update x i (x i+2*Real.pi)) = F x)
    (x : Fin N → ℝ) (i : Fin N) (k : ℤ) :
    F (Function.update x i (x i+(k:ℝ)*(2*Real.pi))) = F x := by
  have hp : Function.Periodic (fun v => F (Function.update x i v)) (2*Real.pi) := by
    intro v
    have hh := hF (Function.update x i v) i
    simpa only [Function.update_self,Function.update_idem] using hh
  simpa only [Function.update_eq_self] using (hp.int_mul k) (x i)

theorem coordinatePeriodic_centeredWrap {N : ℕ} {A : Type*} (F : (Fin N → ℝ) → A)
    (hF : ∀ x i, F (Function.update x i (x i+2*Real.pi)) = F x)
    (c x : Fin N → ℝ) : F (centeredWrap c x) = F x := by
  classical
  have hstep (T : Finset (Fin N)) : F (fun i => if i ∈ T then centeredWrap c x i else x i) = F x := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
      let q : Fin N → ℝ := fun j => if j ∈ T then centeredWrap c x j else x j
      have hq : q i = x i := by simp [q,hi]
      have he : (fun j => if j ∈ insert i T then centeredWrap c x j else x j) =
          Function.update q i (centeredWrap c x i) := by
        funext j
        by_cases hj : j=i
        · subst j; simp
        · simp [q,hj]
      obtain ⟨k,hk⟩ := periodicAngle_eq_add_int_period (x i-c i)
      have hw : centeredWrap c x i = q i+(k:ℝ)*(2*Real.pi) := by
        rw [hq,centeredWrap,hk]
        ring
      rw [he,hw,coordinatePeriodic_update_int F hF q i k]
      exact ih
  simpa only [Finset.mem_univ,ite_true] using hstep Finset.univ

theorem centeredWrap_pi_mem_angleBox {N : ℕ} (x : Fin N → ℝ) :
    centeredWrap (fun _ => Real.pi) x ∈ angleBox N := by
  constructor
  · intro i
    have h := Complex.neg_pi_lt_log_im (exp (((x i-Real.pi:ℝ):ℂ)*I))
    change 0 ≤ Real.pi+periodicAngle (x i-Real.pi)
    dsimp [periodicAngle]
    linarith
  · intro i
    have h := Complex.log_im_le_pi (exp (((x i-Real.pi:ℝ):ℂ)*I))
    change Real.pi+periodicAngle (x i-Real.pi) ≤ 2*Real.pi
    dsimp [periodicAngle]
    linarith

end
end IsingBulk.First
