import IsingBulk.Anisotropic.NegativeNormalForm.Algebra
import Mathlib.Analysis.Calculus.FDeriv.Linear

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

def meanCLM (n : ℕ) : Config n →L[ℂ] ℂ :=
  (n:ℂ)⁻¹ • ∑ i : Fin n, ContinuousLinearMap.proj i

@[simp] theorem meanCLM_apply {n : ℕ} (v : Config n) : meanCLM n v=mean v := by
  simp [meanCLM,mean,div_eq_mul_inv,mul_comm]

def meanVectorCLM (n : ℕ) : Config n →L[ℂ] Config n := ContinuousLinearMap.pi (fun _ => meanCLM n)

def projectCLM (n : ℕ) : Config n →L[ℂ] Config n := ContinuousLinearMap.id ℂ (Config n)-meanVectorCLM n

@[simp] theorem projectCLM_apply {n : ℕ} (v : Config n) : projectCLM n v=project v := by
  ext i
  simp [projectCLM,meanVectorCLM,project]

theorem project_eq_self {n : ℕ} {v : Config n} (hv : ZeroMean v) : project v=v := by
  ext i
  simp [project,mean,ZeroMean] at *
  rw [hv]
  simp

theorem projectCLM_idempotent {n : ℕ} (hn : n ≠ 0) :
    (projectCLM n).comp (projectCLM n)=projectCLM n := by
  ext v i
  simp only [ContinuousLinearMap.comp_apply,projectCLM_apply]
  rw [project_eq_self (project_zeroMean hn v)]

/-- Uniform in dimension for the actual maximum norm used by Config n. -/
theorem norm_mean_le {n : ℕ} (hn : n ≠ 0) (v : Config n) : ‖mean v‖ ≤ ‖v‖ := by
  have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [mean,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ hn').mpr
  calc
    ‖∑ i : Fin n, v i‖ ≤ ∑ i : Fin n, ‖v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ := Finset.sum_le_sum (fun i _ => norm_le_pi_norm v i)
    _ = ‖v‖*(n:ℝ) := by simp [mul_comm]

theorem norm_project_le {n : ℕ} (hn : n ≠ 0) (v : Config n) : ‖project v‖ ≤ 2*‖v‖ := by
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
  intro i
  exact (norm_sub_le _ _).trans (by
    change ‖v i‖+‖mean v‖ ≤ 2*‖v‖
    linarith [norm_le_pi_norm v i,norm_mean_le hn v])

end
end IsingBulk.Anisotropic.NegativeNormalForm
