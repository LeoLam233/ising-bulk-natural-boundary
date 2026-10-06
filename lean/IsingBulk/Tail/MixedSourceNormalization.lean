import IsingBulk.Tail.MixedDensityPointwiseBudget
import IsingBulk.Tail.SelectorOriginal

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators

theorem pulledDensity_zero_independent {N : ℕ} (f g : SelectorFunctions) (r τ : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : pulledDensity f r τ 0 s θ=pulledDensity g r τ 0 s θ := by
  simp only [pulledDensity,deformedPoint_zero,angularJacobian_zero]

theorem mixedDensityNormalization_norm {N : ℕ} (f : SelectorFunctions) (τ lam : ℝ) (θ : Fin N → ℝ) :
    ‖mixedDensityNormalization f τ lam θ‖=
      (N.factorial:ℝ)⁻¹*(2*Real.pi)⁻¹^N*‖(angularJacobian f τ lam θ).det‖ := by
  simp only [mixedDensityNormalization,norm_mul,norm_inv,Complex.norm_natCast,
    zpow_neg,zpow_natCast,norm_pow,Complex.norm_I,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,mul_one,inv_pow]

theorem mixedDensityNormalization_norm_le {N : ℕ} (f : SelectorFunctions) (τ lam : ℝ) (θ : Fin N → ℝ)
    {A : ℝ} (_hA : 0≤A) (hdet : ‖(angularJacobian f τ lam θ).det‖≤A^N) :
    ‖mixedDensityNormalization f τ lam θ‖≤A^N := by
  have hf : (N.factorial:ℝ)⁻¹≤1 := (inv_le_one₀ (by positivity)).mpr (by exact_mod_cast Nat.factorial_pos N)
  have hp : (2*Real.pi)⁻¹≤1 := (inv_le_one₀ (by positivity)).mpr (by linarith [Real.pi_gt_three])
  rw [mixedDensityNormalization_norm]
  calc
    _ ≤ 1*1^N*A^N := by gcongr
    _ = _ := by simp

/-- Complex constants commute with the literal differential operator,
including the Stokes multiplier -2 i tau. -/
theorem lieStep_const_mul {n : ℕ} (V : ℂ → (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (A : ℂ → (Fin (n+1) → ℝ) → ℂ) (c : ℂ) :
    IsingBulk.Lie.lieStep V (fun s x => c*A s x)=fun s x => c*IsingBulk.Lie.lieStep V A s x := by
  funext s x
  have hsp (i : Fin (n+1)) :
      fderiv ℝ (fun y => V s y i*(c*A s y)) x=c • fderiv ℝ (fun y => V s y i*A s y) x := by
    have he : (fun y => V s y i*(c*A s y))=c • (fun y => V s y i*A s y) := by
      funext y
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
    rw [he,fderiv_const_smul_field]
    rfl
  simp only [IsingBulk.Lie.lieStep,IsingBulk.Lie.divergence,deriv_const_mul_field,hsp,
    smul_apply,smul_eq_mul,← Finset.mul_sum]
  ring

theorem iterate_lieStep_const_mul {n : ℕ} (V : ℂ → (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (A : ℂ → (Fin (n+1) → ℝ) → ℂ) (c : ℂ) (k : ℕ) :
    (IsingBulk.Lie.lieStep V)^[k] (fun s x => c*A s x)=
      fun s x => c*((IsingBulk.Lie.lieStep V)^[k] A) s x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,lieStep_const_mul,Function.iterate_succ_apply']

end
end IsingBulk.Tail
