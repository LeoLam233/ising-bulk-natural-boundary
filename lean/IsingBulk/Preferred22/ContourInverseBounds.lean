import IsingBulk.Preferred22.RegularTransport
import IsingBulk.Preferred22.AnalyticCauchyBounds
import IsingBulk.Preferred22.ContourBumpJets
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! Particle-uniform bounds for the true inverse occupancy matrix. The
complex entrywise neighborhood is constructed from the actual row estimate,
and all inverse derivatives are obtained by Cauchy, not assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem preferred_matrix_inverse_of_row_three_quarters {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hrow : ∀ i, (∑ j, ‖(M-1) i j‖) ≤ (3/4:ℝ)) :
    M.det ≠ 0 ∧ ∀ x : Fin N → ℂ, ‖M⁻¹.mulVec x‖ ≤ 4*‖x‖ := by
  have hcoer (v : Fin N → ℂ) : ‖v‖ ≤ 4*‖M.mulVec v‖ := by
    have hh := preferred_matrix_mulVec_row_bound (M-1) (3/4) (by norm_num) hrow v
    rw [Matrix.sub_mulVec,Matrix.one_mulVec] at hh
    have ht := norm_sub_norm_le v (M.mulVec v)
    rw [norm_sub_rev] at ht
    linarith
  have hinj : Function.Injective M.mulVec := by
    intro v w he
    have hh := hcoer (v-w)
    rw [Matrix.mulVec_sub,he,sub_self,norm_zero,mul_zero] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  have hdet : M.det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj))
  refine ⟨hdet,?_⟩
  intro x
  have hh := hcoer (M⁻¹.mulVec x)
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec] at hh
  exact hh

theorem preferred_matrix_entry_norm_of_mulVec_bound {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) {C : ℝ} (hC : 0≤C)
    (hA : ∀ x : Fin N → ℂ, ‖A.mulVec x‖ ≤ C*‖x‖) : ‖A‖≤C := by
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  have hx : ‖(Pi.single j (1:ℂ) : Fin N → ℂ)‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    by_cases hk : k=j <;> simp [hk]
  have he : (A.mulVec (Pi.single j (1:ℂ))) i=A i j := by
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [← he]
  exact (norm_le_pi_norm (A.mulVec (Pi.single j (1:ℂ))) i).trans
    ((hA _).trans ((mul_le_mul_of_nonneg_left hx hC).trans_eq (mul_one C)))

theorem preferred_matrix_inv_analyticAt {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ) (hdet : M.det≠0) :
    AnalyticAt ℂ (fun A : Matrix (Fin N) (Fin N) ℂ => A⁻¹) M := by
  have he (i j : Fin N) : AnalyticAt ℂ (fun A : Matrix (Fin N) (Fin N) ℂ => A i j) M :=
    ((ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj i : (Matrix (Fin N) (Fin N) ℂ) →L[ℂ] (Fin N → ℂ))).analyticAt M
  have hd : AnalyticAt ℂ (fun A : Matrix (Fin N) (Fin N) ℂ => A.det) M := by
    simp only [Matrix.det_apply']
    exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
      analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => he (σ i) i)))
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  have ha : AnalyticAt ℂ (fun A : Matrix (Fin N) (Fin N) ℂ => A.adjugate i j) M := by
    simp only [Matrix.adjugate_apply,Matrix.det_apply']
    apply Finset.univ.analyticAt_fun_sum
    intro σ _
    apply analyticAt_const.mul
    apply Finset.univ.analyticAt_fun_prod
    intro k _
    by_cases hk : σ k=j
    · simpa only [Matrix.updateRow,Matrix.of_apply,Function.update_apply,hk,ite_true] using
        (analyticAt_const : AnalyticAt ℂ (fun _A : Matrix (Fin N) (Fin N) ℂ =>
          (Pi.single i (1:ℂ) : Fin N → ℂ) k) M)
    · simpa only [Matrix.updateRow,Matrix.of_apply,Function.update_apply,hk,ite_false] using he (σ k) k
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact (hd.inv hdet).fun_mul ha

/-- A true complex matrix ball of radius 1/(4N) around the actual half-row
neighborhood stays uniformly invertible. -/
theorem preferred_matrix_inverse_ball {N : ℕ} (hN : 0<N)
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hrow : ∀ i, (∑ j, ‖(M-1) i j‖)≤(1/2:ℝ)) :
    ∀ A∈ball M (1/(4*(N:ℝ))), A.det≠0 ∧ ‖A⁻¹‖≤4 := by
  intro A hA
  have hNR : 0<(N:ℝ) := by exact_mod_cast hN
  have hdist : ‖A-M‖<1/(4*(N:ℝ)) := by simpa only [mem_ball,dist_eq_norm] using hA
  have harow (i : Fin N) : (∑ j, ‖(A-1) i j‖)≤(3/4:ℝ) := by
    have he (j : Fin N) : ‖(A-1) i j‖≤‖A-M‖+‖(M-1) i j‖ := by
      calc
        _ = ‖(A-M) i j+(M-1) i j‖ := by congr 1; simp only [Matrix.sub_apply]; ring
        _ ≤ ‖(A-M) i j‖+‖(M-1) i j‖ := norm_add_le _ _
        _ ≤ _ := add_le_add ((norm_le_pi_norm ((A-M) i) j).trans
          (norm_le_pi_norm (A-M) i)) le_rfl
    calc
      _ ≤ ∑ j, (‖A-M‖+‖(M-1) i j‖) := Finset.sum_le_sum (fun j _ => he j)
      _ = (N:ℝ)*‖A-M‖+∑ j,‖(M-1) i j‖ := by simp [Finset.sum_add_distrib]
      _ ≤ (N:ℝ)*(1/(4*(N:ℝ)))+1/2 :=
        add_le_add (mul_le_mul_of_nonneg_left hdist.le hNR.le) (hrow i)
      _ = 3/4 := by field_simp; ring
  obtain ⟨hd,hi⟩ := preferred_matrix_inverse_of_row_three_quarters A harow
  exact ⟨hd,preferred_matrix_entry_norm_of_mulVec_bound _ (by norm_num) hi⟩

/-- Uniform all-order inverse matrix derivatives, in the actual entrywise
norm. The sole order-dependent constant is explicit and precedes N. -/
theorem preferred_matrix_inverse_all_jets (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 0<N → ∀ M : Matrix (Fin N) (Fin N) ℂ,
      (∀ i, (∑ k, ‖(M-1) i k‖)≤(1/2:ℝ)) →
      ‖iteratedFDeriv ℂ j (fun A : Matrix (Fin N) (Fin N) ℂ => A⁻¹) M‖≤C*(N:ℝ)^j := by
  refine ⟨cauchyJetConstant j*4*4^j,by have := cauchyJetConstant_pos j; positivity,?_⟩
  intro N hN M hrow
  have hr : 0<1/(4*(N:ℝ)) := by
    have : 0<(N:ℝ) := by exact_mod_cast hN
    positivity
  have hb := preferred_matrix_inverse_ball hN M hrow
  have hf : AnalyticOnNhd ℂ (fun A : Matrix (Fin N) (Fin N) ℂ => A⁻¹)
      (ball M (1/(4*(N:ℝ)))) := fun A hA => preferred_matrix_inv_analyticAt A (hb A hA).1
  have hh := analytic_iteratedFDeriv_center_bound (fun A : Matrix (Fin N) (Fin N) ℂ => A⁻¹)
    M (1/(4*(N:ℝ))) 4 hr hf (fun A hA => (hb A hA).2) j
  convert hh using 1
  rw [div_pow,one_pow,div_div_eq_mul_div,div_one,mul_pow]
  ring

/-- The same explicit inverse-map jets apply to real angular compositions. -/
theorem preferred_matrix_inverse_all_real_jets (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 0<N → ∀ M : Matrix (Fin N) (Fin N) ℂ,
      (∀ i, (∑ k, ‖(M-1) i k‖)≤(1/2:ℝ)) →
      ‖iteratedFDeriv ℝ j (fun A : Matrix (Fin N) (Fin N) ℂ => A⁻¹) M‖≤C*(N:ℝ)^j := by
  obtain ⟨C,hC,hbound⟩ := preferred_matrix_inverse_all_jets j
  refine ⟨C,hC,?_⟩
  intro N hN M hrow
  have hd := (preferred_matrix_inverse_of_row_half M hrow).1
  have ha := preferred_matrix_inv_analyticAt M hd
  have he := (ha.contDiffAt.of_le (show (j:ℕ∞ω)≤ω by simp)).restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  rw [← he,Function.comp_apply,ContinuousMultilinearMap.norm_restrictScalars]
  exact hbound N hN M hrow

/-- The small-row input is derived from the literal coupled occupancy
differential, including both derivatives of the occupancy sums. -/
theorem preferredContourMatrix_half_row {N : ℕ} (hN : 0<N) (τ B : ℝ)
    (hτ : 0≤τ) (hB : 0≤B) (hsmall : 4*τ*B≤1/2)
    (p m : ℝ → ℝ) (θ : Fin N → ℝ)
    (hp : ∀ i, |p (θ i)|≤1) (hm : ∀ i, |m (θ i)|≤1)
    (hdp : ∀ i, |deriv p (θ i)|≤B) (hdm : ∀ i, |deriv m (θ i)|≤B) :
    ∀ i, (∑ j, ‖(preferredContourMatrix τ p m θ-1) i j‖)≤(1/2:ℝ) := by
  intro i
  have he (j : Fin N) : ‖(preferredContourMatrix τ p m θ-1) i j‖ =
      |shiftJacobian τ (fun a => p (θ a)) (fun a => m (θ a))
        (fun a => deriv p (θ a)) (fun a => deriv m (θ a)) i j| := by
    simp only [Matrix.sub_apply,preferredContourMatrix,Matrix.one_apply]
    rw [show (if i=j then (1:ℂ) else 0)-Complex.I*
      (shiftJacobian τ (fun a => p (θ a)) (fun a => m (θ a))
        (fun a => deriv p (θ a)) (fun a => deriv m (θ a)) i j:ℝ)-
      (if i=j then 1 else 0) = -Complex.I*
      (shiftJacobian τ (fun a => p (θ a)) (fun a => m (θ a))
        (fun a => deriv p (θ a)) (fun a => deriv m (θ a)) i j:ℝ) by ring]
    simp only [norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,one_mul,Real.norm_eq_abs]
  simp_rw [he]
  exact (preferred_shiftJacobian_row_bound hN τ B hτ hB _ _ _ _ hp hm hdp hdm i).trans hsmall

/-- One threshold, before every derivative order and particle count, puts
the actual contour matrices in the same uniformly invertible family. -/
theorem preferredContourMatrix_uniform_half_row (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (hp1 : ∀ x, |p x|≤1) (hm1 : ∀ x, |m x|≤1) :
    ∃ τ₀ : ℝ, 0<τ₀ ∧ ∀ τ : ℝ, 0≤τ → τ≤τ₀ →
      ∀ N : ℕ, 0<N → ∀ θ : Fin N → ℝ,
        ∀ i, (∑ j, ‖(preferredContourMatrix τ p m θ-1) i j‖)≤(1/2:ℝ) := by
  obtain ⟨Bp,hBp,hbp⟩ := bump_finite_jets p hp hpp 1
  obtain ⟨Bm,hBm,hbm⟩ := bump_finite_jets m hm hmp 1
  let B := Bp+Bm
  have hB : 0<B := by dsimp [B]; positivity
  have hdp (x : ℝ) : |deriv p x|≤B := by
    rw [← Real.norm_eq_abs,norm_deriv_eq_norm_fderiv]
    have hh : ‖fderiv ℝ p x‖≤Bp := by
      simpa only [norm_iteratedFDeriv_one] using hbp 1 (by omega) x
    exact hh.trans (by dsimp [B]; linarith)
  have hdm (x : ℝ) : |deriv m x|≤B := by
    rw [← Real.norm_eq_abs,norm_deriv_eq_norm_fderiv]
    have hh : ‖fderiv ℝ m x‖≤Bm := by
      simpa only [norm_iteratedFDeriv_one] using hbm 1 (by omega) x
    exact hh.trans (by dsimp [B]; linarith)
  refine ⟨1/(8*B),by positivity,?_⟩
  intro τ hτ hτ₀ N hN θ
  have hsmall : 4*τ*B≤1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<8*B)).mp hτ₀
    nlinarith
  exact preferredContourMatrix_half_row hN τ B hτ hB.le hsmall p m θ
    (fun i => hp1 (θ i)) (fun i => hm1 (θ i)) (fun i => hdp (θ i)) (fun i => hdm (θ i))

end
end IsingBulk.Preferred22
