import IsingBulk.Anisotropic.NegativeCycles.CapTransport
import IsingBulk.Anisotropic.Algebra.DeterminantBound

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open scoped BigOperators

theorem norm_det_le_sqrt_entry_bound {n : ℕ} (hn : 0<n)
    (M : Matrix (Fin n) (Fin n) ℂ) {L : ℝ} (hL : 0≤L)
    (hM : ∀ i j, ‖M i j‖≤L) :
    ‖M.det‖≤Real.sqrt (((n:ℝ)*L^2)^n) := by
  have hd := Algebra.norm_det_sq_le_entry_bound M hL hM (by simpa using hn)
  simp only [Fintype.card_fin] at hd
  have hq : 0≤((n:ℝ)*L^2)^n := by positivity
  nlinarith [Real.sq_sqrt hq,Real.sqrt_nonneg (((n:ℝ)*L^2)^n),norm_nonneg M.det]

/-- Boundary-chain Jacobians cost only the actual Hadamard factor. The density
bound is used on the complex chain, with no modulus-one assertion for its roots. -/
theorem norm_cutoffError_density_le {n : ℕ} (hn : 0<n)
    (χ : ParameterSpace n → ℝ) (f : (Fin n → ℂ) → ℂ)
    (H : ParameterSpace n → Fin n → ℂ) (x : ParameterSpace n)
    {K F L : ℝ} (hK : 0≤K) (hF : 0≤F) (hL : 0≤L)
    (hχ : ∀i, ‖fderiv ℝ χ x (Pi.single i 1)‖≤K)
    (hf : ‖f (H x)‖≤F)
    (hH : ∀i j, ‖fderiv ℝ H x (Pi.single i 1) j‖≤L) :
    ‖cutoffError χ (chainPullback (densityForm f) H) x‖≤
      (n+1)*K*F*Real.sqrt (((n:ℝ)*L^2)^n) := by
  unfold cutoffError
  calc
    _ ≤ ∑ i : Fin (n+1), ‖(-1:ℤ)^i.val •
        (fderiv ℝ χ x (Pi.single i 1)) •
          chainPullback (densityForm f) H x
            (i.removeNth (fun k => (Pi.single k (1:ℝ) : ParameterSpace n)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin (n+1), K*F*Real.sqrt (((n:ℝ)*L^2)^n) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg),norm_smul,
        densityForm_chainPullback,norm_mul]
      rw [mul_assoc K F]
      apply mul_le_mul (hχ i) ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK
      apply mul_le_mul hf (norm_det_le_sqrt_entry_bound hn _ hL ?_) (norm_nonneg _) hF
      intro a b
      exact hH (i.succAbove a) b
    _ = _ := by simp; ring

end IsingBulk.Anisotropic.NegativeCycles
