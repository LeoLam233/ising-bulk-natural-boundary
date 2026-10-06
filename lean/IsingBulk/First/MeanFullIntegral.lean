import IsingBulk.First.MeanPhysicalLemma

/-! The compact smooth mean integral equals the full real integral for the
actual compactly supported mean cutoff. -/
namespace IsingBulk.First
noncomputable section
open Set Complex MeasureTheory

theorem smoothMeanIntegral_eq_full {n : ℕ} (eta : ℝ → ℂ) (s : ℂ)
    (rho alpha delta : ℝ) (t : Fin n → ℝ) (hd : 0 < delta)
    (hsupport : ∀ x : ℝ, 2*delta < |x| → eta x=0) :
    smoothMeanIntegral eta s rho alpha delta t =
      ∫ x : ℝ, eta x * meanLocalDensity s rho alpha t (x:ℂ) := by
  unfold smoothMeanIntegral
  rw [intervalIntegral.integral_of_le (by linarith),← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hout : 2*delta < |x| := by
    by_contra h
    have hh := abs_le.mp (le_of_not_gt h)
    exact hx ⟨by linarith [hh.1],hh.2⟩
  rw [hsupport x hout,zero_mul]

end
end IsingBulk.First
