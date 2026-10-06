import IsingBulk.Tail.SharpExteriorCutoffJetBounds

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets
open scoped ContDiff

/-- Multiplication by a fixed smooth cutoff preserves the one inverse-scale
factor per spatial derivative of the moving cutoff. -/
theorem cutoffJet_product_scale_bound {N J : ℕ} (f g : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (u : Fin N → ℝ)
    {A B ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hfj : ∀ k : List (Fin N), k.length ≤ J → ‖cutoffJet k f u‖ ≤ A)
    (hgj : ∀ k : List (Fin N), k.length ≤ J → ‖cutoffJet k g u‖ ≤ B*(ρ⁻¹)^k.length)
    (l : List (Fin N)) (hl : l.length ≤ J) :
    ‖cutoffJet l (fun x => f x*g x) u‖ ≤ (2:ℝ)^J*A*B*(ρ⁻¹)^l.length := by
  have hb := cutoffJet_product_uniform_bound (J := l.length) f g hf hg u hA
    (show 0 ≤ B*(ρ⁻¹)^l.length by positivity) (fun k hk => hfj k (hk.trans hl))
    (fun k hk => (hgj k (hk.trans hl)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ ((one_le_inv₀ hρ).mpr hρ1) hk) hB)) l le_rfl
  apply hb.trans
  calc
    _ ≤ (2:ℝ)^J*A*(B*(ρ⁻¹)^l.length) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hl) hA) (by positivity)
    _ = _ := by ring

theorem cutoffJet_product_diameter_bound {N J : ℕ} (f g : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (u : Fin N → ℝ)
    {A B ρ D T : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hD : 0 < D) (hDρ : D ≤ T*ρ) (hT : 1 ≤ T)
    (hfj : ∀ k : List (Fin N), k.length ≤ J → ‖cutoffJet k f u‖ ≤ A)
    (hgj : ∀ k : List (Fin N), k.length ≤ J → ‖cutoffJet k g u‖ ≤ B*(ρ⁻¹)^k.length)
    (l : List (Fin N)) (hl : l.length ≤ J) :
    ‖cutoffJet l (fun x => f x*g x) u‖ ≤ ((2:ℝ)^J*A*B*T^J)/D^l.length := by
  have hb := cutoffJet_product_scale_bound f g hf hg u hA hB hρ hρ1 hfj hgj l hl
  have hratio : ρ⁻¹ ≤ T/D := by
    apply (le_div_iff₀ hD).mpr
    rw [mul_comm,← div_eq_mul_inv]
    exact (div_le_iff₀ hρ).mpr hDρ
  have hp : (ρ⁻¹)^l.length ≤ T^J/D^l.length := by
    calc
      _ ≤ (T/D)^l.length := pow_le_pow_left₀ (inv_nonneg.mpr hρ.le) hratio _
      _ = T^l.length/D^l.length := div_pow _ _ _
      _ ≤ _ := div_le_div_of_nonneg_right (pow_le_pow_right₀ hT hl) (pow_nonneg hD.le _)
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (2:ℝ)^J*A*B by positivity)
  exact hh.trans_eq (by ring)

end
end IsingBulk.Tail
