import IsingBulk.Tail.AllBranchExteriorScaledVandermonde

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets

theorem allBranchExterior_scaled_numerator_budget {N : ℕ} {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (A : ℂ × (Fin N → ℂ) → ℂ)
    (z : ℂ × (Fin N → ℂ)) (J : ℕ) (C : ℝ)
    (hA : JetBound A (allBranchPhaseScale R z) J C)
    (hφ : ∀ p q, ‖z.2 p-z.2 q‖ ≤ 2) :
    JetBound (unfactoredNumerator A ∘ allBranchPhaseScale R) z J
      ((2:ℝ)^J*((2:ℝ)^J*R^(N*(N-1))*((8:ℝ)^(N.choose 2)*((N.choose 2:ℝ)+1)^J))*C) := by
  have hv := allBranchExterior_unit_vandermonde_budget z J hφ
  have hc := JetBound.const ((R:ℂ)^(N*(N-1))) z J
  have ha := hA.comp (allBranchPhaseScale R) (allBranchPhaseScale_norm hR.le hR1)
  have hh := (hc.mul hv).mul ha
  have he : (unfactoredNumerator A ∘ allBranchPhaseScale R)=
      (fun y => (R:ℂ)^(N*(N-1))*microcoreVandermondeSquared y.2*A (allBranchPhaseScale R y)) :=
    funext (allBranchExterior_scaled_unfactored R A)
  rw [he]
  convert! hh using 1
  simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]

theorem allBranchExterior_near_mixed_numerator_bound {N : ℕ} {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (A : ℂ × (Fin N → ℂ) → ℂ)
    (z : ℂ × (Fin N → ℂ)) (J : ℕ) (C : ℝ) (hA : JetBound A z J C)
    (hφ : ∀ p q, ‖z.2 p-z.2 q‖ ≤ 2*R)
    (l : List (Option (Fin N))) (hl : l.length ≤ J) :
    ‖numeratorJet l (unfactoredNumerator A) z‖ ≤
      ((2:ℝ)^(2*J)*(8:ℝ)^(N.choose 2)*((N.choose 2:ℝ)+1)^J*C)*
        R^(((N*(N-1):ℕ):ℤ)-((spatialWord l).length:ℤ)) := by
  let y : ℂ × (Fin N → ℂ) := (z.1,fun i => z.2 i/(R:ℂ))
  have hRc : (R:ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hy : allBranchPhaseScale R y=z := by
    apply Prod.ext
    · rfl
    · funext i
      change (R:ℂ)*(z.2 i/(R:ℂ))=z.2 i
      field_simp
  have hφy : ∀ p q, ‖y.2 p-y.2 q‖ ≤ 2 := by
    intro p q
    change ‖z.2 p/(R:ℂ)-z.2 q/(R:ℂ)‖ ≤ 2
    rw [← sub_div,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
    exact (div_le_iff₀ hR).mpr (hφ p q)
  have hAy : JetBound A (allBranchPhaseScale R y) J C := by simpa only [hy] using hA
  have hb := allBranchExterior_scaled_numerator_budget hR hR1 A y J C hAy hφy
  have hw := allBranchExterior_anisotropic_word_bound hR (unfactoredNumerator A) y
    (by rw [hy]; exact unfactoredNumerator_analytic A z hA.analytic) l
  rw [hy] at hw
  apply hw.trans
  apply (mul_le_mul_of_nonneg_left (hb.bound l.length hl) (by positivity)).trans_eq
  rw [zpow_sub₀ hR.ne',zpow_natCast,zpow_natCast,div_eq_mul_inv,← inv_pow]
  rw [pow_mul]
  ring

end
end IsingBulk.Tail
