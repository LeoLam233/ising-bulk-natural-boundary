import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueEnvelope

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.Anisotropic.NegativeDominance

/-- Elementary growing-order budget for the exact five residue factors. -/
theorem residue_energy_budget {n : ℕ} (hn : n≠0) {e d q : ℝ}
    (he : 0≤e) (hd : 0≤d) (hq : 0≤q) :
    let H := (n:ℝ)^2*e+(n:ℝ)*d*Real.sqrt ((n:ℝ)*q)+(n:ℝ)*q
    e≤H ∧ (alpha n:ℝ)*e≤H ∧
      (n:ℝ)*e+d*Real.sqrt ((n:ℝ)*q)+q≤H ∧
      (n:ℝ)^2*e+2*(n:ℝ)*d*Real.sqrt ((n:ℝ)*q)+3*(n:ℝ)*q≤3*H ∧
      e+(d*Real.sqrt ((n:ℝ)*q)+q)/(n:ℝ)≤H := by
  let s := Real.sqrt ((n:ℝ)*q)
  have hs : 0≤s := Real.sqrt_nonneg _
  have hn1 : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hn0 : 0<(n:ℝ) := by linarith
  have hn2 : (n:ℝ)≤(n:ℝ)^2 := by nlinarith
  have he1 : e≤(n:ℝ)^2*e := by nlinarith [mul_le_mul_of_nonneg_right (hn1.trans hn2) he]
  have he2 : (n:ℝ)*e≤(n:ℝ)^2*e := mul_le_mul_of_nonneg_right hn2 he
  have hd1 : d*s≤(n:ℝ)*d*s := by
    have h := mul_le_mul_of_nonneg_right hn1 (mul_nonneg hd hs)
    nlinarith
  have hq1 : q≤(n:ℝ)*q := by nlinarith [mul_le_mul_of_nonneg_right hn1 hq]
  have ha : (alpha n:ℝ)≤(n:ℝ)^2 := by
    have hh : alpha n≤n*n := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    have hh' : alpha n≤n^2 := by simpa [pow_two] using hh
    exact_mod_cast hh'
  have hdiv : (d*s+q)/(n:ℝ)≤d*s+q :=
    (div_le_iff₀ hn0).mpr (by nlinarith [mul_le_mul_of_nonneg_right hn1 (add_nonneg (mul_nonneg hd hs) hq)])
  dsimp
  change e≤_ ∧ _ ∧ _ ∧ _ ∧ e+(d*s+q)/(n:ℝ)≤_
  refine ⟨?_,?_,?_,?_,?_⟩
  · nlinarith [mul_nonneg (mul_nonneg hn0.le hd) hs,mul_nonneg hn0.le hq]
  · nlinarith [mul_le_mul_of_nonneg_right ha he,mul_nonneg (mul_nonneg hn0.le hd) hs,mul_nonneg hn0.le hq]
  · nlinarith
  · nlinarith [mul_nonneg (sq_nonneg (n:ℝ)) he,mul_nonneg (mul_nonneg hn0.le hd) hs]
  · nlinarith

end
end IsingBulk.Anisotropic.NegativeNormalForm
