import IsingBulk.HT22.Geometry.SignedActualShell

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set IsingBulk.Preferred22
open scoped BigOperators

/-- A bound for the actual nonempty shell mean, not for arbitrary labels. -/
theorem signedRightShell_abs_mean_le {n : ℕ} (a : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r : ℝ} (hδB : δB<B.delta)
    {l : ℤ} {i j : Fin (n+1)} {θ : Fin n → ℝ}
    (hθ : θ∈signedRightShell a d B δB r l i j) :
    |d.b+(a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)|≤2*Real.pi := by
  let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
  have hw (v : Fin (n+1)) : |w v|≤Real.pi := by
    have hh := preferred_right_interval_original d B hδB (hθ.2.1.1 v)
    exact abs_le.mpr ⟨hh.1.le,hh.2⟩
  have hs : |a+2*Real.pi*(l:ℝ)|≤((n+1:ℕ):ℝ)*Real.pi := by
    rw [←hθ.2.2]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      have hh := Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hw v)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh)
  have hN : (0:ℝ)<((n+1:ℕ):ℝ) := by positivity
  have hm : |(a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)|≤Real.pi := by
    rw [abs_div,abs_of_pos hN]
    exact (div_le_iff₀ hN).mpr (by simpa only [mul_comm] using hs)
  calc
    _ ≤ |d.b|+|(a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)| := abs_add_le _ _
    _ ≤ d.b+Real.pi := by rw [abs_of_pos d.b_pos]; linarith
    _ ≤ _ := by linarith [d.b_lt]

/-- The universal scale cap precedes particle count and every label;
nonemptiness is essential and explicitly required. -/
theorem signedRightShell_scale_le {n : ℕ} (a : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r ε : ℝ} (hδB : δB<B.delta)
    (hr : r≤Real.pi) (hε : ε≤1) {l : ℤ} {i j : Fin (n+1)}
    (hne : (signedRightShell a d B δB r l i j).Nonempty) :
    |d.b+(a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)|+r+ε≤3*Real.pi+1 := by
  obtain ⟨θ,hθ⟩ := hne
  have hh := signedRightShell_abs_mean_le a d B hδB hθ
  linarith

theorem preferredDyadicRadius_le_pi (m : ℕ) : preferredDyadicRadius m≤Real.pi := by
  have hh : (1/2:ℝ)^m≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold preferredDyadicRadius
  rw [pow_succ]
  nlinarith [Real.pi_pos]

theorem signed_dyadic_shell_scale_le {n : ℕ} (a : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB ε : ℝ} (hδB : δB<B.delta)
    (hε : ε≤1) (m : ℕ) {l : ℤ} {i j : Fin (n+1)}
    (hne : (signedRightShell a d B δB (preferredDyadicRadius m) l i j).Nonempty) :
    |d.b+(a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)|+preferredDyadicRadius m+ε≤3*Real.pi+1 :=
  signedRightShell_scale_le a d B hδB (preferredDyadicRadius_le_pi m) hε hne

end
end IsingBulk.HT22.Geometry
