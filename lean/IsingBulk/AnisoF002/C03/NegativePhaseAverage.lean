import IsingBulk.AnisoF002.C03.NegativeUniformEstimates

/-!
# Full phase averages and the zero-sum quadratic residual

Every angle is present in the finite sum.  The linear angular term
cancels on the literal zero-sum constraint; the remaining bound is the
sum of squared displacements divided by the particle number.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

def centeredPhaseAverage (n : ℕ) (g : ℂ × ℂ → ℂ) (γ d : ℂ)
    (v : Fin n → ℂ) (t : ℂ) : ℂ :=
  (∑ i, (g (t, d + v i) - γ)) / (n : ℂ)

def displacementSquare (n : ℕ) (v : Fin n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

theorem displacementSquare_nonneg (n : ℕ) (v : Fin n → ℂ) :
    0 ≤ displacementSquare n v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem centeredPhaseAverage_hasDerivAt (n : ℕ) (g : ℂ × ℂ → ℂ) (γ d : ℂ)
    (v : Fin n → ℂ) (t : ℂ)
    (hg : ∀ i, DifferentiableAt ℂ g (t, d + v i)) :
    HasDerivAt (centeredPhaseAverage n g γ d v)
      ((∑ i, fderiv ℂ g (t, d + v i) (1, 0)) / (n : ℂ)) t := by
  have h (i : Fin n) : HasDerivAt (fun t => g (t, d + v i) - γ)
      (fderiv ℂ g (t, d + v i) (1, 0)) t :=
    ((hg i).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (d + v i)))).sub_const γ
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)).div_const (n : ℂ)

theorem centeredPhaseAverage_deriv_close (n : ℕ) (g : ℂ × ℂ → ℂ) (γ d c : ℂ)
    (v : Fin n → ℂ) (t : ℂ) (hn : 0 < n)
    (hg : ∀ i, DifferentiableAt ℂ g (t, d + v i))
    (hb : ∀ i, ‖fderiv ℂ g (t, d + v i) (1, 0) - c‖ ≤ ‖c‖ / 2) :
    ‖deriv (centeredPhaseAverage n g γ d v) t - c‖ ≤ ‖c‖ / 2 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [(centeredPhaseAverage_hasDerivAt n g γ d v t hg).deriv]
  have he : (∑ i, fderiv ℂ g (t, d + v i) (1, 0)) / (n : ℂ) - c =
      (∑ i, (fderiv ℂ g (t, d + v i) (1, 0) - c)) / (n : ℂ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  rw [he, norm_div, norm_natCast]
  apply (div_le_iff₀ hnR).mpr
  have hb' := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  have hs := (norm_sum_le Finset.univ
    (fun i => fderiv ℂ g (t, d + v i) (1, 0) - c)).trans hb'
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_comm] using hs

theorem centeredPhaseAverage_quadratic_bound (n : ℕ) (g : ℂ × ℂ → ℂ)
    (γ d τ : ℂ) (v : Fin n → ℂ) (M : ℝ)
    (hcenter : g (τ, d) = γ) (hsum : (∑ i, v i) = 0)
    (hbound : ∀ i,
      ‖g (τ, d + v i) - g (τ, d) - fderiv ℂ g (τ, d) ((τ, d + v i) - (τ, d))‖ ≤
        M * ‖(τ, d + v i) - (τ, d)‖ ^ 2) :
    ‖centeredPhaseAverage n g γ d v τ‖ ≤ M * displacementSquare n v / (n : ℝ) := by
  have hlin : (∑ i, fderiv ℂ g (τ, d) ((τ, d + v i) - (τ, d))) = 0 := by
    rw [← map_sum]
    have hv : (∑ i : Fin n, ((τ, d + v i) - (τ, d))) = (0 : ℂ × ℂ) := by
      simp only [Prod.mk_sub_mk, sub_self, add_sub_cancel_left]
      rw [← prod_mk_sum]
      simp only [Finset.sum_const_zero, hsum, Prod.mk_zero_zero]
    rw [hv, map_zero]
  have he : (∑ i, (g (τ, d + v i) - γ)) =
      ∑ i, (g (τ, d + v i) - g (τ, d) -
        fderiv ℂ g (τ, d) ((τ, d + v i) - (τ, d))) := by
    conv_rhs => rw [Finset.sum_sub_distrib, hlin, sub_zero, hcenter]
  have hpair (i : Fin n) : ‖(τ, d + v i) - (τ, d)‖ = ‖v i‖ := by
    simp [Prod.norm_def]
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
  have hs := (norm_sum_le Finset.univ
    (fun i => g (τ, d + v i) - g (τ, d) -
      fderiv ℂ g (τ, d) ((τ, d + v i) - (τ, d)))).trans hb
  simp only [hpair, ← Finset.mul_sum] at hs
  unfold centeredPhaseAverage
  rw [he, norm_div, norm_natCast]
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)

end
end IsingBulk.AnisoF002.NegativeHT
