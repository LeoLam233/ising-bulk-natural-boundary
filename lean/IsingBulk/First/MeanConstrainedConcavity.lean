import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

/-! Zero-sum concavity gains the full shape quadratic form. This is a
proved analytic bridge to be instantiated with the actual residue phase. -/
namespace IsingBulk.First
noncomputable section
open Set
open scoped BigOperators

theorem constrained_concavity_sum {N : ℕ} (hN : 0 < N) {r d : ℝ}
    (g g' g'' : ℝ → ℝ)
    (hg : ∀ x ∈ Ioo (-r) r, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo (-r) r, HasDerivAt g' (g'' x) x)
    (hsecond : ∀ x ∈ Ioo (-r) r, g'' x ≤ -d)
    (t : Fin N → ℝ) (ht : ∀ i, t i ∈ Ioo (-r) r) (hsum : ∑ i, t i = 0) :
    ∑ i, g (t i) ≤ N*g 0 - (d/2)*∑ i, (t i)^2 := by
  let H : ℝ → ℝ := fun x => g x+(d/2)*x^2
  let H' : ℝ → ℝ := fun x => g' x+d*x
  let H'' : ℝ → ℝ := fun x => g'' x+d
  have hfirst (x : ℝ) (hx : x ∈ Ioo (-r) r) : HasDerivAt H (H' x) x := by
    have hquad : HasDerivAt (fun y : ℝ => (d/2)*y^2) (d*x) x := by
      convert! (((hasDerivAt_id x).pow 2).const_mul (d/2)) using 1
      simp [id_eq]
      ring
    exact (hg x hx).add hquad
  have hnext (x : ℝ) (hx : x ∈ Ioo (-r) r) : HasDerivAt H' (H'' x) x := by
    simpa [H', H''] using! (hg' x hx).add ((hasDerivAt_id x).const_mul d)
  have hconc : ConcaveOn ℝ (Ioo (-r) r) H := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := H') (f'' := H'') (convex_Ioo _ _)
    · exact fun x hx => (hfirst x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hfirst x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact (hnext x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have h := hsecond x (interior_subset hx)
      dsimp [H'']
      linarith
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hweights : ∑ _i : Fin N, (N:ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hNr.ne'
  have hj := hconc.le_map_sum (t := Finset.univ) (w := fun _ : Fin N => (N:ℝ)⁻¹)
    (p := t) (fun _ _ => inv_nonneg.mpr hNr.le) hweights (fun i _ => ht i)
  simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_zero] at hj
  have hm := mul_le_mul_of_nonneg_left hj hNr.le
  have hmul : (N:ℝ)*((N:ℝ)⁻¹*∑ i, H (t i)) = ∑ i, H (t i) := by
    rw [← mul_assoc, mul_inv_cancel₀ hNr.ne', one_mul]
  rw [hmul] at hm
  dsimp [H] at hm
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, add_zero,
    Finset.sum_add_distrib, ← Finset.mul_sum] at hm
  linarith

end
end IsingBulk.First
