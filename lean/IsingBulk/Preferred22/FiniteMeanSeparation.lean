import IsingBulk.Preferred22.Arithmetic
import IsingBulk.Preferred22.ShellGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The finite-block constrained-mean gap is obtained from the actual
nonresonant physical branch. No all-order Diophantine estimate is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex

theorem preferred_prime_branch_formula (d : PreferredBranchData) {p : ℕ} {a : ℤ}
    (ha : d.alpha=IsingBulk.PrimeFamily.angle p a) :
    primeBranch p a=Complex.exp (-(d.b:ℂ)*Complex.I) := by
  unfold primeBranch
  rw [← ha,← d.angle_relation,Real.arccos_cos d.b_pos.le d.b_lt.le]

theorem preferred_prime_branch_power_mean (d : PreferredBranchData) {p : ℕ} {a : ℤ}
    (ha : d.alpha=IsingBulk.PrimeFamily.angle p a) {N : ℕ} (hN : 0<N) (l : ℤ) :
    primeBranch p a^N=
      Complex.exp (-(N:ℂ)*(preferredShellMean d N l:ℂ)*Complex.I) := by
  have hNc : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
  have he : -(N:ℂ)*(preferredShellMean d N l:ℂ)*Complex.I =
      (N:ℂ)*(-(d.b:ℂ)*Complex.I)+((-l:ℤ):ℂ)*(2*Real.pi*Complex.I) := by
    unfold preferredShellMean
    push_cast
    field_simp
    ring
  rw [he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one,
    preferred_prime_branch_formula d ha,Complex.exp_nat_mul]

theorem preferred_prime_branch_power_mean_bound (d : PreferredBranchData) {p : ℕ} {a : ℤ}
    (ha : d.alpha=IsingBulk.PrimeFamily.angle p a) {N : ℕ} (hN : 0<N) (l : ℤ) :
    ‖1-primeBranch p a^N‖≤(N:ℝ)*|preferredShellMean d N l| := by
  calc
    _ = ‖Complex.exp (Complex.I*((-(N:ℝ)*preferredShellMean d N l:ℝ):ℂ))-1‖ := by
      rw [preferred_prime_branch_power_mean d ha hN l,norm_sub_rev]
      congr 2
      push_cast
      ring
    _ ≤ ‖-(N:ℝ)*preferredShellMean d N l‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg N)]

/-- One genuine positive gap works for all constrained means in a fixed
finite block, including every integer mean label, with no angular truncation. -/
theorem preferred_finite_mean_separation (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) {M : ℕ} (hM : 0<M) :
    ∃ r₀ : ℝ, 0<r₀ ∧ ∀ N : ℕ, 1≤N → N≤M → ∀ l : ℤ,
      r₀≤|preferredShellMean d N l| := by
  obtain ⟨δ,hδ,hsep⟩ := prime_branch_finite_separation hp ha M
  have hMr : 0<(M:ℝ) := by exact_mod_cast hM
  refine ⟨δ/M,div_pos hδ hMr,?_⟩
  intro N hN hNM l
  apply (div_le_iff₀ hMr).mpr
  have hn : (N:ℝ)≤M := by exact_mod_cast hNM
  have h := (hsep N hN hNM).trans
    (preferred_prime_branch_power_mean_bound d hα (by omega) l)
  nlinarith [mul_le_mul_of_nonneg_right hn (abs_nonneg (preferredShellMean d N l))]

/-- On every sufficiently small shell in the fixed finite particle block,
the actual right-support coordinates are uniformly on the positive side of
the branch. This is the manuscript's finite-block mean-gap choice. -/
theorem preferred_finite_small_shell_away_branch (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) {M : ℕ} (hM : 0<M) :
    ∃ g : ℝ, 0<g ∧ ∀ B : PreferredCoareaBump d, ∀ n : ℕ, n+1≤M →
      ∀ δB r : ℝ, δB≤g/4 → 0<r → r≤g/8 → ∀ l : ℤ, ∀ i j : Fin (n+1),
      ∀ θ : Fin n → ℝ, θ∈preferredRightShell d B δB r l i j →
      ∀ v : Fin (n+1),
        g/2≤preferredLiftedAngles B.delta (constrainedAngles θ) v+d.b := by
  obtain ⟨g,hg,hsep⟩ := preferred_finite_mean_separation d hp ha hα hM
  refine ⟨g,hg,?_⟩
  intro B n hNM δB r hδ _hr hr l i j θ hθ
  have hw := preferredRightShell_window d B hθ
  have h0 := (hθ.2.1 (0:Fin (n+1))).1
  have h0w := (hw 0).2
  have ht : g≤preferredShellMean d (n+1) l := by
    rcases le_abs.mp (hsep (n+1) (by omega) hNM l) with ht | ht
    · exact ht
    · linarith
  intro v
  have hv := (hw v).1
  linarith

end
end IsingBulk.Preferred22
