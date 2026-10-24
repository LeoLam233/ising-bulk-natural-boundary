import IsingBulk.Anisotropic.NegativeDominance.CollisionDensity
import IsingBulk.Anisotropic.NegativeNormalForm.ShapePeriodExact

/-! Exact algebraic normalization of the two central residues and beta period.
This remains separate from identifying the actual full winding coefficients. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First

theorem two_rpow_alpha (a : ℕ) : (2 : ℝ) ^ (2 - (a : ℝ)) = 4 / 2^a := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
  norm_num

theorem particle_rpow_alpha (n a : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ ((a : ℝ) - 3 / 2) = (n : ℝ)^a / ((n : ℝ)*Real.sqrt n) := by
  have h : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_sub h, Real.rpow_natCast]
  congr 1
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem odd_pi_rpow (n : ℕ) (hn : Odd n) :
    Real.pi ^ (((n : ℝ)-1)/2) = Real.pi ^ ((n-1)/2) := by
  obtain ⟨k, rfl⟩ := hn
  have he : ((2*k+1 : ℕ)-1)/2 = k := by omega
  rw [he]
  have hc : (((2*k+1 : ℕ) : ℝ)-1)/2 = (k : ℝ) := by push_cast; ring
  rw [hc, Real.rpow_natCast]

theorem period_scalar_normalization (n : ℕ) (hn : Odd n) (hn3 : 3 ≤ n) :
    2 * (-2 : ℝ) /
      ((n : ℝ)*(n.factorial : ℝ)*(2*Real.pi)^(n-1)*2^(n*(n-1))) *
      ((n.factorial : ℝ)*Real.pi^((n-1)/2)*factorialProduct n/Real.sqrt n) *
      (2*(n : ℝ))^(alpha n) =
    -(2 : ℝ)^(2-(alpha n : ℝ))*factorialProduct n*
      (n : ℝ)^((alpha n : ℝ)-3/2) / Real.pi^(((n : ℝ)-1)/2) := by
  rw [two_rpow_alpha, particle_rpow_alpha n (alpha n) (by omega), odd_pi_rpow n hn]
  have he : n-1+n*(n-1) = alpha n + alpha n := by
    have ha := two_mul_alpha_add_one n hn
    have hn1 : 1 ≤ n := by omega
    have h : n*(n-1) = n*n-n := by simp [Nat.mul_sub_left_distrib]
    have hh : n ≤ n*n := by nlinarith
    omega
  have hp : n-1 = (n-1)/2+(n-1)/2 := by obtain ⟨k, rfl⟩ := hn; omega
  have htwo : (2 : ℝ)^(n-1)*2^(n*(n-1)) = 2^(alpha n)*2^(alpha n) := by
    rw [← pow_add, he, pow_add]
  have hpi : Real.pi^(n-1) = Real.pi^((n-1)/2)*Real.pi^((n-1)/2) := by
    rw [← pow_add, ← hp]
  rw [mul_pow, mul_pow]
  rw [hpi]
  have hnz : (n : ℝ) ≠ 0 := by positivity
  have hfn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hpz := Real.pi_ne_zero
  field_simp
  linear_combination 4 * factorialProduct n * htwo

/-- The two normalized central residues times the actual constrained period
are exactly M(n,j). This algebra does not identify the complete winding jets. -/
theorem central_period_eq_model (Bn rootBn H : ℂ) (s : ℝ)
    {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n) (j : ℕ) (haj : alpha n ≤ j) :
    2 * centralDensity Bn rootBn s n * H^(-(alpha n : ℤ)) *
      shapePeriod (n-1) j (tau n) ((1/(2*(n : ℝ)) : ℝ) : ℂ) =
      model Bn rootBn H s n j := by
  rw [negativeEdge_exact_period hn hn3 j haj]
  let K : ℝ := 2 * (-2 : ℝ) /
    ((n : ℝ)*(n.factorial : ℝ)*(2*Real.pi)^(n-1)*2^(n*(n-1))) *
    ((n.factorial : ℝ)*Real.pi^((n-1)/2)*factorialProduct n/Real.sqrt n) *
    (2*(n : ℝ))^(alpha n)
  have hK : K = -(2 : ℝ)^(2-(alpha n : ℝ))*factorialProduct n*
      (n : ℝ)^((alpha n : ℝ)-3/2) / Real.pi^(((n : ℝ)-1)/2) :=
    period_scalar_normalization n hn hn3
  have ht : (alpha n : ℤ) - j - 1 = -((j+1-alpha n : ℕ) : ℤ) := by omega
  calc
    _ = (K : ℂ) * (Bn^alpha n/rootBn) / (s : ℂ)^(2*alpha n) *
        H^(-(alpha n : ℤ)) / (tau n : ℂ)^(j+1-alpha n) *
        ((Real.Gamma ((j : ℝ)+1-alpha n)/Real.Gamma ((j : ℝ)+1) : ℝ) : ℂ) := by
      dsimp [centralDensity, K]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [hK]
      unfold model
      rw [ht]
      simp only [zpow_neg, zpow_natCast, Real.rpow_eq_pow]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Full actual central residue and actual constrained period, with the exact
physical factors. The omitted step is control of noncentral density/Jacobian
and analytic remainder in each actual winding coefficient. -/
theorem regularResidue_period_eq_model {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (B rootB : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hd : 1 - Complex.cos d = (tau n : ℂ))
    (hB : AnalyticAt ℂ B (tau n)) (T : Config n → ℂ) (hT : T 0 = (tau n : ℂ))
    (hBn : B (tau n) ≠ 0) (hr : rootB (tau n) ≠ 0)
    (hsq : rootB (tau n)^2 = B (tau n)) (H : ℂ)
    (j : ℕ) (haj : alpha n ≤ j) :
    2 * regularResidue B rootB phi hphi d T 0 * H^(-(alpha n : ℤ)) *
      shapePeriod (n-1) j (tau n) ((1/(2*(n : ℝ)) : ℝ) : ℂ) =
      model (B (tau n)) (rootB (tau n)) H (Real.sin phi) n j := by
  rw [regularResidue_center_normalized hn B rootB phi hphi d
    (hd.symm ▸ hB) T (hT.trans hd.symm) (hd.symm ▸ hBn) (hd.symm ▸ hr)
    (hd.symm ▸ hsq), hd]
  exact central_period_eq_model _ _ _ _ hn hn3 j haj

end
end IsingBulk.Anisotropic.NegativeDominance
