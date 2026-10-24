import IsingBulk.Anisotropic.NegativeDominance.RealOrderDecomposition
import IsingBulk.Anisotropic.NegativeDominance.EntropyFirstDifference
import IsingBulk.Anisotropic.NegativeDominance.TauFirstDifference
import IsingBulk.Anisotropic.NegativeDominance.GammaFirstDifference

/-! Explicit first-difference bounds on the exact real-order model.
Every Gamma, scalar, factorial and distance error is retained. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem modelLogReal_step_bounds
    (B R H : ℕ → ℂ) (B0 : ℂ) (s C : ℝ) (n p : ℕ) (j : ℝ)
    (hn : 2 ≤ n) (hnodd : Odd n) (hj : (alpha (n+2*p) : ℝ) < j) (hs : s ≠ 0)
    (hgood : ∀ k ≥ n, Odd k → B k ≠ 0 ∧ R k ≠ 0 ∧ H k ≠ 0 ∧ (R k)^2 = B k)
    (herr : ∀ k ≥ n, Odd k → |modelAnalyticError B0 (B k) (H k) k| ≤ C) :
    let d : ℝ := 2*p;
    let b : ℝ := 2*p*n+2*(p : ℝ)^2;
    let A : ℝ := alpha (n+2*p);
    let F := modelLogReal (B (n+2*p)) (R (n+2*p)) (H (n+2*p)) s (n+2*p) j -
      modelLogReal (B n) (R n) (H n) s n j;
    -5*d*((n : ℝ)+d)+b*(modelQuadraticConstant B0 s-Real.log j)+
      j*(2*d/((n : ℝ)+d)-Real.pi^2/(10*(n : ℝ)^2))-
      d/2*Real.log Real.pi-2*C ≤ F ∧
    F ≤ b*(modelQuadraticConstant B0 s-Real.log j)+
      j*(2*d/(n : ℝ)+Real.pi^2/(10*((n : ℝ)+d)^2))-
      d/2*Real.log Real.pi+2*C+b*A/(j-A) := by
  dsimp
  have ho : Odd (n+2*p) := by obtain ⟨k, rfl⟩ := hnodd; exact ⟨k+p, by ring⟩
  have ha := alpha_even_step n p hnodd
  rw [Nat.add_assoc] at ha
  have har : (alpha (n+2*p) : ℝ) = alpha n+(2*p*n+2*(p : ℝ)^2) := by
    exact_mod_cast ha
  have hj0 : (alpha n : ℝ) < j := by nlinarith
  have hjpos : 0 ≤ j := le_trans (by positivity) hj.le
  have hdec (k : ℕ) (hk : n ≤ k) (hok : Odd k) (hkj : (alpha k : ℝ) < j) :=
    modelLogReal_decomposition B0 (B k) (R k) (H k) s k j (by omega) hok hkj
      (hgood k hk hok).1 (hgood k hk hok).2.1 (hgood k hk hok).2.2.1 hs
      (hgood k hk hok).2.2.2
  rw [hdec (n+2*p) (by omega) ho hj, hdec n le_rfl hnodd hj0]
  have he := entropyPart_step_bounds n (2*p) hn
  have ht := log_tau_step_bounds n (2*p) hn
  have hg := gammaCorrection_step_bounds (alpha n) (2*p*n+2*p^2) j
    (by rw [← ha]; exact hj)
  rw [← ha] at hg
  have hE0 := abs_le.mp (herr n le_rfl hnodd)
  have hE1 := abs_le.mp (herr (n+2*p) (by omega) ho)
  have htl := mul_le_mul_of_nonneg_left ht.1 hjpos
  have htu := mul_le_mul_of_nonneg_left ht.2 hjpos
  have hqa := congrArg (fun x : ℝ => x*(modelQuadraticConstant B0 s-Real.log j)) har
  push_cast at he hg htl htu hqa ⊢
  constructor <;> nlinarith [he.1, he.2, hg.1, hg.2, hE0.1, hE0.2, hE1.1, hE1.2]

end
end IsingBulk.Anisotropic.NegativeDominance
