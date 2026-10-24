import IsingBulk.Anisotropic.NegativeDominance.OrderCrossingBounds
import IsingBulk.Anisotropic.NegativeDominance.CrossingScalar

/-! Coarse but uniform real-order bounds derived from all exact model factors. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem modelLogReal_coarse_bounds
    (B R H : ℕ → ℂ) (B0 : ℂ) (s C : ℝ) (n p : ℕ) (j : ℝ)
    (hn : 2 ≤ n) (hp : 0 < p) (hpn : 2*p ≤ n) (hpi : Real.pi^2 ≤ (n : ℝ))
    (hnodd : Odd n) (hj : 2*(alpha (n+2*p) : ℝ) ≤ j) (hC : 0 ≤ C) (hs : s ≠ 0)
    (hgood : ∀ k ≥ n, Odd k → B k ≠ 0 ∧ R k ≠ 0 ∧ H k ≠ 0 ∧ (R k)^2 = B k)
    (herr : ∀ k ≥ n, Odd k → |modelAnalyticError B0 (B k) (H k) k| ≤ C) :
    let X : ℝ := 2*p*n;
    let K := 2*|modelQuadraticConstant B0 s|+14+2*C;
    let F := modelLogReal (B (n+2*p)) (R (n+2*p)) (H (n+2*p)) s (n+2*p) j -
      modelLogReal (B n) (R n) (H n) s n j;
    X*(-2*Real.log j+j/(2*(n : ℝ)^2)-K) ≤ F ∧
      F ≤ X*(-Real.log j+3*j/(n : ℝ)^2+K) := by
  have ho : Odd (n+2*p) := by obtain ⟨k, rfl⟩ := hnodd; exact ⟨k+p, by ring⟩
  have ha := alpha_even_step n p hnodd
  rw [Nat.add_assoc] at ha
  have har : (alpha (n+2*p) : ℝ) = alpha n+(2*p*n+2*(p : ℝ)^2) := by exact_mod_cast ha
  have hn0 : (0 : ℝ) < n := by positivity
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpn' : 2*(p : ℝ) ≤ n := by exact_mod_cast hpn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : 0 < (alpha (n+2*p) : ℝ) := by nlinarith [show (0 : ℝ) ≤ alpha n by positivity]
  have hj' : (alpha (n+2*p) : ℝ) < j := by linarith
  have hj0 : (alpha n : ℝ) < j := by nlinarith
  have hj1 : 1 ≤ j := by nlinarith [show (0 : ℝ) ≤ alpha n by positivity]
  have hdec (k : ℕ) (hk : n ≤ k) (hok : Odd k) (hkj : (alpha k : ℝ) < j) :=
    modelLogReal_decomposition B0 (B k) (R k) (H k) s k j (by omega) hok hkj
      (hgood k hk hok).1 (hgood k hk hok).2.1 (hgood k hk hok).2.2.1 hs
      (hgood k hk hok).2.2.2
  dsimp
  rw [hdec (n+2*p) (by omega) ho hj', hdec n le_rfl hnodd hj0]
  let X : ℝ := 2*p*n
  let b : ℝ := 2*p*n+2*(p : ℝ)^2
  have hX : 1 ≤ X := by dsimp [X]; nlinarith
  have hb : X ≤ b ∧ b ≤ 2*X := by dsimp [X, b]; constructor <;> nlinarith
  have he := entropyPart_step_bounds n (2*p) hn
  push_cast at he
  have hE : -10*X ≤ entropyPart (n+2*p)-entropyPart n ∧
      entropyPart (n+2*p)-entropyPart n ≤ 0 := by
    dsimp [X]
    constructor
    · nlinarith [he.1]
    · exact he.2
  have ht := log_tau_step_comparable n (2*p) hn (by omega) hpn hpi
  have htl := mul_le_mul_of_nonneg_left ht.1 (show 0 ≤ j by linarith)
  have htu := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ j by linarith)
  push_cast at htl htu
  have hTe1 : X*(j/(n : ℝ)^2)/2 = j*((2*(p : ℝ))/(2*(n : ℝ))) := by
    dsimp [X]; field_simp
  have hTe2 : 3*X*(j/(n : ℝ)^2) = j*(3*(2*(p : ℝ))/(n : ℝ)) := by
    dsimp [X]; field_simp
  have hT : X*(j/(n : ℝ)^2)/2 ≤ j*(Real.log (tau n)-Real.log (tau (n+2*p))) ∧
      j*(Real.log (tau n)-Real.log (tau (n+2*p))) ≤ 3*X*(j/(n : ℝ)^2) := by
    rw [hTe1, hTe2]
    exact ⟨htl, htu⟩
  have hg := gammaCorrection_step_bounds (alpha n) (2*p*n+2*p^2) j (by rw [← ha]; exact hj')
  rw [← ha] at hg
  push_cast at hg
  have hG : 0 ≤ gammaCorrection (alpha (n+2*p)) j-gammaCorrection (alpha n) j ∧
      gammaCorrection (alpha (n+2*p)) j-gammaCorrection (alpha n) j ≤ b := by
    refine ⟨hg.1, hg.2.trans ?_⟩
    dsimp [b]
    apply (div_le_iff₀ (by linarith : 0 < j-(alpha (n+2*p) : ℝ))).2
    have hb0 : 0 ≤ 2*(p : ℝ)*n+2*(p : ℝ)^2 := by positivity
    nlinarith [mul_nonneg hb0 (show 0 ≤ j-2*(alpha (n+2*p) : ℝ) by linarith)]
  have hlogpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogpi3 : Real.log Real.pi ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_four]
  have hP : -2*X ≤ -(2*(p : ℝ)/2*Real.log Real.pi) ∧
      -(2*(p : ℝ)/2*Real.log Real.pi) ≤ 0 := by
    dsimp [X]
    have hp0 : (0 : ℝ) ≤ p := by positivity
    have h1 := mul_le_mul_of_nonneg_left hn2 hp0
    have h2 := mul_le_mul_of_nonneg_left hlogpi3 hp0
    have h3 := mul_nonneg hp0 hlogpi0
    constructor <;> nlinarith only [h1, h2, h3, hp0]
  have hE0 := abs_le.mp (herr n le_rfl hnodd)
  have hE1 := abs_le.mp (herr (n+2*p) (by omega) ho)
  have hR : -2*C ≤ modelAnalyticError B0 (B (n+2*p)) (H (n+2*p)) (n+2*p)-
      modelAnalyticError B0 (B n) (H n) n ∧
      modelAnalyticError B0 (B (n+2*p)) (H (n+2*p)) (n+2*p)-
      modelAnalyticError B0 (B n) (H n) n ≤ 2*C := by constructor <;> linarith only [hE0.1, hE0.2, hE1.1, hE1.2]
  have hc := crossing_components_bounds X b (modelQuadraticConstant B0 s) (Real.log j)
    (j/(n : ℝ)^2) C _ _ _ _ _ hX hC (Real.log_nonneg hj1) hb hE hT hG hP hR
  have hqa := congrArg (fun x : ℝ => x*(modelQuadraticConstant B0 s-Real.log j)) har
  dsimp [X, b] at hc
  push_cast at hqa ⊢
  have hu : j/(2*(n : ℝ)^2) = (j/(n : ℝ)^2)/2 := by ring
  rw [hu]
  simp only [mul_div_assoc] at hc ⊢
  constructor <;> nlinarith only [hc.1, hc.2, hqa]

end
end IsingBulk.Anisotropic.NegativeDominance
