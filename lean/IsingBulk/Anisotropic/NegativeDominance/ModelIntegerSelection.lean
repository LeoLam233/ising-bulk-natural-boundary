import IsingBulk.Anisotropic.NegativeDominance.ModelBalanceDerivative
import IsingBulk.Anisotropic.NegativeDominance.IntegerRounding

/-! Genuine integer-order selection for the exact model, retaining all
factors. The coarse bracket is Θ(n² log n), with imbalance O(1/n). -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set

theorem exists_integer_model_balance
    (B R H : ℕ → ℂ) (B0 : ℂ) (s C : ℝ) (n p : ℕ)
    (hn : 2 ≤ n) (hp : 0 < p) (hpn : 2*p ≤ n) (hpi : Real.pi^2 ≤ (n : ℝ))
    (hnodd : Odd n) (hC : 0 ≤ C) (hs : s ≠ 0)
    (hscale : max 64 (2*(2*|modelQuadraticConstant B0 s|+14+2*C)+2) ≤ Real.log (n : ℝ))
    (hupper : 32*Real.log (n : ℝ) ≤ n)
    (hgood : ∀ k ≥ n, Odd k → B k ≠ 0 ∧ R k ≠ 0 ∧ H k ≠ 0 ∧ (R k)^2 = B k)
    (herr : ∀ k ≥ n, Odd k → |modelAnalyticError B0 (B k) (H k) k| ≤ C) :
    ∃ j : ℕ, lowerCrossingOrder n-1 < (j : ℝ) ∧ (j : ℝ) ≤ upperCrossingOrder n ∧
      alpha (n+2*p) < j ∧
      |Real.log ‖model (B (n+2*p)) (R (n+2*p)) (H (n+2*p)) s (n+2*p) j‖-
        Real.log ‖model (B n) (R n) (H n) s n j‖| ≤ 8*(p : ℝ)/(n : ℝ) := by
  have hl64 := (le_max_left _ _).trans hscale
  obtain ⟨_, hnL, hLH, _⟩ := crossing_order_range n p hn hpn hnodd hl64 hupper
  have hsign := modelLogReal_crossing_signs B R H B0 s C n p hn hp hpn hpi hnodd hC hs
    hscale hupper hgood herr
  change modelBalance B R H s n p (lowerCrossingOrder n) < 0 ∧
    0 < modelBalance B R H s n p (upperCrossingOrder n) at hsign
  have hd (j : ℝ) (hj : lowerCrossingOrder n-1 ≤ j) :=
    modelBalance_deriv_bound B R H s n p hn hp hpn hpi hnodd hl64 j hj
  have hc : ContinuousOn (modelBalance B R H s n p) (Icc (lowerCrossingOrder n) (upperCrossingOrder n)) := by
    intro j hj
    exact (hasDerivAt_modelBalance B R H s n p hnodd j (hd j (by linarith [hj.1])).1).continuousAt.continuousWithinAt
  obtain ⟨j, hjL, hjH, hjbal⟩ := exists_nat_balanced_of_sign_change
    (modelBalance B R H s n p) (deriv (modelBalance B R H s n p))
    (le_trans (by positivity : (0 : ℝ) ≤ n) hnL) hLH hc hsign.1.le hsign.2.le
    (show 0 ≤ 8*(p : ℝ)/(n : ℝ) by positivity)
    (fun x hx => (hasDerivAt_modelBalance B R H s n p hnodd x (hd x hx.1).1).differentiableAt.hasDerivAt.hasDerivWithinAt)
    (fun x hx => (hd x hx.1).2)
  have hjA : alpha (n+2*p) < j := by exact_mod_cast (hd j hjL.le).1
  have ha := alpha_even_step n p hnodd
  have hjn : alpha n < j := by omega
  have ho : Odd (n+2*p) := by obtain ⟨k, rfl⟩ := hnodd; exact ⟨k+p, by ring⟩
  have hg0 := hgood n le_rfl hnodd
  have hg1 := hgood (n+2*p) (by omega) ho
  unfold modelBalance at hjbal
  rw [modelLogReal_nat _ _ _ _ _ _ (by omega) hjA hg1.1 hg1.2.1 hg1.2.2.1 hs,
    modelLogReal_nat _ _ _ _ _ _ (by omega) hjn hg0.1 hg0.2.1 hg0.2.2.1 hs] at hjbal
  exact ⟨j, hjL, hjH, hjA, hjbal⟩

end
end IsingBulk.Anisotropic.NegativeDominance
