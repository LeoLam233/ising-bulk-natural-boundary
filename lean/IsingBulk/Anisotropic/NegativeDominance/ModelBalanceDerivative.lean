import IsingBulk.Anisotropic.NegativeDominance.OrderCrossingSigns
import IsingBulk.Anisotropic.NegativeDominance.OrderBalance

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

def modelBalance (B R H : ℕ → ℂ) (s : ℝ) (n p : ℕ) (j : ℝ) : ℝ :=
  modelLogReal (B (n+2*p)) (R (n+2*p)) (H (n+2*p)) s (n+2*p) j -
    modelLogReal (B n) (R n) (H n) s n j

theorem modelBalance_eq_orderBalance (B R H : ℕ → ℂ) (s : ℝ) (n p : ℕ) (ho : Odd n) :
    modelBalance B R H s n p = orderBalance
      (modelOrderConstant (B (n+2*p)) (R (n+2*p)) (H (n+2*p)) s (n+2*p)-
        modelOrderConstant (B n) (R n) (H n) s n)
      (Real.log (tau n)-Real.log (tau (n+2*p))) (alpha n) (2*p*n+2*p^2) := by
  funext j
  unfold modelBalance modelLogReal orderBalance
  have ha := alpha_even_step n p ho
  rw [Nat.add_assoc] at ha
  rw [ha]
  ring

theorem hasDerivAt_modelBalance (B R H : ℕ → ℂ) (s : ℝ) (n p : ℕ) (ho : Odd n)
    (j : ℝ) (hj : (alpha (n+2*p) : ℝ) < j) :
    HasDerivAt (modelBalance B R H s n p)
      (Real.log (tau n)-Real.log (tau (n+2*p))-
        ∑ k ∈ Finset.range (2*p*n+2*p^2), (j-((alpha n+k : ℕ) : ℝ))⁻¹) j := by
  rw [modelBalance_eq_orderBalance B R H s n p ho]
  apply hasDerivAt_orderBalance
  have ha := alpha_even_step n p ho
  rw [Nat.add_assoc] at ha
  rwa [← ha]

theorem modelBalance_deriv_bound (B R H : ℕ → ℂ) (s : ℝ) (n p : ℕ)
    (hn : 2 ≤ n) (hp : 0 < p) (hpn : 2*p ≤ n) (hpi : Real.pi^2 ≤ (n : ℝ))
    (ho : Odd n) (hscale : 64 ≤ Real.log (n : ℝ))
    (j : ℝ) (hj : lowerCrossingOrder n-1 ≤ j) :
    (alpha (n+2*p) : ℝ) < j ∧ ‖deriv (modelBalance B R H s n p) j‖ ≤ 8*(p : ℝ)/(n : ℝ) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpn' : 2*(p : ℝ) ≤ n := by exact_mod_cast hpn
  have ho' : Odd (n+2*p) := by obtain ⟨k, rfl⟩ := ho; exact ⟨k+p, by ring⟩
  have ha := alpha_even_step n p ho
  rw [Nat.add_assoc] at ha
  have ha2 := two_mul_alpha_add_one (n+2*p) ho'
  have har : 2*(alpha (n+2*p) : ℝ)+1=((n : ℝ)+2*p)^2 := by
    exact_mod_cast (ha2.trans (pow_two (n+2*p)).symm)
  have hlow := mul_le_mul_of_nonneg_left hscale (sq_nonneg (n : ℝ))
  dsimp [lowerCrossingOrder] at hj
  have hjsq : (n : ℝ)^2 ≤ j := by nlinarith only [hlow, hj, hn2]
  have hjA : 2*(alpha (n+2*p) : ℝ) ≤ j := by nlinarith [hlow, hj]
  have hApos : 0 < (alpha (n+2*p) : ℝ) := by nlinarith only [har, hn2, hp1]
  have hj' : (alpha (n+2*p) : ℝ) < j := by linarith only [hjA, hApos]
  refine ⟨hj', ?_⟩
  rw [(hasDerivAt_modelBalance B R H s n p ho j hj').deriv, Real.norm_eq_abs]
  push_cast
  have hs := reciprocal_order_sum_bounds (alpha n) (2*p*n+2*p^2) j (by rw [← ha]; exact hj')
  rw [← ha] at hs
  push_cast at hs
  have hb : 2*(p : ℝ)*n+2*(p : ℝ)^2 ≤ 4*(p : ℝ)*n := by nlinarith only [hpn', hp1]
  have hfrac : (2*(p : ℝ)*n+2*(p : ℝ)^2)/(j-(alpha (n+2*p) : ℝ)) ≤ 8*(p : ℝ)/(n : ℝ) := by
    apply (div_le_div_iff₀ (by linarith only [hj']) hn0).2
    have h1 := mul_le_mul_of_nonneg_right hb hn0.le
    have h2 := mul_le_mul_of_nonneg_left (show (n : ℝ)^2 ≤ 2*(j-(alpha (n+2*p) : ℝ)) by linarith only [hjsq, hjA])
      (show 0 ≤ 4*(p : ℝ) by positivity)
    nlinarith only [h1, h2]
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (2*p*n+2*p^2), (j-((alpha n : ℝ)+k))⁻¹ := by
    have hbase : 0 ≤ (2*(p : ℝ)*n+2*(p : ℝ)^2)/j :=
      div_nonneg (by positivity) (by linarith only [hj', hApos])
    exact hbase.trans hs.1
  have ht := log_tau_step_comparable n (2*p) hn (by omega) hpn hpi
  push_cast at ht
  have ht0 : 0 ≤ Real.log (tau n)-Real.log (tau (n+2*p)) :=
    (div_nonneg (by positivity) (by positivity)).trans ht.1
  have htupper : 3*(2*(p : ℝ))/(n : ℝ) ≤ 8*(p : ℝ)/(n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hn0.le
    linarith
  apply abs_le.mpr
  constructor <;> linarith only [ht0, ht.2, htupper, hs.2, hfrac, hsum0]

end
end IsingBulk.Anisotropic.NegativeDominance
