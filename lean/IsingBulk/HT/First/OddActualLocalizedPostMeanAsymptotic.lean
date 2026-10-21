import IsingBulk.First.ActualPostMeanInterchange
import IsingBulk.HT.First.OddActualPostMeanCoordinateLimit

/-! Source-order asymptotics for the derivative of the actual fixed-cutoff
post-mean shape integral, with derivative/integral interchange proved. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.Branch Complex Filter IsingBulk.First
open scoped Topology

theorem actual_localized_postMean_odd_asymptotic {n : ℕ} (hn : 1 ≤ n)
    (a : OrderedChartData) (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    let k := derivativeOrder (n+1);
    -I*localLeadingCoefficient a n k ≠ 0 ∧
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => (deriv^[k] (localizedPostMeanIntegral a chi)) (radialParameter a.theta epsilon)-
          ((epsilon:ℂ)⁻¹)*(-I*localLeadingCoefficient a n k))
        (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  have hp3 : 3 ≤ n+1 := by
    obtain ⟨m,hm⟩ := ho
    omega
  have hdegree : n-1+(n+1)*n = 2*derivativeOrder (n+1)-1 := by
    simpa only [Nat.add_sub_cancel] using odd_shape_radial_exponent ho hp3
  have hk := derivativeOrder_pos ho hp3
  refine ⟨?_,?_⟩
  · simpa only [oddLocalLeadingCoefficient,Nat.add_sub_cancel] using
      oddLocalLeadingCoefficient_ne_zero a ho hp3
  · obtain ⟨Rl,hRl,hL⟩ := actual_postMean_coordinate_epsilon_limit hn hk hdegree a ho ha hb
    obtain ⟨Ri,hRi,hI⟩ := actual_postMean_integral_interchange (n := n) a ha hb
    refine ⟨min Rl Ri,lt_min hRl hRi,?_⟩
    intro chi hchi hchi0 hchib hchis
    have ht := hL chi hchi hchi0 hchib (fun x hx => (hchis x hx).trans_le (min_le_left _ _))
    apply normalized_epsilon_limit_isLittleO
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hRi).filter_mono nhdsWithin_le_nhds] with epsilon he heRi
    rw [hI epsilon he heRi chi hchi (fun x hx => (hchis x hx).trans_le (min_le_right _ _))]
end
end IsingBulk.HT.First
