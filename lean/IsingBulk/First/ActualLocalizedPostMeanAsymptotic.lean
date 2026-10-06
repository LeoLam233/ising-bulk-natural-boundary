import IsingBulk.First.ActualPostMeanInterchange

/-! Source-order asymptotics for the derivative of the actual fixed-cutoff
post-mean shape integral, with derivative/integral interchange proved. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex Filter
open scoped Topology

theorem actual_localized_postMean_source_asymptotic {n : ℕ} (hn : 1 ≤ n)
    (a : OrderedChartData) (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    let k := (n+1)^2/2-1
    localLeadingCoefficient a n k ≠ 0 ∧
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => (deriv^[k] (localizedPostMeanIntegral a chi)) (radialParameter a.theta epsilon)-
          ((Real.sqrt epsilon:ℂ)⁻¹)*localLeadingCoefficient a n k)
        (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) := by
  dsimp only
  have hdegree := source_shape_radial_exponent hn he
  have hk : 1 ≤ (n+1)^2/2-1 := by
    have hp : 2 ≤ (n+1)*n := by
      have h := Nat.mul_le_mul (show 2 ≤ n+1 by omega) hn
      simpa using h
    omega
  refine ⟨localLeadingCoefficient_ne_zero a hn he,?_⟩
  obtain ⟨Rl,hRl,hL⟩ := actual_postMean_coordinate_sqrt_limit hn hk hdegree a he ha hb
  obtain ⟨Ri,hRi,hI⟩ := actual_postMean_integral_interchange (n := n) a ha hb
  refine ⟨min Rl Ri,lt_min hRl hRi,?_⟩
  intro chi hchi hchi0 hchib hchis
  have ht := hL chi hchi hchi0 hchib (fun x hx => (hchis x hx).trans_le (min_le_left _ _))
  apply normalized_sqrt_limit_isLittleO
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hRi).filter_mono nhdsWithin_le_nhds] with epsilon he heRi
  rw [hI epsilon he heRi chi hchi (fun x hx => (hchis x hx).trans_le (min_le_right _ _))]

end
end IsingBulk.First
