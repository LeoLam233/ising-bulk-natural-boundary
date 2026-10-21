import IsingBulk.First.RegularIntegratedMean
import IsingBulk.HT.First.RegularOddShapeAsymptotic
import IsingBulk.HT.First.RegularOddCoefficient
import IsingBulk.First.SourceAsymptoticAttachment

/-! Fixed-cutoff integration of the actual regular-chart source.
Holomorphy, absolute integrability and every parameter interchange are proved
from the physical analytic neighborhood, before varying the radial parameter. -/
namespace IsingBulk.HT.First.Regular
noncomputable section
open Complex MeasureTheory Filter Set Metric IsingBulk.Branch IsingBulk.First IsingBulk.First.Regular
open scoped Topology BigOperators

theorem actual_postMean_coordinate_epsilon_limit {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hdegree : n-1+(n+1)*n = 2*k-1) (a : RegularChartData) (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => epsilon • localizedPostMeanDerivativeIntegral a k chi epsilon)
        (𝓝[>] 0) (𝓝 (-I*localLeadingCoefficient a n k)) := by
  obtain ⟨R,hR,h⟩ := actual_postMean_shape_epsilon_limit hn hk hdegree a ho ha hb
  refine ⟨R,hR,?_⟩
  intro chi hchi hchi0 hchib hchis
  have ht := (h chi hchi hchi0 hchib hchis).const_smul (Real.sqrt (n+1))⁻¹
  convert ht using 1
  · funext epsilon
    have hi := integral_shapeExtend n (fun x => chi x*intrinsicPostMeanDerivative a k epsilon x)
    have hid : localizedPostMeanDerivativeIntegral a k chi epsilon =
        (Real.sqrt (n+1))⁻¹ • ∫ x : ShapeSpace n, chi x*intrinsicPostMeanDerivative a k epsilon x := by
      simpa only [IsingBulk.First.Regular.localizedPostMeanDerivativeIntegral,
        IsingBulk.First.Regular.intrinsicPostMeanDerivative,
        intrinsicShapeCoordinates_shapeCoordinateEquiv] using hi
    rw [hid, smul_comm]
  · congr 1
    rw [localLeadingCoefficient, shapePeriod_eq_intrinsic]
    simp only [Complex.real_smul, ofReal_mul, ofReal_ofNat]
    ring

theorem actual_localized_postMean_odd_asymptotic {n : ℕ} (hn : 1 ≤ n)
    (a : RegularChartData) (ho : Odd (n+1))
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

theorem actual_local_mean_odd_asymptotic {n : ℕ} (hn : 1 ≤ n)
    (a : RegularChartData) (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    let k := derivativeOrder (n+1);
    -I*localLeadingCoefficient a n k ≠ 0 ∧
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ R : ℝ, 0 < R ∧ ∀ eta : ℝ → ℂ, Continuous eta →
        (∀ v : ℝ, |v| ≤ delta → eta v=1) →
        ∀ chi : ShapeSpace n → ℂ, Continuous chi → chi 0=1 → (∀ x, ‖chi x‖ ≤ 1) →
          (∀ x, chi x ≠ 0 → ‖x‖ < R) →
          Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
            (fun epsilon => (deriv^[k] (localizedSmoothMeanIntegral a chi eta
              (-(Real.sin a.theta/4)*epsilon) delta)) (radialParameter a.theta epsilon)-
              ((epsilon:ℂ)⁻¹)*(-I*localLeadingCoefficient a n k))
            (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  obtain ⟨hL,Rp,hRp,hP⟩ := actual_localized_postMean_odd_asymptotic hn a ho ha hb
  refine ⟨hL,?_⟩
  obtain ⟨Dd,hDd,hD⟩ := actual_integrated_mean_derivative_decomposition (n := n) a ha hb
  obtain ⟨De,hDe,hE⟩ := actual_mean_error_shape_sqrt_limit (n := n) a ha hb
  refine ⟨min Dd De,lt_min hDd hDe,?_⟩
  intro delta hd hdD
  obtain ⟨Rd,epsilon₀,hRd,he0,hDec⟩ := hD delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨Re,hRe,hErr⟩ := hE delta hd (hdD.trans (min_le_right _ _))
  let R := min Rp (min Rd Re)
  have hR : 0 < R := lt_min hRp (lt_min hRd hRe)
  have hRRp : R ≤ Rp := min_le_left _ _
  have hRRd : R ≤ Rd := (min_le_right _ _).trans (min_le_left _ _)
  have hRRe : R ≤ Re := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R,hR,?_⟩
  intro eta heta heta1 chi hchi hchi0 hchib hchis
  have hPost := hP chi hchi hchi0 hchib (fun x hx => (hchis x hx).trans_le hRRp)
  have hError := normalized_epsilon_limit_isLittleO (epsilon_limit_of_sqrt_limit_zero
    (hErr eta heta chi hchi hchib (fun x hx => (hchis x hx).trans_le hRRe) (derivativeOrder (n+1))))
  simp only [mul_zero,sub_zero] at hError
  apply (hPost.add hError).congr' ?_ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds he0).filter_mono nhdsWithin_le_nhds] with epsilon he he0'
  rw [hDec eta heta heta1 chi hchi (fun x hx => (hchis x hx).trans_le hRRd) epsilon he he0']
  ring

theorem attach_local_odd_asymptotic {n : ℕ} {alpha beta : ℝ}
    {U : Set (Fin n → ℝ)} (c : CompatibleYCutoffData n alpha beta U)
    (a : RegularChartData) (j : ℕ) (L : ℂ)
    (hlocal : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[j] (localizedSmoothMeanIntegral a (liftShapeCutoff c.chi)
        (fun v => (c.eta v:ℂ)) (-(Real.sin a.theta/4)*epsilon) c.delta))
          (radialParameter a.theta epsilon) - (epsilon:ℂ)⁻¹*L)
      (fun epsilon => (epsilon:ℂ)⁻¹)) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => radialWeightedDerivative n j a.theta
        (fixedYChartWeight a.alpha c.chi c.eta) epsilon - (epsilon:ℂ)⁻¹*L)
      (fun epsilon => (epsilon:ℂ)⁻¹) := by
  obtain ⟨e,he,_,hmargin⟩ := radial_disk_source_trace_margin a.sin_theta_pos
  apply hlocal.congr' ?_ (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with epsilon hp hsmall
  have hr1 : Real.exp (-(Real.sin a.theta/4)*epsilon) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos a.sin_theta_pos hp]
  have hm := (hmargin epsilon hp hsmall (radialParameter a.theta epsilon)
    (by simpa using mul_pos (show 0 < Real.sin a.theta/16 from div_pos a.sin_theta_pos (by norm_num)) hp)).2
  rw [radialWeightedDerivative,compatible_source_localizedSmoothMean_derivative c a _ _ hr1 hm j]

end
end IsingBulk.HT.First.Regular
