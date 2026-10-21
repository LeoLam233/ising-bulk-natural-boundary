import IsingBulk.HT.First.OddActualLowerShapeLimit
import IsingBulk.HT.First.OddLimitTransfer
import IsingBulk.HT.First.OrderArithmetic
import IsingBulk.First.ActualPostMeanInterchange
import IsingBulk.First.ActualPostMeanCoordinateLimit
import IsingBulk.First.IntegratedMeanDecomposition

/-! Actual fixed-radius lower jets are o(ε⁻¹). This endpoint is sufficient for
leading-term comparison and does not strengthen the critical logarithmic jet
to a false uniform O(1) estimate. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.Branch Complex MeasureTheory Filter IsingBulk.First
open scoped Topology

theorem actual_localized_postMean_lower_epsilon_limit {n k j : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k-1) (hj : j < k) (a : OrderedChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x, ‖chi x‖ ≤ 1) → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => epsilon •
        (deriv^[j] (localizedPostMeanIntegral a chi)) (radialParameter a.theta epsilon))
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Rl,hRl,hL⟩ := actual_lower_postMean_shape_epsilon_limit hn hdegree hj a hb
  obtain ⟨Ri,hRi,hI⟩ := actual_postMean_integral_interchange (n := n) a ha hb
  refine ⟨min Rl Ri,lt_min hRl hRi,?_⟩
  intro chi hchi hchib hchis
  have ht := (hL chi hchi hchib (fun x hx => (hchis x hx).trans_le (min_le_left _ _))).const_smul
    (Real.sqrt (n+1))⁻¹
  simp only [smul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hRi).filter_mono nhdsWithin_le_nhds] with epsilon he heRi
  rw [hI epsilon he heRi chi hchi (fun x hx => (hchis x hx).trans_le (min_le_right _ _))]
  have hi := integral_shapeExtend n (fun x => chi x*intrinsicPostMeanDerivative a j epsilon x)
  have hid : localizedPostMeanDerivativeIntegral a j chi epsilon =
      (Real.sqrt (n+1))⁻¹ • ∫ x : ShapeSpace n, chi x*intrinsicPostMeanDerivative a j epsilon x := by
    simpa only [localizedPostMeanDerivativeIntegral, intrinsicPostMeanDerivative,
      intrinsicShapeCoordinates_shapeCoordinateEquiv] using hi
  rw [hid,smul_comm]

theorem actual_local_mean_lower_epsilon_limit {n k j : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k-1) (hj : j < k) (a : OrderedChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ R : ℝ, 0 < R ∧ ∀ eta : ℝ → ℂ, Continuous eta →
        (∀ v : ℝ, |v| ≤ delta → eta v=1) →
        ∀ chi : ShapeSpace n → ℂ, Continuous chi → (∀ x, ‖chi x‖ ≤ 1) →
          (∀ x, chi x ≠ 0 → ‖x‖ < R) →
          Tendsto (fun epsilon : ℝ => epsilon •
            (deriv^[j] (localizedSmoothMeanIntegral a chi eta
              (-(Real.sin a.theta/4)*epsilon) delta)) (radialParameter a.theta epsilon))
            (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Rp,hRp,hP⟩ := actual_localized_postMean_lower_epsilon_limit hn hdegree hj a ha hb
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
  intro eta heta heta1 chi hchi hchib hchis
  have hPost := hP chi hchi hchib (fun x hx => (hchis x hx).trans_le hRRp)
  have hError := epsilon_limit_of_sqrt_limit_zero
    (hErr eta heta chi hchi hchib (fun x hx => (hchis x hx).trans_le hRRe) j)
  have ht := hPost.add hError
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds he0).filter_mono nhdsWithin_le_nhds] with epsilon he he0'
  rw [hDec eta heta heta1 chi hchi (fun x hx => (hchis x hx).trans_le hRRd) epsilon he he0',smul_add]

end
end IsingBulk.HT.First
