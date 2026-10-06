import IsingBulk.First.ActualLowerIntegralBounds
import IsingBulk.First.IntegratedMeanDecomposition

/-! Uniform boundedness below k for the complete actual smooth local chart,
including the genuine displaced-side and real-cutoff error integrals. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch
open scoped Topology

theorem actual_smooth_local_lower_bounds {n : ℕ} (hn : 1 ≤ n) (a : OrderedChartData)
    (heven : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ R epsilon₀ : ℝ, 0 < R ∧ 0 < epsilon₀ ∧
      ∀ eta : ℝ → ℂ, Continuous eta → (∀ v : ℝ, |v| ≤ delta → eta v=1) →
      ∀ chi : ShapeSpace n → ℂ, Continuous chi → (∀ x, ‖chi x‖ ≤ 1) →
        (∀ x, chi x ≠ 0 → ‖x‖ < R) →
        ∀ j : ℕ, j < (n+1)^2/2-1 → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
          0 < epsilon → epsilon < epsilon₀ →
          ‖(deriv^[j] (localizedSmoothMeanIntegral a chi eta
            (-(Real.sin a.theta/4)*epsilon) delta)) (radialParameter a.theta epsilon)‖ ≤ C := by
  obtain ⟨Dp,hDp,hDecomp⟩ := actual_integrated_mean_derivative_decomposition (n := n) a ha hb
  obtain ⟨De,hDe,hError⟩ := actual_mean_error_shape_integral_bounds (n := n) a ha hb
  obtain ⟨Rp,hRp,hPost⟩ := actual_first_postMean_lower_bounds hn a heven ha hb
  refine ⟨min Dp De,lt_min hDp hDe,?_⟩
  intro delta hd hdD
  obtain ⟨Rd,ed,hRd,hed,hId⟩ := hDecomp delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨Re,hRe,hErr⟩ := hError delta hd (hdD.trans (min_le_right _ _))
  let R := min Rp (min Rd Re)
  have hR : 0 < R := lt_min hRp (lt_min hRd hRe)
  have hRRp : R ≤ Rp := min_le_left _ _
  have hRRd : R ≤ Rd := (min_le_right _ _).trans (min_le_left _ _)
  have hRRe : R ≤ Re := (min_le_right _ _).trans (min_le_right _ _)
  let c₀ := Real.sin a.theta/4
  have hc₀ : 0 < c₀ := div_pos a.sin_theta_pos (by norm_num)
  let e₀ := min ed (min Rp (Re/(c₀+1)))
  have he₀ : 0 < e₀ := lt_min hed (lt_min hRp (div_pos hRe (by positivity)))
  refine ⟨R,e₀,hR,he₀,?_⟩
  intro eta heta heta1 chi hchi hchib hchis j hj
  obtain ⟨Cp,hCp,hp⟩ := hPost chi hchi hchib (fun x hx => (hchis x hx).trans_le hRRp) j hj
  obtain ⟨Ce,hCe,he⟩ := (hErr eta heta chi hchi hchib
    (fun x hx => (hchis x hx).trans_le hRRe)).2 j
  refine ⟨Cp+‖(Real.sqrt (n+1))⁻¹‖*Ce,by positivity,?_⟩
  intro epsilon heps heps0
  have hed' : epsilon < ed := heps0.trans_le (min_le_left _ _)
  have hep' : epsilon < Rp := heps0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hem : epsilon*(c₀+1) < Re := (lt_div_iff₀ (show 0 < c₀+1 by positivity)).mp
    (heps0.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have herho : |(-c₀*epsilon)| ≤ Re := by
    rw [abs_of_neg (by nlinarith)]
    nlinarith
  have hes : ‖radialParameter a.theta epsilon-exp ((a.theta:ℂ)*I)‖ < Re := by
    rw [radialParameter_sub_center_norm,abs_of_pos heps]
    nlinarith
  rw [hId eta heta heta1 chi hchi (fun x hx => (hchis x hx).trans_le hRRd) epsilon heps hed' j]
  apply (norm_add_le _ _).trans
  apply add_le_add (hp epsilon heps hep')
  rw [localizedMeanErrorIntegral_iteratedDeriv,norm_smul]
  exact mul_le_mul_of_nonneg_left (he (-c₀*epsilon) herho _ hes) (norm_nonneg _)

end
end IsingBulk.First
