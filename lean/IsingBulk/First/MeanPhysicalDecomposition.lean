import IsingBulk.First.MeanParameterRectangle
import IsingBulk.First.MeanParameterDisk

/-! Exact hard-mean decomposition on a complex s neighborhood, retaining a
fixed evaluation radius and the three actual displaced side integrals. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch

 theorem radialParameter_sub_center_norm (theta epsilon : ℝ) :
    ‖radialParameter theta epsilon-exp ((theta:ℂ)*I)‖ = |epsilon| := by
  have he : radialParameter theta epsilon-exp ((theta:ℂ)*I) =
      (epsilon:ℂ)*exp ((theta:ℂ)*I) := by unfold radialParameter; push_cast; ring
  rw [he,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs]

/-- The mean residue identity holds for every s in the source complex disk,
with rho fixed at the evaluation epsilon before s varies. -/
theorem uniform_actual_mean_disk (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1) :
    ∃ R epsilon₀ : ℝ, 0 < R ∧ 0 < epsilon₀ ∧ ∀ (epsilon : ℝ) (t : Fin n → ℝ) (s : ℂ),
      0 < epsilon → epsilon < epsilon₀ → (∀ j, |shapeExtend t j| < R/4) →
      ‖s-radialParameter a.theta epsilon‖ < (Real.sin a.theta/16)*epsilon →
      clockwiseRectangle (R/4) 0 (-(R/4))
        (meanLocalDensity s (-(Real.sin a.theta/4)*epsilon) a.alpha t) = postMeanDensity s a.alpha t := by
  obtain ⟨R,hR,_,hD⟩ := parameter_actual_mean_rectangle a n halpha
  obtain ⟨eM,heM,_,hM⟩ := radial_disk_source_trace_margin a.sin_theta_pos
  let c₀ := Real.sin a.theta/4
  let c₁ := Real.sin a.theta/16
  let K := c₀+c₁+1
  have hc₀ : 0 < c₀ := div_pos a.sin_theta_pos (by norm_num)
  have hc₁ : 0 < c₁ := div_pos a.sin_theta_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have hNc : 0 < (n+1:ℝ)*c₀ := mul_pos (by positivity) hc₀
  let e₀ := min eM (min (R/K) ((R/4)/((n+1:ℝ)*c₀)))
  have he₀ : 0 < e₀ := lt_min heM (lt_min (div_pos hR hK) (div_pos (by positivity) hNc))
  refine ⟨R,e₀,hR,he₀,?_⟩
  intro epsilon t s he her ht hs
  change ‖s-radialParameter a.theta epsilon‖ < c₁*epsilon at hs
  have heM' : epsilon < eM := her.trans_le (min_le_left _ _)
  have heK : epsilon < R/K := her.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heN : epsilon < (R/4)/((n+1:ℝ)*c₀) := her.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hKR : epsilon*K < R := (lt_div_iff₀ hK).mp heK
  have hscenter : ‖s-exp ((a.theta:ℂ)*I)‖ < R := by
    have htri := norm_sub_le_norm_sub_add_norm_sub s (radialParameter a.theta epsilon) (exp ((a.theta:ℂ)*I))
    rw [radialParameter_sub_center_norm,abs_of_pos he] at htri
    dsimp [K] at hKR
    nlinarith [mul_pos hc₀ he]
  have hrho : |(-c₀*epsilon)| < R := by
    rw [abs_of_neg (by nlinarith [mul_pos hc₀ he])]
    dsimp [K] at hKR
    nlinarith [mul_pos hc₁ he]
  have hrhoneg : -c₀*epsilon < 0 := by nlinarith [mul_pos hc₀ he]
  have hheight : -(n+1:ℝ)*(-c₀*epsilon) < R/4 := by
    have hm := (lt_div_iff₀ hNc).mp heN
    nlinarith
  have hmargin := (hM epsilon he heM' s hs).2
  exact hD s (-c₀*epsilon) t hscenter hrho hrhoneg hheight hmargin ht

def hardMeanIntegral {n : ℕ} (s : ℂ) (rho alpha delta : ℝ) (t : Fin n → ℝ) : ℂ :=
  ∫ v : ℝ in -delta..delta, meanLocalDensity s rho alpha t (v:ℂ)

def displacedMeanSides {n : ℕ} (s : ℂ) (rho alpha delta height : ℝ) (t : Fin n → ℝ) : ℂ :=
  (∫ v : ℝ in -delta..delta, meanLocalDensity s rho alpha t ((v:ℂ)-(height:ℂ)*I)) -
    I*(∫ y : ℝ in 0..-height, meanLocalDensity s rho alpha t ((delta:ℂ)+(y:ℂ)*I)) +
    I*(∫ y : ℝ in 0..-height, meanLocalDensity s rho alpha t (-(delta:ℂ)+(y:ℂ)*I))

/-- Explicit top-side decomposition using the already oriented physical
rectangle. Boundedness of the displayed sides is a separate source obligation. -/
theorem hardMean_eq_residue_add_sides {n : ℕ} (s : ℂ) (rho alpha delta height : ℝ)
    (t : Fin n → ℝ)
    (hres : clockwiseRectangle delta 0 (-height) (meanLocalDensity s rho alpha t) =
      postMeanDensity s alpha t) :
    hardMeanIntegral s rho alpha delta t =
      postMeanDensity s alpha t+displacedMeanSides s rho alpha delta height t := by
  unfold hardMeanIntegral displacedMeanSides
  unfold clockwiseRectangle at hres
  simp only [Complex.ofReal_zero,zero_mul,add_zero,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] at hres ⊢
  linear_combination hres

end
end IsingBulk.First
