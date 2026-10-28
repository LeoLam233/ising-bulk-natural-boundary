import IsingBulk.HT22.First.LocalLimit.Assembly
import IsingBulk.Analysis.BranchRadial

/-! Exact F001 two reflected angular charts, including the true normalization
and the arbitrary-sign curvature. This is not the finite-complement theorem. -/
namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex MeasureTheory Set Filter Metric IsingBulk.First IsingBulk.HT.First IsingBulk.Branch
open scoped Topology
set_option maxHeartbeats 1000000

theorem radial_source_upper {α ε : ℝ} (hs : 0<Real.sin α) (he : 0<ε) :
    0<(sourceS (radialParameter α ε)).im := by
  have ht := (radial_trace_components α ε (by linarith)).2
  change (sourceS (radialParameter α ε)).im = _ at ht
  rw [ht]
  apply mul_pos _ hs
  have hden : 0<1+ε := by linarith
  have hh : ε^2/(1+ε)<2*ε := (div_lt_iff₀ hden).mpr (by nlinarith)
  linarith

theorem equalAngle_angular_lower_limit {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    let k := derivativeOrder (n+1)
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ,
      Continuous χ → χ 0=1 → (∀ x,‖χ x‖≤1) → (∀ x,χ x≠0 → ‖x‖<R) →
      Tendsto (fun ε : ℝ => ε • (deriv^[k] (angularLocalIntegral α χ)) (radialParameter α ε))
        (𝓝[>] 0) (𝓝 (
          -I*(equalAngleAmplitude (n+1) α:ℂ)*(k.factorial:ℂ)*(2*(n+1:ℂ))^k*
            exp (-(α:ℂ)*I)^k * shapePeriod n k (2*(n+1)) (-I*(Real.cos α/Real.sin α)))) := by
  dsimp only
  let a := equalAngleRegularData α hα hαπ hc
  let k := derivativeOrder (n+1)
  obtain ⟨Rl,hRl,hL⟩ := equalAngle_coordinate_limit hn ho α hα hαπ hc ha
  obtain ⟨Ri,hRi,hI⟩ := Regular.actual_postMean_integral_interchange (n:=n) a ha ha
  obtain ⟨Ra,hRa,hA⟩ := angularLocalIntegral_deriv_eq_postMean (n:=n) a ha
  let R := min Rl (min Ri Ra)
  refine ⟨R,lt_min hRl (lt_min hRi hRa),?_⟩
  intro χ hχ hχ0 hχb hχs
  have ht := hL χ hχ hχ0 hχb (fun x hx => (hχs x hx).trans_le (min_le_left _ _))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hRi).filter_mono nhdsWithin_le_nhds] with ε he heRi
  have hnrm : 1<‖radialParameter α ε‖ := by rw [radialParameter_norm he.le]; exact lt_add_of_pos_right 1 he
  have hu := radial_source_upper (Real.sin_pos_of_pos_of_lt_pi hα hαπ) he
  have heq := hA χ (fun x hx => (hχs x hx).trans_le
    ((min_le_right Rl (min Ri Ra)).trans (min_le_right Ri Ra))) (radialParameter α ε) hnrm hu k
  change (deriv^[k] (angularLocalIntegral α χ)) (radialParameter α ε) = _ at heq
  rw [heq]
  have hi := hI ε he heRi χ hχ (fun x hx => (hχs x hx).trans_le
    ((min_le_right Rl (min Ri Ra)).trans (min_le_left Ri Ra))) k
  change (deriv^[k] (Regular.localizedPostMeanIntegral a χ)) (radialParameter α ε) = _ at hi
  rw [hi]

def angularTwoChartIntegral {n : ℕ} (α : ℝ) (χ : ShapeSpace n → ℂ) (s : ℂ) : ℂ :=
  angularLocalIntegral α χ s + angularUpperLocalIntegral α χ s

theorem angularTwoChartIntegral_eq_twice {n : ℕ} (α : ℝ) (χ : ShapeSpace n → ℂ) :
    angularTwoChartIntegral α χ = fun s => 2*angularLocalIntegral α χ s := by
  funext s
  rw [angularTwoChartIntegral,angularUpperLocalIntegral_eq_lower]
  ring

/-- Exact rational period inserted into the physical two-chart coefficient,
not merely a separately stated positivity certificate. -/
theorem equalAngleLeadingCoefficient_radial_formula {p : ℕ} (ho : Odd p) (hp : 3≤p)
    {α : ℝ} (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0) :
    equalAngleLeadingCoefficient p α =
      -2*I*(equalAngleAmplitude p α:ℂ)*((derivativeOrder p).factorial:ℂ)*
        (2*(p:ℂ))^(derivativeOrder p)*exp (-(α:ℂ)*I)^(derivativeOrder p)*
        ((shapeAngularConstant (p-1)/
          (2*(derivativeOrder p:ℝ)*(2*p)*|Real.cos α/Real.sin α|^(derivativeOrder p)):ℝ):ℂ) := by
  unfold equalAngleLeadingCoefficient
  have hs : Real.sin α≠0 := (Real.sin_pos_of_pos_of_lt_pi hα hαπ).ne'
  have hj := constrained_odd_period_exact ho hp (show (0:ℝ)<2*p by positivity)
    (div_ne_zero hc hs)
  simpa only [ofReal_div] using congrArg
    (fun z : ℂ => -2*I*(equalAngleAmplitude p α:ℂ)*((derivativeOrder p).factorial:ℂ)*
      (2*(p:ℂ))^(derivativeOrder p)*exp (-(α:ℂ)*I)^(derivativeOrder p)*z) hj

theorem equalAngleLeadingCoefficient_radial_nonzero {p : ℕ} (ho : Odd p) (hp : 3≤p)
    {α : ℝ} (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0) :
    equalAngleLeadingCoefficient p α≠0 := by
  rw [equalAngleLeadingCoefficient_radial_formula ho hp hα hαπ hc]
  have hs : Real.sin α≠0 := (Real.sin_pos_of_pos_of_lt_pi hα hαπ).ne'
  have hd : 0 < |Real.cos α/Real.sin α| := abs_pos.mpr (div_ne_zero hc hs)
  have hS := shapeAngularConstant_pos (n:=p-1) (by omega)
  have hk : 0<(derivativeOrder p:ℝ) := by exact_mod_cast derivativeOrder_pos ho hp
  have hJ : (0:ℝ)<shapeAngularConstant (p-1)/
      (2*(derivativeOrder p:ℝ)*(2*p)*|Real.cos α/Real.sin α|^(derivativeOrder p)) := by positivity
  apply mul_ne_zero _ (ofReal_ne_zero.mpr hJ.ne')
  apply mul_ne_zero _ (pow_ne_zero _ (exp_ne_zero _))
  apply mul_ne_zero _ (pow_ne_zero _ (mul_ne_zero (by norm_num)
    (by exact_mod_cast (show p≠0 by omega))))
  apply mul_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero (derivativeOrder p))
  apply mul_ne_zero _ (ofReal_ne_zero.mpr (equalAngleAmplitude_pos p hα hαπ).ne')
  exact mul_ne_zero (by norm_num) I_ne_zero

/-- The actual sum of the two reflected chart integrals has exactly F001's
nonzero epsilon^{-1} coefficient. It applies on both sides of α=π/2. -/
theorem equalAngle_two_chart_limit {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    equalAngleLeadingCoefficient (n+1) α≠0 ∧
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ,
      Continuous χ → χ 0=1 → (∀ x,‖χ x‖≤1) → (∀ x,χ x≠0 → ‖x‖<R) →
      Tendsto (fun ε : ℝ => ε •
        (deriv^[derivativeOrder (n+1)] (angularTwoChartIntegral α χ)) (radialParameter α ε))
        (𝓝[>] 0) (𝓝 (equalAngleLeadingCoefficient (n+1) α)) := by
  have hp3 : 3≤n+1 := by obtain ⟨m,hm⟩ := ho;omega
  refine ⟨equalAngleLeadingCoefficient_radial_nonzero ho hp3 hα hαπ hc,?_⟩
  obtain ⟨R,hR,hL⟩ := equalAngle_angular_lower_limit hn ho α hα hαπ hc ha
  refine ⟨R,hR,?_⟩
  intro χ hχ hχ0 hχb hχs
  have ht := (hL χ hχ hχ0 hχb hχs).const_mul 2
  convert ht using 1
  · funext ε
    rw [angularTwoChartIntegral_eq_twice,iterate_deriv_const_mul]
    simp only [real_smul]
    ring
  · congr 1
    unfold equalAngleLeadingCoefficient
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    ring

/-- Equivalent little-o formulation, with no assumed local asymptotic. -/
theorem equalAngle_two_chart_asymptotic {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ,
      Continuous χ → χ 0=1 → (∀ x,‖χ x‖≤1) → (∀ x,χ x≠0 → ‖x‖<R) →
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun ε => (deriv^[derivativeOrder (n+1)] (angularTwoChartIntegral α χ))
          (radialParameter α ε)-(ε:ℂ)⁻¹*equalAngleLeadingCoefficient (n+1) α)
        (fun ε => (ε:ℂ)⁻¹) := by
  obtain ⟨_,R,hR,h⟩ := equalAngle_two_chart_limit hn ho α hα hαπ hc ha
  exact ⟨R,hR,fun χ hχ hχ0 hχb hχs =>
    normalized_epsilon_limit_isLittleO (h χ hχ hχ0 hχb hχs)⟩

end
end IsingBulk.HT22.LocalLimit
