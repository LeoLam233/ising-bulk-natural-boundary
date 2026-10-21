import IsingBulk.HT.Final.PhysicalNormalization
import IsingBulk.First.FarExteriorFormFactor
import IsingBulk.First.OnsiteRadiusIndependence
import IsingBulk.First.ExteriorAnalyticGeometry

/-! Genuine local normal convergence for the full odd, full-site contour sum
near infinity. The onsite term is included in `standardFormFactor`; no onsite
resummation identity and no LT physical representation enter this proof. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First Set Filter MeasureTheory
open scoped Topology BigOperators

/-- A full-site geometric density bound. The inverse-product factors cost
16^N; the 2N normalized contour lengths cancel exactly that cost. -/
theorem standardDensity_quarter_norm_bound {N : ℕ} (hN : 0 < N)
    (t : ℂ) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖=(1/4:ℝ)) (hy : ∀ i, ‖y i‖=(1/4:ℝ))
    (hD : ∀ i, 1 ≤ ‖dispersion (x i) (y i) t‖) :
    ‖standardDensity t x y‖ ≤ 16*(16:ℝ)^N := by
  have hpow : 1 ≤ (4:ℝ)^N := one_le_pow₀ (by norm_num)
  have hnx : ‖1+(coordinateProduct x)⁻¹‖ ≤ 2*(4:ℝ)^N := by
    have h := norm_add_le (1:ℂ) (coordinateProduct x)⁻¹
    rw [norm_one,coordinateProduct_quarter_inv_norm x hx] at h
    linarith
  have hny : ‖1+(coordinateProduct y)⁻¹‖ ≤ 2*(4:ℝ)^N := by
    have h := norm_add_le (1:ℂ) (coordinateProduct y)⁻¹
    rw [norm_one,coordinateProduct_quarter_inv_norm y hy] at h
    linarith
  have hdx := one_sub_coordinateProduct_quarter_norm_lower hN x hx
  have hdy := one_sub_coordinateProduct_quarter_norm_lower hN y hy
  have hden : (1/4:ℝ) ≤ ‖(1-coordinateProduct x)*(1-coordinateProduct y)‖ := by
    rw [norm_mul]
    nlinarith
  have hnum : ‖(1+(coordinateProduct x)⁻¹)*(1+(coordinateProduct y)⁻¹)‖ ≤
      4*(16:ℝ)^N := by
    rw [norm_mul]
    calc
      _ ≤ (2*(4:ℝ)^N)*(2*(4:ℝ)^N) := mul_le_mul hnx hny (norm_nonneg _) (by positivity)
      _ = _ := by rw [show (16:ℝ)=4*4 by norm_num,mul_pow]; ring
  have hglobal : ‖(1+(coordinateProduct x)⁻¹)*(1+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct x)*(1-coordinateProduct y))‖ ≤ 16*(16:ℝ)^N := by
    rw [norm_div]
    apply (div_le_iff₀ (by linarith : 0 < ‖(1-coordinateProduct x)*(1-coordinateProduct y)‖)).mpr
    nlinarith [pow_pos (by norm_num : (0:ℝ)<16) N]
  have hpx := pairProduct_quarter_norm_le_one x hx
  have hpy := pairProduct_quarter_norm_le_one y hy
  have hres : ‖∏ i, (dispersion (x i) (y i) t)⁻¹‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro i _; exact norm_nonneg _
    · intro i _; rw [norm_inv]; exact inv_le_one_of_one_le₀ (hD i)
  have hc : ‖commonDensity t x y‖ ≤ 1 := by
    simp only [commonDensity,norm_mul]
    calc
      _ ≤ 1*1*1 := mul_le_mul (mul_le_mul hpx hpy (norm_nonneg _) (by norm_num))
        hres (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  rw [standardDensity,norm_mul]
  calc
    _ ≤ (16*(16:ℝ)^N)*1 := mul_le_mul hglobal hc (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- The factorial is retained; this is a bound on the actual full coefficient. -/
theorem standardFormFactor_quarter_norm_bound (N : ℕ) (hN : 0 < N)
    {t : ℂ} (ht : 16 < ‖t‖) :
    ‖standardFormFactor N (1/4) t‖ ≤ 16/(N.factorial:ℝ) := by
  have h := multiCircleIntegral_norm_le N (r := 1/4) (by norm_num)
    (fun y => multiCircleIntegral (1/4) N (fun x => standardDensity t x y)) (by
      intro y hy
      apply multiCircleIntegral_norm_le N (by norm_num)
      intro x hx
      exact standardDensity_quarter_norm_bound hN t x y hx hy (fun i =>
        farExterior_dispersion_norm_lower ht
          (by rw [hx i]; norm_num) (by rw [hy i]; norm_num)))
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg N.factorial))
  have hcancel : (1/4:ℝ)^N*((1/4:ℝ)^N*(16*(16:ℝ)^N))=16 := by
    calc
      _ = 16*(((1/4:ℝ)*(1/4)*16)^N) := by simp only [mul_pow]; ring
      _ = 16 := by norm_num
  rw [hcancel] at hh
  simpa only [standardFormFactor,norm_mul,norm_inv,Complex.norm_natCast,
    div_eq_mul_inv,mul_comm] using hh

/-- Genuine holomorphy at a fixed radius. Continuity of the spatial amplitude
is obtained from an existing admissible upper reference point; that amplitude
is independent of t. The target domain is the full far exterior. -/
theorem standardFormFactor_far_analyticOn (N : ℕ) (hN : 0 < N)
    {r : ℝ} (hr : (1/4:ℝ) ≤ r) (hr1 : r < 1) :
    AnalyticOnNhd ℂ (standardFormFactor N r) {t : ℂ | 16 < ‖t‖} := by
  let t₀ : ℂ := 10*Complex.I
  have hq : (1/4:ℝ)⁻¹-1/4 < (sourceS t₀).im := by
    norm_num [t₀,sourceS,mul_inv_rev]
  have hr0 : 0 < r := by linarith
  have hm : r⁻¹-r < (sourceS t₀).im :=
    (inverse_radius_drop_mono (by norm_num : (0:ℝ)<1/4) hr).trans_lt hq
  let A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ := fun x y =>
    (1+(coordinateProduct x)⁻¹)*(1+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct x)*(1-coordinateProduct y))*pairProduct x*pairProduct y
  have hfac : ∀ t x y, standardDensity t x y=A x y*∏ i,(dispersion (x i) (y i) t)⁻¹ := by
    intro t x y
    dsimp only [standardDensity,commonDensity,A]
    ring
  have hf := (normalizationDensities_continuous_angles N hN r t₀
    (globalRoot t₀) (globalRoot_admissible hr0 hr1 hm)).2
  have hA : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      A (angleTuple r p.1) (angleTuple r p.2)) := by
    apply spatialAmplitude_continuous hr0 hr1 (dampingDomain_of_margin hr0 hr1 hm) A
    simpa only [angularResolventProduct_eq,← hfac] using hf
  have hD : ∀ t : ℂ, 16 < ‖t‖ →
      ∀ p : (Fin N → ℝ) × (Fin N → ℝ), ∀ i,
      sourceS t-angularDispersionTrace r i p ≠ 0 := by
    intro t ht p i
    rw [sourceS_sub_angularDispersionTrace]
    exact farExterior_dispersion_ne_zero ht
      (by simp only [angleTuple,anglePoint_norm hr0.le]; exact ⟨hr,hr1.le⟩)
      (by simp only [angleTuple,anglePoint_norm hr0.le]; exact ⟨hr,hr1.le⟩)
  intro t ht
  have ha := rationalDoubleContour_analyticAt_on N hr0 A hA
    (U := {s : ℂ | 16 < ‖s‖}) (isOpen_lt continuous_const continuous_norm)
    (fun s hs => norm_pos_iff.mp (by change 16 < ‖s‖ at hs; linarith))
    hD ht
  convert! ha using 1
  funext s
  simp only [standardFormFactor,rationalDoubleContour,hfac]

theorem standardFormFactor_quarter_analyticOn (N : ℕ) (hN : 0 < N) :
    AnalyticOnNhd ℂ (standardFormFactor N (1/4)) {t : ℂ | 16 < ‖t‖} :=
  standardFormFactor_far_analyticOn N hN le_rfl (by norm_num)

/-- Full-site radius independence near infinity follows by the identity
principle from the already proved all-N onsite and offsite annular transport. -/
theorem standardFormFactor_far_radius_eq (N : ℕ) (hN : 0 < N)
    {r : ℝ} (hr : (1/4:ℝ) ≤ r) (hr1 : r < 1)
    {t : ℂ} (ht : 16 < ‖t‖) :
    standardFormFactor N r t = standardFormFactor N (1/4) t := by
  let t₀ : ℂ := 20*Complex.I
  have ht₀ : t₀ ∈ complexNormExterior 16 := by
    change 16 < ‖20*Complex.I‖
    norm_num [norm_mul]
  have hm₀ : (1/4:ℝ)⁻¹-1/4 < (sourceS t₀).im := by
    norm_num [t₀,sourceS,mul_inv_rev]
  have hr0 : 0 < r := by linarith
  have he : standardFormFactor N r =ᶠ[𝓝 t₀] standardFormFactor N (1/4) := by
    filter_upwards [dampingDomain_mem_nhds
      (dampingDomain_of_margin (by norm_num : (0:ℝ)<1/4) (by norm_num) hm₀)] with s hs
    have hmr := (inverse_radius_drop_mono (by norm_num : (0:ℝ)<1/4) hr).trans_lt hs.2
    rw [standardFormFactor_eq_onsite_add_double N hN r s (globalRoot s)
      (globalRoot_admissible hr0 hr1 hmr)]
    rw [standardFormFactor_eq_onsite_add_double N hN (1/4) s (globalRoot s)
      (globalRoot_admissible (by norm_num) (by norm_num) hs.2)]
    rw [onsiteFormFactor_radius_eq N hN (by norm_num) hr1 hr hs.2,
      doubleFormFactor_radius_eq N hN (by norm_num) hr1 hr hs.2]
  exact (standardFormFactor_far_analyticOn N hN hr hr1).eqOn_of_preconnected_of_eventuallyEq
    (standardFormFactor_quarter_analyticOn N hN)
    (complexNormExterior_isPreconnected (by norm_num : (0:ℝ) ≤ 16)) ht₀ he ht

/-- Entire odd full-site series, including N=1, converges normally on |t|>16. -/
theorem quarter_oddFull_majorant_summable :
    Summable (fun n : ℕ => 16/((2*n+1).factorial:ℝ)) := by
  have h : Summable (fun n : ℕ => (1:ℝ)/(n.factorial:ℝ)) := by
    simpa only [one_pow] using Real.summable_pow_div_factorial (1:ℝ)
  have hinj : Function.Injective (fun n : ℕ => 2*n+1) := by
    intro a b hab
    dsimp only at hab
    omega
  have ho := h.comp_injective hinj
  simpa only [Function.comp_def,mul_one_div] using ho.mul_left (16:ℝ)

theorem fixedOddFullSeries_quarter_analyticOn :
    AnalyticOnNhd ℂ (fixedOddFullSeries (1/4)) {t : ℂ | 16 < ‖t‖} := by
  have hsum : DifferentiableOn ℂ (fixedOddFullSeries (1/4)) {t : ℂ | 16 < ‖t‖} := by
    apply Complex.differentiableOn_tsum_of_summable_norm quarter_oddFull_majorant_summable
    · intro n
      exact (standardFormFactor_quarter_analyticOn (2*n+1) (by omega)).differentiableOn
    · exact isOpen_lt continuous_const continuous_norm
    · intro n t ht
      exact standardFormFactor_quarter_norm_bound (2*n+1) (by omega) ht
  exact hsum.analyticOnNhd (isOpen_lt continuous_const continuous_norm)

theorem fixedOddFullSeries_quarter_summable {t : ℂ} (ht : 16 < ‖t‖) :
    Summable (fun n : ℕ => oddFullCoefficient n (1/4) t) :=
  quarter_oddFull_majorant_summable.of_norm_bounded
    (fun n => standardFormFactor_quarter_norm_bound (2*n+1) (by omega) ht)

theorem fixedNormalizedBulk_quarter_analyticOn :
    AnalyticOnNhd ℂ (fixedNormalizedBulk (1/4)) {t : ℂ | 16 < ‖t‖} := by
  intro t ht
  exact (exteriorPrefactor_analyticOn t (by change 16 < ‖t‖ at ht; change 1 < ‖t‖; linarith)).mul
    (fixedOddFullSeries_quarter_analyticOn t ht)

end
end IsingBulk.HT.Final
