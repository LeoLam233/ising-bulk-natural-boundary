import IsingBulk.HT22.First.LocalLimit.PrimeCharts
import IsingBulk.HT.Contour.SignedReflectionJets

/-! Exact negative-signed critical charts at the positive trace. The real
shape orientation is retained explicitly: the lower chart is −u−β. Its
factorial/Haar normalization is identical to the original unsigned chart.
Only generic reflection derivative calculus is reused from SignedReflectionJets. -/
namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex Set Filter MeasureTheory IsingBulk.First IsingBulk.Branch IsingBulk.HT.First
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def negativeCriticalLocalIntegral {n : ℕ} (β : ℝ) (χ : ShapeSpace n → ℝ) (s : ℂ) : ℂ :=
  ∫ u : Fin n → ℝ,(χ (shapeCoordinateEquiv n (WithLp.toLp 2 u)):ℂ)*
    ((((n+1).factorial:ℂ)*(2*(Real.pi:ℂ))^n)⁻¹*
      Physical.signedAngularDensity true s
        (Physical.constrainedAngles true n (fun i => -u i-β)))

def negativeCriticalUpperIntegral {n : ℕ} (β : ℝ) (χ : ShapeSpace n → ℝ) (s : ℂ) : ℂ :=
  ∫ u : Fin n → ℝ,(χ (shapeCoordinateEquiv n (WithLp.toLp 2 u)):ℂ)*
    ((((n+1).factorial:ℂ)*(2*(Real.pi:ℂ))^n)⁻¹*
      Physical.signedAngularDensity true s
        (Physical.constrainedAngles true n (fun i => u i+β)))

def negativeCriticalTwoChartIntegral {n : ℕ} (β : ℝ) (χ : ShapeSpace n → ℝ) (s : ℂ) : ℂ :=
  negativeCriticalLocalIntegral β χ s+negativeCriticalUpperIntegral β χ s

theorem negativeCriticalUpperIntegral_eq_lower {n : ℕ} (β : ℝ) (χ : ShapeSpace n → ℝ) (s : ℂ) :
    negativeCriticalUpperIntegral β χ s=negativeCriticalLocalIntegral β χ s := by
  unfold negativeCriticalUpperIntegral negativeCriticalLocalIntegral
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    dsimp only
    have he : (fun i => u i+β)=(fun i => -(-u i-β)) := by funext i;ring
    rw [he,Physical.constrainedDensity_reflect]

theorem negativeCriticalLocalIntegral_reflected {n : ℕ} (ho : Odd (n+1))
    (α : ℝ) (χ : ShapeSpace n → ℝ) {s : ℂ} (hs : 1<‖s‖) :
    negativeCriticalLocalIntegral (Real.pi-α) χ (-star s)=
      -star (angularLocalIntegral α (fun x => (χ x:ℂ)) s) := by
  have hpoint (u : Fin n → ℝ) :
      Physical.signedAngularDensity true (-star s)
        (Physical.constrainedAngles true n (fun i => -u i-(Real.pi-α)))=
      -star (Physical.signedAngularDensity false s
        (Physical.constrainedAngles false n (fun i => α-u i))) := by
    have hh := Physical.signedAngularDensity_neg_of_angles false ho
      (show 1<‖star s‖ by simpa using hs)
      (Physical.constrainedAngles false n (fun i => α-u i))
      (Physical.constrainedAngles true n (fun i => -u i-(Real.pi-α)))
    have hy (i : Fin (n+1)) :
        IsingBulk.Preferred22.angleRoot (Physical.constrainedAngles true n (fun i => -u i-(Real.pi-α)) i)=
        -IsingBulk.Preferred22.angleRoot (Physical.constrainedAngles false n (fun i => α-u i) i) := by
      have h := Physical.constrainedAngles_add_pi_positive_to_negative ho
        (fun i => -u i-(Real.pi-α)) i
      have he : (fun i => (-u i-(Real.pi-α))+Real.pi)=(fun i => α-u i) := by funext i;ring
      rw [he] at h
      linear_combination h
    have hh' := hh hy
    simpa only [Bool.not_false,Physical.signedAngularDensity_conj false hs] using hh'
  rw [←angularUpperLocalIntegral_eq_lower α (fun x => (χ x:ℂ)) s]
  unfold negativeCriticalLocalIntegral angularUpperLocalIntegral
  simp_rw [hpoint]
  simp only [Complex.star_def]
  rw [←integral_conj,←integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    dsimp only
    simp [map_ofNat]


theorem negativeCriticalTwoChartIntegral_eq_twice {n : ℕ} (β : ℝ) (χ : ShapeSpace n → ℝ) :
    negativeCriticalTwoChartIntegral β χ=fun s => 2*negativeCriticalLocalIntegral β χ s := by
  funext s
  rw [negativeCriticalTwoChartIntegral,negativeCriticalUpperIntegral_eq_lower]
  ring

theorem negativeCriticalTwoChartIntegral_reflected {n : ℕ} (ho : Odd (n+1))
    (α : ℝ) (χ : ShapeSpace n → ℝ) {s : ℂ} (hs : 1<‖s‖) :
    negativeCriticalTwoChartIntegral (Real.pi-α) χ (-star s)=
      -star (angularTwoChartIntegral α (fun x => (χ x:ℂ)) s) := by
  rw [negativeCriticalTwoChartIntegral_eq_twice,angularTwoChartIntegral_eq_twice]
  dsimp only
  rw [negativeCriticalLocalIntegral_reflected ho α χ hs]
  simp only [star_mul',star_ofNat]
  ring

theorem negativeCriticalTwoChartIntegral_iteratedDeriv {n : ℕ} (ho : Odd (n+1))
    (α : ℝ) (χ : ShapeSpace n → ℝ) (j : ℕ) {s : ℂ} (hs : 1<‖s‖) :
    iteratedDeriv j (negativeCriticalTwoChartIntegral (Real.pi-α) χ) (-star s)=
      -((-1:ℂ)^j*star (iteratedDeriv j (angularTwoChartIntegral α (fun x => (χ x:ℂ))) s)) := by
  have he : negativeCriticalTwoChartIntegral (Real.pi-α) χ =ᶠ[𝓝 (-star s)]
      (fun z => -star (angularTwoChartIntegral α (fun x => (χ x:ℂ)) (-star z))) := by
    have hs' : 1<‖-star s‖ := by simpa using hs
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hs'] with z hz
    have hh := negativeCriticalTwoChartIntegral_reflected ho α χ (s := -star z) (by simpa using hz)
    simpa only [star_neg,star_star,neg_neg] using hh
  rw [he.iteratedDeriv_eq j,iteratedDeriv_fun_neg,
    IsingBulk.HT.Contour.iteratedDeriv_star_neg_conj]
  simp only [star_neg,star_star,neg_neg]

def signedCriticalLeadingCoefficient (p : ℕ) (α : ℝ) : ℂ :=
  -((-1:ℂ)^(derivativeOrder p)*star (equalAngleLeadingCoefficient p α))

theorem signedCriticalLeadingCoefficient_ne_zero {p : ℕ} {α : ℝ}
    (h : equalAngleLeadingCoefficient p α≠0) : signedCriticalLeadingCoefficient p α≠0 := by
  unfold signedCriticalLeadingCoefficient
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num)) (star_ne_zero.mpr h))

theorem negativeCritical_two_chart_limit {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    signedCriticalLeadingCoefficient (n+1) α≠0 ∧
    ∃ R : ℝ,0<R ∧ ∀ χ : ShapeSpace n → ℝ,
      Continuous χ → χ 0=1 → (∀ x,|χ x|≤1) → (∀ x,χ x≠0 → ‖x‖<R) →
      Tendsto (fun ε : ℝ => ε •
        (deriv^[derivativeOrder (n+1)] (negativeCriticalTwoChartIntegral (Real.pi-α) χ))
          (radialParameter (Real.pi-α) ε))
        (𝓝[>] 0) (𝓝 (signedCriticalLeadingCoefficient (n+1) α)) := by
  obtain ⟨hΛ,R,hR,hL⟩ := equalAngle_two_chart_limit hn ho α hα hαπ hc ha
  refine ⟨signedCriticalLeadingCoefficient_ne_zero hΛ,R,hR,?_⟩
  intro χ hχ hχ0 hχb hχs
  have ht := hL (fun x => (χ x:ℂ)) (continuous_ofReal.comp hχ)
    (by exact_mod_cast hχ0) (fun x => by simpa only [norm_real,Real.norm_eq_abs] using hχb x)
    (fun x hx => hχs x (ofReal_ne_zero.mp hx))
  have hs := (continuous_star.tendsto _).comp ht
  have hlim := hs.const_mul (-((-1:ℂ)^derivativeOrder (n+1)))
  have he : (fun ε : ℝ => ε •
        (deriv^[derivativeOrder (n+1)] (negativeCriticalTwoChartIntegral (Real.pi-α) χ))
          (radialParameter (Real.pi-α) ε)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun ε : ℝ => -((-1:ℂ)^derivativeOrder (n+1))*star
        (ε • (deriv^[derivativeOrder (n+1)] (angularTwoChartIntegral α (fun x => (χ x:ℂ)) ))
          (radialParameter α ε))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0<ε := hε
    have hnorm : 1<‖radialParameter α ε‖ := by rw [radialParameter_norm hεpos.le];linarith
    rw [IsingBulk.HT.Contour.radialParameter_neg_conjugate,
      ←iteratedDeriv_eq_iterate,negativeCriticalTwoChartIntegral_iteratedDeriv ho α χ _ hnorm]
    simp only [real_smul,star_mul',Complex.star_def,Complex.conj_ofReal]
    rw [iteratedDeriv_eq_iterate]
    ring
  apply Tendsto.congr' he.symm
  simpa only [signedCriticalLeadingCoefficient,neg_mul,Function.comp_def] using hlim

/-- Applying the physical signed reflection twice restores the exact original
coefficient, including its derivative parity and complex phase. -/
theorem signed_reflection_coefficient_involution (k : ℕ) (z : ℂ) :
    -((-1:ℂ)^k * star (-((-1:ℂ)^k * star z)))=z := by
  simp only [star_neg,star_mul',star_pow,star_neg,star_one,star_star]
  have h : (-1:ℂ)^k*(-1:ℂ)^k=1 := by rw [←mul_pow];simp
  calc
    -((-1:ℂ)^k * -((-1:ℂ)^k * z)) = ((-1:ℂ)^k*(-1:ℂ)^k)*z := by ring
    _ = z := by rw [h,one_mul]

theorem signedCriticalLeadingCoefficient_transfer_back (p : ℕ) (α : ℝ) :
    -((-1:ℂ)^derivativeOrder p * star (signedCriticalLeadingCoefficient p α))=
      equalAngleLeadingCoefficient p α :=
  signed_reflection_coefficient_involution _ _

/-- One actual lower signed critical chart has exactly half the coefficient.
The physical decomposition supplies the other factor two, not a cutoff symmetry. -/
theorem negativeCritical_lower_limit {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    ∃ R : ℝ,0<R ∧ ∀ χ : ShapeSpace n → ℝ,
      Continuous χ → χ 0=1 → (∀ x,|χ x|≤1) → (∀ x,χ x≠0 → ‖x‖<R) →
      Tendsto (fun ε : ℝ => ε •
        (deriv^[derivativeOrder (n+1)] (negativeCriticalLocalIntegral (Real.pi-α) χ))
          (radialParameter (Real.pi-α) ε))
        (𝓝[>] 0) (𝓝 ((1/2:ℂ)*signedCriticalLeadingCoefficient (n+1) α)) := by
  obtain ⟨_,R,hR,hL⟩ := negativeCritical_two_chart_limit hn ho α hα hαπ hc ha
  refine ⟨R,hR,?_⟩
  intro χ hχ hχ0 hχb hχs
  have ht := (hL χ hχ hχ0 hχb hχs).const_mul (1/2:ℂ)
  convert ht using 1
  funext ε
  rw [negativeCriticalTwoChartIntegral_eq_twice,iterate_deriv_const_mul]
  simp only [real_smul]
  ring

theorem negativeCritical_two_chart_asymptotic {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    ∃ R : ℝ,0<R ∧ ∀ χ : ShapeSpace n → ℝ,
      Continuous χ → χ 0=1 → (∀ x,|χ x|≤1) → (∀ x,χ x≠0 → ‖x‖<R) →
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun ε => (deriv^[derivativeOrder (n+1)]
          (negativeCriticalTwoChartIntegral (Real.pi-α) χ))
          (radialParameter (Real.pi-α) ε)-(ε:ℂ)⁻¹*signedCriticalLeadingCoefficient (n+1) α)
        (fun ε => (ε:ℂ)⁻¹) := by
  obtain ⟨_,R,hR,hL⟩ := negativeCritical_two_chart_limit hn ho α hα hαπ hc ha
  exact ⟨R,hR,fun χ hχ hχ0 hχb hχs =>
    normalized_epsilon_limit_isLittleO (hL χ hχ hχ0 hχb hχs)⟩

end
end IsingBulk.HT22.LocalLimit
