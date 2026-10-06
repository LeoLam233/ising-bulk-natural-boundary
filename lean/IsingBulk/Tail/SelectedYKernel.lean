import IsingBulk.Tail.SelectorPeriodicity
import IsingBulk.Tail.SimpleKernelBounds

/-! Selected-contour y-Schur bounds with the coupled occupancy retained.
An m-supported variable has a uniformly bounded pair with every partner;
the remaining pairs compare to the original periodic scalar kernel. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

 def phaseChord (t : ℝ) : ℝ := ‖Complex.exp (Complex.I*(t:ℂ))-1‖

 theorem phase_chord_le_twice_denominator_all {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    phaseChord t ≤ 2*phaseDenominator r t := by
  let E := Complex.exp (Complex.I*(t:ℂ))
  have he : ‖E‖=1 := by simp [E]
  have hn : ‖E-(r:ℂ)*E‖=|1-r| := by
    rw [show E-(r:ℂ)*E=(1-(r:ℂ))*E by ring,norm_mul,he,mul_one]
    norm_cast
  have hg : |1-r| ≤ phaseDenominator r t := by
    have hh := abs_norm_sub_norm_le (1:ℂ) ((r:ℂ)*E)
    simpa only [norm_one,norm_mul,he,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hr,phaseDenominator,E] using hh
  have ht := norm_add_le (E-(r:ℂ)*E) ((r:ℂ)*E-1)
  rw [show (E-(r:ℂ)*E)+((r:ℂ)*E-1)=E-1 by ring,hn,norm_sub_rev ((r:ℂ)*E) 1] at ht
  change phaseChord t ≤ |1-r|+phaseDenominator r t at ht
  linarith

 theorem sine_sum_le_phaseChord (x y : ℝ) : |Real.sin x+Real.sin y| ≤ phaseChord (x+y) := by
  rw [Real.sin_add_sin]
  unfold phaseChord
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [Real.norm_eq_abs,abs_mul]
  norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hh := Real.abs_cos_le_one ((x-y)/2)
  nlinarith [abs_nonneg (Real.sin ((x+y)/2))]

 theorem shift_le_half_tau {N : ℕ} (hN : 0 < N) {τ : ℝ} (hτ : 0 ≤ τ)
    (p m : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (_hm0 : ∀ i, 0 ≤ m i) (hm1 : ∀ i, m i ≤ 1) (i : Fin N) :
    retractionShift τ p m i ≤ τ/2 := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hP0 := occupancy_nonneg hp0
  have hP1 := occupancy_le hp1
  have ha0 : 0 ≤ τ*occupancy p/(2*N) := by positivity
  have ha1 : τ*occupancy p/(2*N) ≤ τ/2 := by
    apply (div_le_iff₀ (show 0 < (2:ℝ)*N by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hP1 hτ]
  have hh := mul_le_mul_of_nonneg_left (hm1 i) ha0
  unfold retractionShift
  nlinarith [mul_nonneg hτ (hp0 i)]

 theorem constructed_shift_le_half {N : ℕ} (hN : 0 < N) {τ : ℝ} (hτ : 0 ≤ τ)
    (b η α : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    shiftMap (constructedSelector b η α) τ θ i ≤ τ/2 := by
  apply shift_le_half_tau hN hτ
  · intro j; exact (thresholdStep_range _ _ _).1
  · intro j; exact (thresholdStep_range _ _ _).2
  · intro j; exact Real.smoothTransition.nonneg _
  · intro j; exact Real.smoothTransition.le_one _

 theorem m_supported_reciprocal_partner {N : ℕ} (b η α : ℝ)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (θ : Fin N → ℝ) (i j : Fin N)
    (hm : (constructedSelector b η α).m (θ i) ≠ 0)
    (hchord : phaseChord (θ i+θ j) < Real.sin b/4) :
    (constructedSelector b η α).p (θ j)=1 ∧ (constructedSelector b η α).m (θ j)=0 := by
  have hlow := lowerM_support_negative b η hb hη hηsmall (θ i) (subset_closure hm)
  have hsum := sine_sum_le_phaseChord (θ i) (θ j)
  have hsin : Real.sin b/4 < Real.sin (θ j) := by
    have hh := (abs_le.mp hsum).1
    linarith
  constructor
  · exact thresholdStep_one (by linarith) (by linarith)
  · exact lowerM_zero_of_nonneg_sine b η (θ j) hb hη hηsmall (by linarith)

 theorem m_supported_reciprocal_shift {N : ℕ} (hN : 0 < N) {τ : ℝ} (hτ : 0 ≤ τ)
    (b η α : ℝ) (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (θ : Fin N → ℝ) (i j : Fin N)
    (hm : (constructedSelector b η α).m (θ i) ≠ 0)
    (hchord : phaseChord (θ i+θ j) < Real.sin b/4) :
    shiftMap (constructedSelector b η α) τ θ i+shiftMap (constructedSelector b η α) τ θ j ≤ -3*τ/2 := by
  obtain ⟨hpj,hmj⟩ := m_supported_reciprocal_partner b η α hb hη hηsmall hα hαsmall θ i j hm hchord
  have hj : shiftMap (constructedSelector b η α) τ θ j = -2*τ :=
    retractionShift_named τ _ _ j hpj hmj
  rw [hj]
  linarith [constructed_shift_le_half hN hτ b η α θ i]

 def selectedYRadius {N : ℕ} (f : SelectorFunctions) (r τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℝ :=
  r*Real.exp (shiftMap f τ θ i)

 theorem selectedY_radius_representation {N : ℕ} (f : SelectorFunctions) (r τ : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    deformedPoint f r τ 1 θ i = (selectedYRadius f r τ θ i:ℂ)*Complex.exp (Complex.I*(θ i:ℂ)) := by
  rw [deformedPoint_eq_angle]
  simp only [one_mul,anglePoint,circleMap,zero_add,selectedYRadius,Complex.ofReal_mul,Complex.ofReal_exp]
  rw [mul_comm (θ i:ℂ) Complex.I]
  ring

 theorem selectedY_product_radius {N : ℕ} (f : SelectorFunctions) (r τ : ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    selectedYRadius f r τ θ i*selectedYRadius f r τ θ j =
      r^2*Real.exp (shiftMap f τ θ i+shiftMap f τ θ j) := by
  simp only [selectedYRadius,Real.exp_add]
  ring

 theorem selectedY_pair_denominator {N : ℕ} (f : SelectorFunctions) (r τ : ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    ‖1-deformedPoint f r τ 1 θ i*deformedPoint f r τ 1 θ j‖ =
      phaseDenominator (selectedYRadius f r τ θ i*selectedYRadius f r τ θ j) (θ i+θ j) := by
  rw [selectedY_radius_representation,selectedY_radius_representation]
  unfold phaseDenominator
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_add,mul_add,Complex.exp_add]
  ring

 theorem selectedY_norm_le {N : ℕ} (hN : 0 < N) (b η α : ℝ) {r τ : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i : Fin N) :
    ‖deformedPoint (constructedSelector b η α) r τ 1 θ i‖ ≤ Real.exp (τ/2) := by
  rw [deformedPoint_norm _ hr]
  simp only [one_mul]
  have he := Real.exp_le_exp.mpr (constructed_shift_le_half hN hτ b η α θ i)
  calc
    _ ≤ 1*Real.exp (shiftMap (constructedSelector b η α) τ θ i) :=
      mul_le_mul_of_nonneg_right hr1 (Real.exp_pos _).le
    _ ≤ Real.exp (τ/2) := by simpa using he

 theorem selectedY_numerator_le {N : ℕ} (hN : 0 < N) (b η α : ℝ) {r τ : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i j : Fin N) :
    ‖deformedPoint (constructedSelector b η α) r τ 1 θ i-
      deformedPoint (constructedSelector b η α) r τ 1 θ j‖ ≤ 2*Real.exp (τ/2) := by
  exact (norm_sub_le _ _).trans (by
    linarith [selectedY_norm_le hN b η α hr hr1 hτ θ i,selectedY_norm_le hN b η α hr hr1 hτ θ j])

 def selectedYPairGap (b τ : ℝ) : ℝ := min (1-Real.exp (-3*τ/2)) (Real.sin b/8)

 theorem selectedYPairGap_pos {b τ : ℝ} (hb : 0 < Real.sin b) (hτ : 0 < τ) :
    0 < selectedYPairGap b τ := by
  apply lt_min
  · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  · positivity

 theorem selected_m_pair_denominator_lower {N : ℕ} (hN : 0 < N)
    (b η α : ℝ) (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4) {r τ : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hτ : 0 < τ)
    (θ : Fin N → ℝ) (i j : Fin N) (hm : (constructedSelector b η α).m (θ i) ≠ 0) :
    selectedYPairGap b τ ≤ ‖1-deformedPoint (constructedSelector b η α) r τ 1 θ i*
      deformedPoint (constructedSelector b η α) r τ 1 θ j‖ := by
  let f := constructedSelector b η α
  let ρ := selectedYRadius f r τ θ i*selectedYRadius f r τ θ j
  have hρ : 0 ≤ ρ := by dsimp [ρ,selectedYRadius]; positivity
  rw [selectedY_pair_denominator]
  change selectedYPairGap b τ ≤ phaseDenominator ρ (θ i+θ j)
  by_cases hc : phaseChord (θ i+θ j) < Real.sin b/4
  · have hshift := m_supported_reciprocal_shift hN hτ.le b η α hb hη hηsmall hα hαsmall θ i j hm hc
    have hρbound : ρ ≤ Real.exp (-3*τ/2) := by
      dsimp [ρ]
      rw [selectedY_product_radius]
      have hs := Real.exp_le_exp.mpr hshift
      have hr2 : r^2 ≤ 1 := by nlinarith
      calc
        _ ≤ r^2*Real.exp (-3*τ/2) := mul_le_mul_of_nonneg_left hs (sq_nonneg r)
        _ ≤ 1*Real.exp (-3*τ/2) := mul_le_mul_of_nonneg_right hr2 (Real.exp_pos _).le
        _ = _ := one_mul _
    have hg := radial_deficit_le_phaseDenominator hρ (θ i+θ j)
    exact (min_le_left _ _).trans (by linarith)
  · have hphase := phase_chord_le_twice_denominator_all hρ (θ i+θ j)
    exact (min_le_right _ _).trans (by push Not at hc; linarith)

 def selectedYPairConstant (b τ : ℝ) : ℝ := 2*Real.exp (τ/2)/selectedYPairGap b τ

 theorem selected_m_pair_norm_le {N : ℕ} (hN : 0 < N)
    (b η α : ℝ) (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4) {r τ : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hτ : 0 < τ)
    (θ : Fin N → ℝ) (i j : Fin N) (hm : (constructedSelector b η α).m (θ i) ≠ 0) :
    ‖pairKernel (deformedPoint (constructedSelector b η α) r τ 1 θ i)
      (deformedPoint (constructedSelector b η α) r τ 1 θ j)‖ ≤ selectedYPairConstant b τ := by
  have hgap := selected_m_pair_denominator_lower hN b η α hb hη hηsmall hα hαsmall hr hr1 hτ θ i j hm
  have hp := selectedYPairGap_pos hb hτ
  rw [pairKernel,norm_div]
  exact div_le_div₀ (by positivity) (selectedY_numerator_le hN b η α hr hr1 hτ.le θ i j) hp hgap

 theorem pairKernel_norm_swap (a b : ℂ) : ‖pairKernel a b‖=‖pairKernel b a‖ := by
  simp only [pairKernel,norm_div]
  rw [norm_sub_rev a b,mul_comm a b]

 theorem selected_no_m_product_radius_le {N : ℕ} (b η α : ℝ) {r τ : ℝ}
    (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i j : Fin N)
    (hmi : (constructedSelector b η α).m (θ i)=0)
    (hmj : (constructedSelector b η α).m (θ j)=0) :
    selectedYRadius (constructedSelector b η α) r τ θ i*
      selectedYRadius (constructedSelector b η α) r τ θ j ≤ r^2 := by
  rw [selectedY_product_radius]
  have hp0 (k : Fin N) : 0 ≤ (constructedSelector b η α).p (θ k) :=
    (thresholdStep_range _ _ _).1
  have hs : shiftMap (constructedSelector b η α) τ θ i+
      shiftMap (constructedSelector b η α) τ θ j ≤ 0 := by
    simp only [shiftMap,retractionShift,hmi,hmj,mul_zero,add_zero]
    nlinarith [mul_nonneg hτ (hp0 i),mul_nonneg hτ (hp0 j)]
  have he := Real.exp_le_one_iff.mpr hs
  simpa using mul_le_mul_of_nonneg_left he (sq_nonneg r)

 def selectedYKernelMajorant (b τ r t : ℝ) : ℝ :=
  selectedYPairConstant b τ+4*Real.exp (τ/2)/phaseDenominator (r^2) t

 theorem selected_y_pair_majorant {N : ℕ} (hN : 0 < N)
    (b η α : ℝ) (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4) {r τ : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hτ : 0 < τ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    ‖pairKernel (deformedPoint (constructedSelector b η α) r τ 1 θ i)
      (deformedPoint (constructedSelector b η α) r τ 1 θ j)‖ ≤
        selectedYKernelMajorant b τ r (θ i+θ j) := by
  have hK : 0 ≤ selectedYPairConstant b τ := by
    unfold selectedYPairConstant
    exact div_nonneg (by positivity) (selectedYPairGap_pos hb hτ).le
  have hD : 0 ≤ phaseDenominator (r^2) (θ i+θ j) := norm_nonneg _
  have hextra : 0 ≤ 4*Real.exp (τ/2)/phaseDenominator (r^2) (θ i+θ j) := by positivity
  by_cases hmi : (constructedSelector b η α).m (θ i)=0
  · by_cases hmj : (constructedSelector b η α).m (θ j)=0
    · let ρ := selectedYRadius (constructedSelector b η α) r τ θ i*
        selectedYRadius (constructedSelector b η α) r τ θ j
      have hρ : 0 ≤ ρ := by dsimp [ρ,selectedYRadius]; positivity
      have hρle : ρ ≤ r^2 := selected_no_m_product_radius_le b η α hτ.le θ i j hmi hmj
      have hr2 : r^2 < 1 := by nlinarith
      have hInv := simple_kernel_radius_floor (t := θ i+θ j) hρ hρle hr2
      rw [pairKernel,norm_div,selectedY_pair_denominator,div_eq_mul_inv]
      change ‖deformedPoint (constructedSelector b η α) r τ 1 θ i-
        deformedPoint (constructedSelector b η α) r τ 1 θ j‖*(phaseDenominator ρ (θ i+θ j))⁻¹ ≤ _
      calc
        _ ≤ (2*Real.exp (τ/2))*(2*(phaseDenominator (r^2) (θ i+θ j))⁻¹) :=
          mul_le_mul (selectedY_numerator_le hN b η α hr hr1.le hτ.le θ i j) hInv
            (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
        _ = 4*Real.exp (τ/2)/phaseDenominator (r^2) (θ i+θ j) := by ring
        _ ≤ selectedYKernelMajorant b τ r (θ i+θ j) := by unfold selectedYKernelMajorant; linarith
    · rw [pairKernel_norm_swap]
      exact (selected_m_pair_norm_le hN b η α hb hη hηsmall hα hαsmall hr hr1.le hτ θ j i hmj).trans
        (by unfold selectedYKernelMajorant; linarith)
  · exact (selected_m_pair_norm_le hN b η α hb hη hηsmall hα hαsmall hr hr1.le hτ θ i j hmi).trans
      (by unfold selectedYKernelMajorant; linarith)

 theorem selected_y_pair_denominator_ne_zero {N : ℕ} (hN : 0 < N)
    (b η α : ℝ) (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4) {r τ : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hτ : 0 < τ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    1-deformedPoint (constructedSelector b η α) r τ 1 θ i*
      deformedPoint (constructedSelector b η α) r τ 1 θ j ≠ 0 := by
  apply norm_pos_iff.mp
  by_cases hmi : (constructedSelector b η α).m (θ i)=0
  · by_cases hmj : (constructedSelector b η α).m (θ j)=0
    · rw [selectedY_pair_denominator]
      have hρ : 0 ≤ selectedYRadius (constructedSelector b η α) r τ θ i*
          selectedYRadius (constructedSelector b η α) r τ θ j := by unfold selectedYRadius; positivity
      have hl := selected_no_m_product_radius_le (r := r) b η α hτ.le θ i j hmi hmj
      have hg := radial_deficit_le_phaseDenominator hρ (θ i+θ j)
      have hr2 : r^2 < 1 := by nlinarith
      linarith
    · rw [mul_comm (deformedPoint (constructedSelector b η α) r τ 1 θ i)
        (deformedPoint (constructedSelector b η α) r τ 1 θ j)]
      exact (selectedYPairGap_pos hb hτ).trans_le
        (selected_m_pair_denominator_lower hN b η α hb hη hηsmall hα hαsmall hr hr1.le hτ θ j i hmj)
  · exact (selectedYPairGap_pos hb hτ).trans_le
      (selected_m_pair_denominator_lower hN b η α hb hη hηsmall hα hαsmall hr hr1.le hτ θ i j hmi)

 theorem selected_any_m_pair_norm_le {N : ℕ} (hN : 0 < N)
    (b η α : ℝ) (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4) {r τ : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hτ : 0 < τ)
    (θ : Fin N → ℝ) (i j : Fin N)
    (hm : (constructedSelector b η α).m (θ i) ≠ 0 ∨ (constructedSelector b η α).m (θ j) ≠ 0) :
    ‖pairKernel (deformedPoint (constructedSelector b η α) r τ 1 θ i)
      (deformedPoint (constructedSelector b η α) r τ 1 θ j)‖ ≤ selectedYPairConstant b τ := by
  rcases hm with hm | hm
  · exact selected_m_pair_norm_le hN b η α hb hη hηsmall hα hαsmall hr hr1 hτ θ i j hm
  · rw [pairKernel_norm_swap]
    exact selected_m_pair_norm_le hN b η α hb hη hηsmall hα hαsmall hr hr1 hτ θ j i hm

 theorem selectedYKernelMajorant_nonneg {b τ r : ℝ} (hb : 0 < Real.sin b) (hτ : 0 < τ) (t : ℝ) :
    0 ≤ selectedYKernelMajorant b τ r t := by
  unfold selectedYKernelMajorant selectedYPairConstant
  have hg := (selectedYPairGap_pos hb hτ).le
  have hden : 0 ≤ phaseDenominator (r^2) t := norm_nonneg _
  positivity

 theorem selectedYKernelMajorant_periodic (b τ r : ℝ) :
    Function.Periodic (selectedYKernelMajorant b τ r) (2*Real.pi) := by
  intro t
  unfold selectedYKernelMajorant
  rw [phaseDenominator_periodic]

 theorem selectedYKernelMajorant_continuous (b τ : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (selectedYKernelMajorant b τ r) := by
  have hr2 : r^2 < 1 := by nlinarith
  have hd : Continuous (phaseDenominator (r^2)) := by unfold phaseDenominator; fun_prop
  have hn : ∀ t, phaseDenominator (r^2) t ≠ 0 := by
    intro t
    have hh := radial_deficit_le_phaseDenominator (sq_nonneg r) t
    exact ne_of_gt (by linarith)
  exact continuous_const.add (continuous_const.div hd hn)

 theorem selected_y_kernel_period_integral (b τ : ℝ) {c₀ eps : ℝ}
    (hc : 0 < c₀) (heps : 0 < eps) (hsmall : 2*c₀*eps ≤ 1) (t₀ : ℝ) :
    (∫ t : ℝ in t₀..t₀+2*Real.pi,
      selectedYKernelMajorant b τ (Real.exp (-c₀*eps)) t) ≤
      2*Real.pi*selectedYPairConstant b τ+
        4*Real.exp (τ/2)*simpleKernelConstant*(1+|Real.log (2*c₀*eps)|) := by
  let r := Real.exp (-c₀*eps)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hc heps])
  have hr2 : r^2 < 1 := by nlinarith
  have hd : Continuous (phaseDenominator (r^2)) := by unfold phaseDenominator; fun_prop
  have hn : ∀ t, phaseDenominator (r^2) t ≠ 0 := by
    intro t
    have hh := radial_deficit_le_phaseDenominator (sq_nonneg r) t
    exact ne_of_gt (by linarith)
  have hk : Continuous (fun t => (2:ℝ)/phaseDenominator (r^2) t) := continuous_const.div hd hn
  have he : selectedYKernelMajorant b τ r =
      (fun t => selectedYPairConstant b τ+(2*Real.exp (τ/2))*(2/phaseDenominator (r^2) t)) := by
    funext t
    unfold selectedYKernelMajorant
    ring
  change (∫ t : ℝ in t₀..t₀+2*Real.pi, selectedYKernelMajorant b τ r t) ≤ _
  have hint : IntervalIntegrable (fun t => (2*Real.exp (τ/2))*(2/phaseDenominator (r^2) t))
      MeasureTheory.volume t₀ (t₀+2*Real.pi) :=
    (hk.intervalIntegrable _ _).const_mul _
  rw [he]
  dsimp only
  rw [intervalIntegral.integral_add intervalIntegrable_const hint,intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  have hb := original_y_kernel_period_integral hc heps hsmall t₀
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*Real.exp (τ/2) by positivity)
  simp only [smul_eq_mul] at *
  dsimp [r] at *
  nlinarith

/-- The exceptional scalar kernel is needed only when both vertices lie off
the exact lower branch plateau. The mask is used only after differentiation. -/
theorem selected_y_pair_compact_split {N : ℕ} (hN : 0 < N)
    (b η α : ℝ) (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4) {r τ : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hτ : 0 < τ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    ‖pairKernel (deformedPoint (constructedSelector b η α) r τ 1 θ i)
      (deformedPoint (constructedSelector b η α) r τ 1 θ j)‖ ≤
      selectedYPairConstant b τ +
        if (constructedSelector b η α).m (θ i) ≠ 1 ∧
          (constructedSelector b η α).m (θ j) ≠ 1
        then 4*Real.exp (τ/2)/phaseDenominator (r^2) (θ i+θ j) else 0 := by
  classical
  by_cases hh : (constructedSelector b η α).m (θ i) ≠ 1 ∧
      (constructedSelector b η α).m (θ j) ≠ 1
  · rw [ite_eq_left hh]
    exact selected_y_pair_majorant hN b η α hb hη hηsmall hα hαsmall hr hr1 hτ θ i j
  · rw [ite_eq_right hh,add_zero]
    apply selected_any_m_pair_norm_le hN b η α hb hη hηsmall hα hαsmall hr hr1.le hτ θ i j
    by_cases hi : (constructedSelector b η α).m (θ i) = 1
    · exact Or.inl (by rw [hi]; norm_num)
    · have hj : (constructedSelector b η α).m (θ j) = 1 := by tauto
      exact Or.inr (by rw [hj]; norm_num)

/-- Any compact mask containing the complement of the exact branch core is
allowed; in particular the manuscript chord-threshold compact set. -/
theorem selected_y_pair_mask_split {N : ℕ} (hN : 0 < N)
    (b η α : ℝ) (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4) {r τ : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hτ : 0 < τ)
    (θ : Fin N → ℝ) (c : ℝ → Prop) [DecidablePred c]
    (hc : ∀ t, ¬c t → (constructedSelector b η α).m t ≠ 0) (i j : Fin N) :
    ‖pairKernel (deformedPoint (constructedSelector b η α) r τ 1 θ i)
      (deformedPoint (constructedSelector b η α) r τ 1 θ j)‖ ≤
      selectedYPairConstant b τ + if c (θ i) ∧ c (θ j)
        then 4*Real.exp (τ/2)/phaseDenominator (r^2) (θ i+θ j) else 0 := by
  by_cases hh : c (θ i) ∧ c (θ j)
  · rw [ite_eq_left hh]
    exact selected_y_pair_majorant hN b η α hb hη hηsmall hα hαsmall hr hr1 hτ θ i j
  · rw [ite_eq_right hh,add_zero]
    apply selected_any_m_pair_norm_le hN b η α hb hη hηsmall hα hαsmall hr hr1.le hτ θ i j
    by_cases hi : c (θ i)
    · exact Or.inr (hc _ (fun hj => hh ⟨hi,hj⟩))
    · exact Or.inl (hc _ hi)

end
end IsingBulk.Tail
