import IsingBulk.Tail.OriginalDensityMajorant
import IsingBulk.Tail.SelectedFContinuationIntegral
import IsingBulk.Tail.SelectedFDiscountedWeights
import IsingBulk.Tail.SelectedYKernel
import IsingBulk.Tail.WeightedAngularPfaffian
import IsingBulk.Tail.ExteriorPairBridge

/-! The actual occupancy-coupled selected y Pfaffian is bounded only after
pointwise domination by a common measurable two-angle kernel. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory Set
open scoped BigOperators Topology

theorem pairProduct_eq_labelPfaffian_of_denominators (n : ℕ) (y : Fin (2*n) → ℂ)
    (hd : ∀ i j, 1-y i*y j ≠ 0) :
    First.pairProduct y = labelPfaffian (fun a b => pairKernel (y a) (y b)) n
      (List.finRange (2*n)) := by
  rw [labelPfaffian_source,← List.ofFn_eq_map,pairProduct_eq_schur]
  exact (Schur.schur_fraction_specialization n y hd).symm

def selectedExceptionalKernel (τ r t : ℝ) : ℝ :=
  4*Real.exp (τ/2)/phaseDenominator (r^2) t

def selectedMaskedKernel (b η τ r x y : ℝ) : ℝ :=
  selectedYPairConstant b τ + if η^2/2 ≤ lowerChord b x ∧ η^2/2 ≤ lowerChord b y
    then selectedExceptionalKernel τ r (x+y) else 0

theorem selectedExceptionalKernel_nonneg (τ r t : ℝ) :
    0 ≤ selectedExceptionalKernel τ r t := by unfold selectedExceptionalKernel phaseDenominator; positivity

theorem selectedExceptionalKernel_continuous (τ : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (selectedExceptionalKernel τ r) := by
  have hr2 : r^2 < 1 := by nlinarith
  apply continuous_const.div
  · unfold phaseDenominator
    fun_prop
  · intro t
    have hh := radial_deficit_le_phaseDenominator (sq_nonneg r) t
    exact ne_of_gt (by linarith)

theorem selectedExceptionalKernel_periodic (τ r : ℝ) :
    Function.Periodic (selectedExceptionalKernel τ r) (2*Real.pi) := by
  intro t
  unfold selectedExceptionalKernel
  rw [phaseDenominator_periodic]

theorem selectedMaskedKernel_nonneg {b τ : ℝ} (hb : 0 < Real.sin b) (hτ : 0 < τ)
    (η r x y : ℝ) : 0 ≤ selectedMaskedKernel b η τ r x y := by
  have hK : 0 ≤ selectedYPairConstant b τ := by
    unfold selectedYPairConstant
    exact div_nonneg (by positivity) (selectedYPairGap_pos hb hτ).le
  unfold selectedMaskedKernel
  split_ifs
  · exact add_nonneg hK (selectedExceptionalKernel_nonneg _ _ _)
  · simpa using hK

theorem discountedSelectedWeight_measurable (b η C eps L : ℝ) :
    Measurable (discountedSelectedWeight b η C eps L) := by
  unfold discountedSelectedWeight
  apply Measurable.ite
  · exact (isClosed_le continuous_const (by unfold lowerChord; fun_prop)).measurableSet
  · exact measurable_const
  · fun_prop

theorem selectedMaskedKernel_measurable (b η τ r : ℝ) :
    Measurable (Function.uncurry (selectedMaskedKernel b η τ r)) := by
  unfold Function.uncurry selectedMaskedKernel selectedExceptionalKernel phaseDenominator
  apply Measurable.add measurable_const
  apply Measurable.ite
  · apply MeasurableSet.inter
    · exact (isClosed_le (f := fun _ : ℝ × ℝ => η^2/2)
        (g := fun p => lowerChord b p.1) continuous_const (by unfold lowerChord; fun_prop)).measurableSet
    · exact (isClosed_le (f := fun _ : ℝ × ℝ => η^2/2)
        (g := fun p => lowerChord b p.2) continuous_const (by unfold lowerChord; fun_prop)).measurableSet
  · fun_prop
  · exact measurable_const

theorem selected_discounted_pair_integral {b η C eps L τ r D : ℝ}
    (hb : 0 ≤ b) (hbT : b ≤ 2*Real.pi) (hbs : 0 < Real.sin b)
    (hC : 0 ≤ C) (heps : 0 < eps) (hL : 1 ≤ L) (hτ : 0 < τ)
    (hr : 0 ≤ r) (hr1 : r < 1) (hD : 0 ≤ D)
    (hKL : (∫ t in Icc 0 (2*Real.pi),selectedExceptionalKernel τ r t) ≤ D*L) :
    let w := discountedSelectedWeight b η C eps L
    let f := fun x y => w x*w y*selectedMaskedKernel b η τ r x y
    IntegrableOn (Function.uncurry f) (Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi)) ∧
    (∫ p in Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi),f p.1 p.2) ≤
      selectedYPairConstant b τ*(4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^2+
        C^2*(2*Real.pi)*D := by
  obtain ⟨hwi,hw0,hwc,hwA⟩ := discountedSelectedWeight_integrable hb hbT hC heps hL (η := η)
  dsimp only
  let w := discountedSelectedWeight b η C eps L
  have hm : Measurable (fun p : ℝ × ℝ => w p.1*w p.2*selectedMaskedKernel b η τ r p.1 p.2) :=
    (((discountedSelectedWeight_measurable b η C eps L).comp measurable_fst).mul
      ((discountedSelectedWeight_measurable b η C eps L).comp measurable_snd)).mul
      (selectedMaskedKernel_measurable b η τ r)
  have hp := selected_weighted_pair_integral_le (T := 2*Real.pi) (K₀ := selectedYPairConstant b τ)
    (d := C/L) (by positivity) hwi (selectedExceptionalKernel_continuous τ hr hr1)
    (selectedExceptionalKernel_periodic τ r) hm.aestronglyMeasurable
    (fun p => mul_nonneg (mul_nonneg (hw0 p.1) (hw0 p.2))
      (selectedMaskedKernel_nonneg hbs hτ η r p.1 p.2))
    (fun p => discounted_pair_pointwise hw0 (div_nonneg hC (by linarith))
      (selectedExceptionalKernel_nonneg τ r) (fun x hx => (hwc x hx).le)
      (fun x y => le_rfl) p.1 p.2)
  refine ⟨hp.1,hp.2.trans ?_⟩
  apply selected_discount_uniform _ hC (by positivity) hD _ hwA hKL hL
  · unfold selectedYPairConstant
    exact div_nonneg (by positivity) (selectedYPairGap_pos hbs hτ).le
  · exact integral_nonneg hw0

theorem selected_actual_y_weighted_integral {n : ℕ} (hn : 0 < n)
    {b η α C eps L τ r D : ℝ}
    (hb : 0 ≤ b) (hbT : b ≤ 2*Real.pi) (hbs : 0 < Real.sin b)
    (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (hC : 0 ≤ C) (heps : 0 < eps) (hL : 1 ≤ L) (hτ : 0 < τ)
    (hr : 0 ≤ r) (hr1 : r < 1) (hD : 0 ≤ D)
    (hKL : (∫ t in Icc 0 (2*Real.pi),selectedExceptionalKernel τ r t) ≤ D*L) :
    Integrable (fun θ : Fin (2*n) → ℝ =>
      (∏ i,discountedSelectedWeight b η C eps L (θ i))*
        ‖First.pairProduct (deformedPoint (constructedSelector b η α) r τ 1 θ)‖)
      (Measure.pi (fun _ => volume.restrict (Icc 0 (2*Real.pi)))) ∧
    (∫ θ : Fin (2*n) → ℝ,
      (∏ i,discountedSelectedWeight b η C eps L (θ i))*
        ‖First.pairProduct (deformedPoint (constructedSelector b η α) r τ 1 θ)‖
      ∂Measure.pi (fun _ => volume.restrict (Icc 0 (2*Real.pi)))) ≤
      (matchingCount n:ℝ)*(selectedYPairConstant b τ*
        (4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^2+C^2*(2*Real.pi)*D)^n := by
  let f := constructedSelector b η α
  let w := discountedSelectedWeight b η C eps L
  let k := selectedMaskedKernel b η τ r
  let A := fun (θ : Fin (2*n) → ℝ) i j => pairKernel
    (deformedPoint f r τ 1 θ i) (deformedPoint f r τ 1 θ j)
  have hN : 0 < 2*n := by omega
  have hy := deformedPoint_continuous (N := 2*n) f r τ 1
    (periodicUpperP_smooth α).continuous (periodicLowerM_smooth b η).continuous
  have hd (θ : Fin (2*n) → ℝ) (i j : Fin (2*n)) :
      1-deformedPoint f r τ 1 θ i*deformedPoint f r τ 1 θ j ≠ 0 :=
    selected_y_pair_denominator_ne_zero hN b η α hbs hη hηsmall hα hαsmall hr hr1 hτ θ i j
  have hAc (i j : Fin (2*n)) : Continuous (fun θ => A θ i j) := by
    apply ((continuous_apply i).comp hy |>.sub ((continuous_apply j).comp hy)).div
      (continuous_const.sub (((continuous_apply i).comp hy).mul ((continuous_apply j).comp hy)))
    exact fun θ => hd θ i j
  have hpf := continuous_labelPfaffian A hAc n (List.finRange (2*n))
  obtain ⟨hwi,hw0,hwc,hwA⟩ := discountedSelectedWeight_integrable hb hbT hC heps hL (η := η)
  have hA (θ : Fin (2*n) → ℝ) (i j : Fin (2*n)) : ‖A θ i j‖ ≤ k (θ i) (θ j) := by
    apply selected_y_pair_mask_split hN b η α hbs hη hηsmall hα hαsmall hr hr1 hτ θ
      (fun t => η^2/2 ≤ lowerChord b t) _ i j
    intro t ht
    have hc : lowerChord b t ≤ η^2 := by linarith [lt_of_not_ge ht,sq_nonneg η]
    rw [(constructed_lower_core_plateau hbs hη hηsmall hα hc).1]
    norm_num
  obtain ⟨hpair,hpairbound⟩ := selected_discounted_pair_integral hb hbT hbs hC heps hL hτ hr hr1 hD hKL (η := η)
  have hmprod : Measurable (fun θ : Fin (2*n) → ℝ =>
      ((List.finRange (2*n)).map (fun i => w (θ i))).prod) := by
    have he (θ : Fin (2*n) → ℝ) :
        ((List.finRange (2*n)).map (fun i => w (θ i))).prod = ∏ i,w (θ i) := by
      rw [← List.ofFn_eq_map,List.prod_ofFn]
    simp_rw [he]
    apply Finset.measurable_fun_prod
    intro i hi
    exact (discountedSelectedWeight_measurable b η C eps L).comp (measurable_pi_apply i)
  have hmain := integral_coupled_weighted_labelPfaffian_le n
    (volume.restrict (Icc (0:ℝ) (2*Real.pi))) w hw0 A k
    (selectedMaskedKernel_nonneg hbs hτ η r) hA
    (selected_pair_pi_integrable _ _ hpair) (hmprod.mul hpf.norm.measurable).aestronglyMeasurable
  have hint := integrable_coupled_weighted_labelPfaffian n
    (volume.restrict (Icc (0:ℝ) (2*Real.pi))) w hw0 A k
    (selectedMaskedKernel_nonneg hbs hτ η r) hA
    (selected_pair_pi_integrable _ _ hpair) (hmprod.mul hpf.norm.measurable).aestronglyMeasurable
  rw [pair_pi_integral_eq_prod (2*Real.pi) (fun x y => w x*w y*k x y)] at hmain
  have he (θ : Fin (2*n) → ℝ) :
      (∏ i,w (θ i))*‖First.pairProduct (deformedPoint f r τ 1 θ)‖ =
      ((List.finRange (2*n)).map (fun i => w (θ i))).prod *
        ‖labelPfaffian (A θ) n (List.finRange (2*n))‖ := by
    rw [pairProduct_eq_labelPfaffian_of_denominators n _ (hd θ),← List.ofFn_eq_map,List.prod_ofFn]
  refine ⟨hint.congr (Filter.Eventually.of_forall (fun θ => (he θ).symm)), ?_⟩
  change (∫ θ : Fin (2*n) → ℝ, (∏ i,w (θ i))*
    ‖First.pairProduct (deformedPoint f r τ 1 θ)‖
    ∂Measure.pi (fun _ => volume.restrict (Icc 0 (2*Real.pi)))) ≤ _
  simp_rw [he]
  apply hmain.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ _ hpairbound
  apply integral_nonneg
  intro p
  exact mul_nonneg (mul_nonneg (hw0 p.1) (hw0 p.2))
    (selectedMaskedKernel_nonneg hbs hτ η r p.1 p.2)

theorem selectedExceptionalKernel_period_integral {c₀ eps : ℝ} (hc : 0 < c₀)
    (heps : 0 < eps) (hsmall : 2*c₀*eps ≤ 1) (τ : ℝ) :
    (∫ t in Icc 0 (2*Real.pi),selectedExceptionalKernel τ (Real.exp (-c₀*eps)) t) ≤
      4*Real.exp (τ/2)*simpleKernelConstant*(1+|Real.log (2*c₀*eps)|) := by
  have he : selectedExceptionalKernel τ (Real.exp (-c₀*eps)) =
      fun t => (2*Real.exp (τ/2))*(2/phaseDenominator ((Real.exp (-c₀*eps))^2) t) := by
    funext t
    unfold selectedExceptionalKernel
    ring
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi),
    he,intervalIntegral.integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left (original_y_kernel_period_integral hc heps hsmall 0)
    (show 0 ≤ 2*Real.exp (τ/2) by positivity)
  simp only [zero_add] at hh
  convert hh using 1; ring

def selectedExceptionalConstant (c₀ τ : ℝ) : ℝ :=
  4*Real.exp (τ/2)*simpleKernelConstant*(1+|Real.log (2*c₀)|)

theorem selectedExceptionalConstant_pos (c₀ τ : ℝ) : 0 < selectedExceptionalConstant c₀ τ := by
  unfold selectedExceptionalConstant
  have := simpleKernelConstant_pos
  positivity

theorem selectedExceptionalKernel_log_bound {c₀ eps L : ℝ} (hc : 0 < c₀)
    (heps : 0 < eps) (hsmall : 2*c₀*eps ≤ 1) (hL : 1+|Real.log eps| ≤ L) (τ : ℝ) :
    (∫ t in Icc 0 (2*Real.pi),selectedExceptionalKernel τ (Real.exp (-c₀*eps)) t) ≤
      selectedExceptionalConstant c₀ τ*L := by
  apply (selectedExceptionalKernel_period_integral hc heps hsmall τ).trans
  have hl : |Real.log (2*c₀*eps)| ≤ |Real.log (2*c₀)|+|Real.log eps| := by
    rw [Real.log_mul (by positivity : 2*c₀≠0) heps.ne']
    exact abs_add_le _ _
  have hg : 1+|Real.log (2*c₀*eps)| ≤ (1+|Real.log (2*c₀)|)*L := by
    have hprod := mul_nonneg (abs_nonneg (Real.log (2*c₀))) (abs_nonneg (Real.log eps))
    have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ 1+|Real.log (2*c₀)| by positivity)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ 4*Real.exp (τ/2)*simpleKernelConstant by
      have := simpleKernelConstant_pos
      positivity)
  exact hm.trans_eq (by unfold selectedExceptionalConstant; ring)

theorem selected_actual_y_weighted_radial_integral {n : ℕ} (hn : 0 < n)
    {b η α C eps L τ c₀ : ℝ}
    (hb : 0 ≤ b) (hbT : b ≤ 2*Real.pi) (hbs : 0 < Real.sin b)
    (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (hC : 0 ≤ C) (hc : 0 < c₀) (heps : 0 < eps) (hsmall : 2*c₀*eps ≤ 1)
    (hL : 1+|Real.log eps| ≤ L) (hτ : 0 < τ) :
    (∫ θ : Fin (2*n) → ℝ,
      (∏ i,discountedSelectedWeight b η C eps L (θ i))*
        ‖First.pairProduct (deformedPoint (constructedSelector b η α) (Real.exp (-c₀*eps)) τ 1 θ)‖
      ∂Measure.pi (fun _ => volume.restrict (Icc 0 (2*Real.pi)))) ≤
      (matchingCount n:ℝ)*(selectedYPairConstant b τ*
        (4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^2+
          C^2*(2*Real.pi)*selectedExceptionalConstant c₀ τ)^n := by
  exact (selected_actual_y_weighted_integral hn hb hbT hbs hη hηsmall hα hαsmall hC heps
    (by linarith [abs_nonneg (Real.log eps)]) hτ (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hc heps]))
    (selectedExceptionalConstant_pos c₀ τ).le
    (selectedExceptionalKernel_log_bound hc heps hsmall hL τ)).2

theorem selected_actual_y_weighted_radial_integrable {n : ℕ} (hn : 0 < n)
    {b η α C eps L τ c₀ : ℝ}
    (hb : 0 ≤ b) (hbT : b ≤ 2*Real.pi) (hbs : 0 < Real.sin b)
    (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (hC : 0 ≤ C) (hc : 0 < c₀) (heps : 0 < eps) (hsmall : 2*c₀*eps ≤ 1)
    (hL : 1+|Real.log eps| ≤ L) (hτ : 0 < τ) :
    Integrable (fun θ : Fin (2*n) → ℝ =>
      (∏ i,discountedSelectedWeight b η C eps L (θ i))*
        ‖First.pairProduct (deformedPoint (constructedSelector b η α) (Real.exp (-c₀*eps)) τ 1 θ)‖)
      (Measure.pi (fun _ => volume.restrict (Icc 0 (2*Real.pi)))) := by
  exact (selected_actual_y_weighted_integral hn hb hbT hbs hη hηsmall hα hαsmall hC heps
    (by linarith [abs_nonneg (Real.log eps)]) hτ (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hc heps]))
    (selectedExceptionalConstant_pos c₀ τ).le
    (selectedExceptionalKernel_log_bound hc heps hsmall hL τ)).1

end
end IsingBulk.Tail
