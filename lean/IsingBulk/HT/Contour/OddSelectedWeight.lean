import IsingBulk.HT.Contour.OddMatching
import IsingBulk.HT.Contour.SelectedWeight

/-! The actual odd selected-y integral. The source contour retains its
coupled occupancy. Its only comparison is the established two-angle kernel,
with a unit addend for the ghost row. No all-N estimate is an input. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch Set MeasureTheory
open scoped BigOperators Topology

/-- The ghost row costs a single inverse one-body mass and one extra matching
pair. This is uniform in every odd particle number, including N=1. -/
theorem odd_selected_y_weighted_integrable_and_bound (n : ℕ)
    {b η α C eps L τ r D : ℝ}
    (hb : 0 ≤ b) (hbT : b ≤ 2*Real.pi) (hbs : 0 < Real.sin b)
    (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (hC : 0 < C) (heps : 0 < eps) (heps1 : eps ≤ 1) (hL : 1 ≤ L)
    (hτ : 0 < τ) (hr : 0 ≤ r) (hr1 : r < 1) (hD : 0 ≤ D)
    (hKL : (∫ t in Icc 0 (2*Real.pi),selectedExceptionalKernel τ r t) ≤ D*L) :
    let w := discountedSelectedWeight b η C eps L
    let V := (selectedYPairConstant b τ+1)*
      (4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^2+C^2*(2*Real.pi)*D
    Integrable (fun θ : Fin (2*n+1) → ℝ => (∏ i,w (θ i))*
      ‖First.pairProduct (deformedPoint (constructedSelector b η α) r τ 1 θ)‖)
      (Measure.pi (fun _ => volume.restrict (Icc 0 (2*Real.pi)))) ∧
    (∫ θ : Fin (2*n+1) → ℝ, (∏ i,w (θ i))*
      ‖First.pairProduct (deformedPoint (constructedSelector b η α) r τ 1 θ)‖
      ∂Measure.pi (fun _ => volume.restrict (Icc 0 (2*Real.pi)))) ≤
      (matchingCount (n+1):ℝ)*V^(n+1)*
        (L*(2*Real.pi+1)/((2*Real.pi)*C)) := by
  have hL0 : 0 < L := by linarith
  let f := constructedSelector b η α
  let w := discountedSelectedWeight b η C eps L
  let k := selectedMaskedKernel b η τ r
  let μ := volume.restrict (Icc (0:ℝ) (2*Real.pi))
  let Y := fun θ : Fin (2*n+1) → ℝ => deformedPoint f r τ 1 θ
  let W := 4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi)
  let V := (selectedYPairConstant b τ+1)*W^2+C^2*(2*Real.pi)*D
  obtain ⟨hwi,hw0,_,hwA⟩ := discountedSelectedWeight_integrable hb hbT hC.le heps hL (η := η)
  have hd (θ : Fin (2*n+1) → ℝ) (i j : Fin (2*n+1)) :
      1-Y θ i*Y θ j ≠ 0 :=
    selected_y_pair_denominator_ne_zero (by omega) b η α hbs hη hηsmall hα hαsmall hr hr1 hτ θ i j
  have hg (θ : Fin (2*n+1) → ℝ) (i : Fin (2*n+1)) : Y θ i ≠ -1 := by
    intro he
    have hh := hd θ i i
    norm_num [he] at hh
  have hA (θ : Fin (2*n+1) → ℝ) (i j : Fin (2*n+1)) :
      ‖pairKernel (Y θ i) (Y θ j)‖ ≤ k (θ i) (θ j) := by
    apply selected_y_pair_mask_split (by omega : 0 < 2*n+1)
      b η α hbs hη hηsmall hα hαsmall hr hr1 hτ θ
      (fun t => η^2/2 ≤ lowerChord b t) _ i j
    intro t ht
    have hc : lowerChord b t ≤ η^2 := by linarith [lt_of_not_ge ht,sq_nonneg η]
    rw [(constructed_lower_core_plateau hbs hη hηsmall hα hc).1]
    norm_num
  obtain ⟨hpair,hpairbound⟩ := selected_discounted_pair_integral hb hbT hbs
    hC.le heps hL hτ hr hr1 hD hKL (η := η)
  change IntegrableOn (fun p : ℝ × ℝ => w p.1*w p.2*k p.1 p.2)
    (Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi)) at hpair
  change (∫ p in Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi),
    w p.1*w p.2*k p.1 p.2) ≤
      selectedYPairConstant b τ*W^2+C^2*(2*Real.pi)*D at hpairbound
  have hpure : IntegrableOn (fun p : ℝ × ℝ => w p.1*w p.2)
      (Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi)) := by
    rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict]
    exact hwi.mul_prod hwi
  have hplus : IntegrableOn (fun p : ℝ × ℝ => w p.1*w p.2*(k p.1 p.2+1))
      (Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi)) := by
    convert hpair.add hpure using 1
    funext p
    simp only [Pi.add_apply]
    ring
  have hV : (∫ p in Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi),
      w p.1*w p.2*(k p.1 p.2+1)) ≤ V := by
    have he : (fun p : ℝ × ℝ => w p.1*w p.2*(k p.1 p.2+1)) =
        fun p => w p.1*w p.2*k p.1 p.2+w p.1*w p.2 := by funext p; ring
    have hpureIntegral : (∫ p in Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi),
        w p.1*w p.2) = (∫ t in Icc 0 (2*Real.pi),w t)^2 := by
      rw [Measure.volume_eq_prod,setIntegral_prod_mul,pow_two]
    rw [he,integral_add hpair hpure,hpureIntegral]
    have hw : 0 ≤ ∫ t in Icc 0 (2*Real.pi),w t := integral_nonneg hw0
    have hw2 := pow_le_pow_left₀ hw hwA 2
    dsimp [V,W]
    nlinarith [hpairbound, hw2]
  have hY : Continuous Y := deformedPoint_continuous (N := 2*n+1) f r τ 1
    (periodicUpperP_smooth α).continuous (periodicLowerM_smooth b η).continuous
  have hPc : Continuous (fun θ : Fin (2*n+1) → ℝ => First.pairProduct (Y θ)) := by
    unfold First.pairProduct
    apply continuous_finsetProd
    intro i _
    apply continuous_finsetProd
    intro j _
    exact (((continuous_apply i).comp hY).sub ((continuous_apply j).comp hY)).div
      (continuous_const.sub (((continuous_apply i).comp hY).mul ((continuous_apply j).comp hY)))
      (fun θ => hd θ i j)
  have hinit : Continuous (Fin.init : (Fin (2*n+1+1) → ℝ) → Fin (2*n+1) → ℝ) := by
    apply continuous_pi
    intro i
    exact continuous_apply i.castSucc
  have hmprod : Measurable (fun θ : Fin (2*n+1+1) → ℝ => ∏ i,w (θ i)) := by
    apply Finset.measurable_fun_prod
    intro i _
    exact (discountedSelectedWeight_measurable b η C eps L).comp (measurable_pi_apply i)
  have hmeas : AEStronglyMeasurable (fun θ : Fin (2*n+1+1) → ℝ =>
      (∏ i,w (θ i))*‖First.pairProduct (Y (Fin.init θ))‖) (Measure.pi (fun _ => μ)) :=
    (hmprod.mul (hPc.comp hinit).norm.measurable).aestronglyMeasurable
  have hmass := discountedSelectedWeight_mass_pos hb hbT hC heps heps1 hL (η := η)
  obtain ⟨hi,hm⟩ := coupled_odd_pairProduct_integrable_and_le n μ w hw0 Y k
    (selectedMaskedKernel_nonneg hbs hτ η r) hd hg hA
    (selected_pair_pi_integrable (2*Real.pi)
      (fun x y => w x*w y*(k x y+1)) hplus) hmeas hmass
  refine ⟨hi,hm.trans ?_⟩
  rw [pair_pi_integral_eq_prod (2*Real.pi) (fun x y => w x*w y*(k x y+1))]
  have hp0 : 0 ≤ ∫ p in Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi),
      w p.1*w p.2*(k p.1 p.2+1) := by
    apply integral_nonneg
    intro p
    exact mul_nonneg (mul_nonneg (hw0 p.1) (hw0 p.2))
      (by linarith [selectedMaskedKernel_nonneg hbs hτ η r p.1 p.2])
  have hWlow := discountedSelectedWeight_mass_lower hb hbT hC.le heps heps1 hL (η := η)
  have hM : 0 ≤ (matchingCount (n+1):ℝ)*V^(n+1) := by
    apply mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hp0.trans hV) _)
  calc
    _ ≤ ((matchingCount (n+1):ℝ)*V^(n+1)) /
        ((2*Real.pi)*C/(L*(2*Real.pi+1))) := by
      apply div_le_div₀ hM
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hV _) (Nat.cast_nonneg _)
      · positivity
      · exact hWlow
    _ = _ := by dsimp only [V,W]; field_simp

end
end IsingBulk.HT.Contour
