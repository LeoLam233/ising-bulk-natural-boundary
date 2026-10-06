import IsingBulk.Tail.CompactKernelRadialBudget
import IsingBulk.Tail.CompactNearFarIntegral
import IsingBulk.Tail.CompactActualKernelFloor
import IsingBulk.Tail.LeftCompactSourceJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter MeasureTheory
open scoped Topology BigOperators
set_option maxHeartbeats 1500000

theorem compact_actual_simple_kernel_floor {N : ℕ} (f : SelectorFunctions) {r : ℝ}
    (hr : 0 < r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hW : ∀ i, 0 < (sourceW s (deformedPoint f r τ lam θ i)).im)
    (hY : ‖coordinateProduct (deformedPoint f r τ lam θ)‖ ≤ Real.exp (-a))
    (hZ : ‖coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))‖ ≤ Real.exp (-b)) :
    ‖mixedSimpleKernel f r τ lam s θ‖ ≤
      4*twoPhaseKernel a b ((∑ i, θ i),currentUnwrappedPhase f r τ lam s θ) := by
  let Y := coordinateProduct (deformedPoint f r τ lam θ)
  let Z := coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
  have hyexp : Complex.exp (unwrappedLogY f r τ lam θ)=Y := unwrappedLogY_exp f hr τ lam θ
  have hzexp : Complex.exp (-Complex.I*currentComplexPhase f r τ lam s θ)=Z :=
    (product_root_unwrapped_phase (fun i => sourceW s (deformedPoint f r τ lam θ i))).symm
  have hy := allBranchExterior_exp_kernel_floor (unwrappedLogY f r τ lam θ) ha (by rwa [hyexp])
  have hz := allBranchExterior_exp_kernel_floor (-Complex.I*currentComplexPhase f r τ lam s θ) hb (by rwa [hzexp])
  rw [hyexp,unwrappedLogY_im] at hy
  have hzIm : (-Complex.I*currentComplexPhase f r τ lam s θ).im= -currentUnwrappedPhase f r τ lam s θ := by
    rw [currentUnwrappedPhase_eq_re]
    simp [Complex.mul_im]
  rw [hzexp,hzIm,phaseDenominator_neg] at hz
  have he : mixedSimpleKernel f r τ lam s θ=(1-Z)⁻¹*(1-Y)⁻¹ := by
    unfold mixedSimpleKernel
    congr 3
    unfold Z coordinateProduct
    apply Finset.prod_congr rfl
    intro i _
    exact (continuedRoot_eq_interiorRoot (hW i)).symm
  rw [he,norm_mul,norm_inv,norm_inv]
  have hh := mul_le_mul hz hy (inv_nonneg.mpr (norm_nonneg _)) (by unfold phaseDenominator; positivity)
  exact hh.trans_eq (by unfold twoPhaseKernel; ring)

def compactRadialPhaseKernel {N : ℕ} (d : LocalBranchData) (f : SelectorFunctions)
    (τ lam H a : ℝ) (θ : Fin N → ℝ) : ℝ :=
  twoPhaseKernel (d.c₀*Real.exp (-H)) (a*Real.exp (-H))
    ((∑ i, θ i),currentUnwrappedPhase f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
      (radialParameter d.theta (Real.exp (-H))) θ)

theorem compactRadialPhaseKernel_nonneg {N : ℕ} (d : LocalBranchData) (f : SelectorFunctions)
    (τ lam H a : ℝ) (θ : Fin N → ℝ) : 0 ≤ compactRadialPhaseKernel d f τ lam H a θ :=
  twoPhaseKernel_nonneg _ _ _

/-- Source attachment: the actual coupled roots and Y product prove both
attenuation floors. We deliberately weaken their N-fold attenuation to a
single factor, which already gives the required logarithmic integral cost. -/
theorem actual_compact_right_source_kernel_budget (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {τ δ D β : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hδ : 0 < δ) (hδsmall : δ < 2*(1-Real.cos d.thetaB)) (hD : 0 ≤ D) (hβ : 0 < β) :
    ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ᶠ H : ℝ in atTop,
      ∀ N : ℕ, 0 < N → (N:ℝ) ≤ D*Real.sqrt H →
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      let S := Icc (fun _ : Fin N => -rightSectorRadius d.thetaB δ)
        (fun _ => rightSectorRadius d.thetaB δ)
      let L := compactRadialPhaseKernel (N := N) d f τ lam H a
      IntegrableOn (fun x => allBranchExteriorDiameter x*L x) S ∧
      (∫ x in S, allBranchExteriorDiameter x*L x) ≤ K^N*(N:ℝ)^4*(H+1)^2 ∧
      ∀ θ : Fin N → ℝ,
      ‖mixedSimpleKernel f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
        (radialParameter d.theta (Real.exp (-H))) θ‖ ≤ 4*L θ := by
  have hsin : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨r,e,a,hr,_,he,_,ha,hroot⟩ := original_current_root_modulus d.theta d.c₀ τ
    hsin d.c₀_pos hcsmall hτ f hf.p_nonneg hp1 hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero
  obtain ⟨K,hK,hIntegral⟩ := actual_compact_right_radial_kernel_integral d hcsmall f hf hp1
    hδ hδsmall d.c₀_pos ha hD hβ
  refine ⟨a,K,ha,hK,?_⟩
  have ht : Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall (fun H => Real.exp_pos (-H))⟩
  filter_upwards [hIntegral,ht.eventually (radial_source_eventually_damping d hcsmall),
    eventually_ge_atTop (0:ℝ),Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds he)]
    with H hInt hdom hH heps
  intro N hN hND lam hlam hlamB
  have hlam1 : lam ≤ 1 := hlamB.trans (Real.exp_le_one_iff.mpr (by nlinarith))
  have hh := hInt N hN hND τ lam hτ hτ1 hlam hlamB
  refine ⟨hh.1,hh.2,?_⟩
  intro θ
  have hY := original_current_y_product_bound hN f d.c₀_pos.le (Real.exp_pos (-H)).le hτ hlam θ hf.p_nonneg hf.m_le_one
  have hZ := (hroot N hN (Real.exp (-H)) lam (Real.exp_pos _) heps hlam hlam1 θ
    (radialParameter d.theta (Real.exp (-H)))
    (by simp only [sub_self,norm_zero]; exact mul_nonneg hr.le (Real.exp_pos _).le)).2
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hZe : Real.exp (-a*(N:ℝ)*Real.exp (-H)) ≤ Real.exp (-(a*Real.exp (-H))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hn (mul_nonneg ha.le (Real.exp_pos (-H)).le)]
  exact compact_actual_simple_kernel_floor f hdom.1 τ lam _ θ
    (mul_pos d.c₀_pos (Real.exp_pos _)) (mul_pos ha (Real.exp_pos _))
    (fun i => deformed_sourceW_upper_on_damping hN f hf hdom.1 hdom.2.1 hτ hlam hdom.2.2 θ i)
    (by simpa only [neg_mul] using hY) (hZ.trans hZe)

end
end IsingBulk.Tail
