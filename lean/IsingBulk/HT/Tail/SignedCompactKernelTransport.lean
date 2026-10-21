import IsingBulk.HT.Tail.SignedCompactSource

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Contour Set Filter
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem signed_compact_kernel_frozen_of_phases (σ : ℂ) (hσ : ‖σ‖ = 1) {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {s : ℂ} (hs : s ∈ dampingDomain r) (θ : AngularSpace n)
    (hfreeze : transport V (fun _ x => unwrappedLogY f r τ lam x) s θ=0 ∧
      transport V (currentComplexPhase f r τ lam) s θ=0) :
    transport V (signedMixedSimpleKernel σ f r τ lam) s θ=0 := by
  let Y := fun (_ : ℂ) (x : AngularSpace n) => coordinateProduct (deformedPoint f r τ lam x)
  let Z := fun (z : ℂ) (x : AngularSpace n) =>
    coordinateProduct (fun i => globalRoot z (deformedPoint f r τ lam x i))
  have hp : (s,θ) ∈ compactSourceDomain (n+1) r := ⟨hs,mem_univ _⟩
  have hY := compactSource_Y_smooth (N := n+1) f hf r τ lam
  have hZ := compactSource_Z_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam
  have hPhase := compactSource_phase_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam
  have hLog := compactSource_logY_smooth (N := n+1) f hf r τ lam
  have hYfreeze : transport V Y s θ=0 := by
    have he : Y=(fun (_ : ℂ) (x : AngularSpace n) => Complex.exp (unwrappedLogY f r τ lam x)) := by
      funext t x
      exact (unwrappedLogY_exp f hr τ lam x).symm
    rw [he,transport_cexp V (fun _ x => unwrappedLogY f r τ lam x) s θ
      (hLog _ hp).2 (hLog.angular_differentiableAt hp),hfreeze.1,mul_zero]
  have hZfreeze : transport V Z s θ=0 := by
    have he : Function.uncurry Z =ᶠ[𝓝 (s,θ)]
        Function.uncurry (fun z x => Complex.exp (-Complex.I*currentComplexPhase f r τ lam z x)) := by
      filter_upwards [(compactSourceDomain_isOpen (n+1) r).mem_nhds hp] with p hp'
      change coordinateProduct (fun i => globalRoot p.1 (deformedPoint f r τ lam p.2 i))=
        Complex.exp (-Complex.I*currentComplexPhase f r τ lam p.1 p.2)
      unfold currentComplexPhase
      rw [← product_root_unwrapped_phase (fun i => sourceW p.1 (deformedPoint f r τ lam p.2 i))]
      apply Finset.prod_congr rfl
      intro i _
      exact (continuedRoot_eq_interiorRoot
        (deformed_sourceW_upper_on_damping (Nat.succ_pos n) f hf hr hr1 hτ hlam hp'.1 p.2 i)).symm
    rw [transport_congr_joint_germ V s θ he,transport_cexp V
      (fun z x => -Complex.I*currentComplexPhase f r τ lam z x) s θ
      ((hPhase _ hp).2.const_mul _) ((hPhase.angular_differentiableAt hp).const_mul _),
      transport_const_mul V (currentComplexPhase f r τ lam) (-Complex.I) s θ
        (hPhase.angular_differentiableAt hp),hfreeze.2,mul_zero,mul_zero]
  have hZσ : transport V (fun t x => σ*Z t x) s θ = 0 := by
    rw [IsingBulk.Tail.transport_const_mul V Z σ s θ (hZ.angular_differentiableAt hp),hZfreeze,mul_zero]
  have hYσ : transport V (fun t x => σ*Y t x) s θ = 0 := by
    rw [IsingBulk.Tail.transport_const_mul V Y σ s θ (hY.angular_differentiableAt hp),hYfreeze,mul_zero]
  exact simpleKernel_frozen V (fun t x => σ*Z t x) (fun t x => σ*Y t x) s θ
    ((hZ _ hp).2.const_mul σ) ((hY _ hp).2.const_mul σ)
    ((hZ.angular_differentiableAt hp).const_mul σ) ((hY.angular_differentiableAt hp).const_mul σ)
    (signed_product_gap_ne_zero (Nat.succ_pos n) σ hσ _ (fun i => interiorRoot_norm_lt_one
      (deformed_sourceW_upper_on_damping (Nat.succ_pos n) f hf hr hr1 hτ hlam hs θ i)))
    (signed_gap_ne_zero σ _ hσ (homotopy_y_product_lt_one (Nat.succ_pos n) f hr hr1 hτ hlam θ hf.p_nonneg hf.m_le_one))
    hZσ hYσ

theorem signed_currentSelectedPairField_kernel_frozen (σ : ℂ) (hσ : ‖σ‖ = 1) {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (i j : Fin (n+1))
    {s : ℂ} (hs : s ∈ dampingDomain r) (θ : AngularSpace n)
    (hD : currentAngularDeterminant f r τ lam s i j θ ≠ 0) :
    transport (currentSelectedPairField f r τ lam i j) (signedMixedSimpleKernel σ f r τ lam) s θ=0 := by
  have hh := cancelledAngularPair_functionals (currentAngularLogYCoefficient f r τ lam θ)
    (currentAngularPhaseCoefficient f r τ lam s θ) (currentPhaseParameterDerivative f r τ lam s θ)
    (currentAngularDeterminant f r τ lam s i j θ) i j (d := 1) hD (by
      simp only [Complex.ofReal_one,one_mul,currentAngularDeterminant,angularPairDeterminant,
        currentAngularLogYCoefficient,currentAngularPhaseCoefficient])
  have hy : (∑ k,currentSelectedPairField f r τ lam i j s θ k*
      fderiv ℝ (unwrappedLogY f r τ lam) θ (Pi.single k 1))=0 := by
    simpa only [complexCoordinateFunctional,LinearMap.coe_mk,AddHom.coe_mk,
      currentAngularLogYCoefficient,currentSelectedPairField,mul_comm] using hh.1
  have hz : (∑ k,currentSelectedPairField f r τ lam i j s θ k*
      fderiv ℝ (currentComplexPhase f r τ lam s) θ (Pi.single k 1))=
        deriv (fun z => currentComplexPhase f r τ lam z θ) s := by
    simpa only [complexCoordinateFunctional,LinearMap.coe_mk,AddHom.coe_mk,one_smul,
      currentAngularPhaseCoefficient,currentPhaseParameterDerivative,currentSelectedPairField,mul_comm] using hh.2
  apply signed_compact_kernel_frozen_of_phases σ hσ _ f hf hr hr1 hτ hlam hs θ
  constructor
  · simp only [transport,deriv_const,hy,sub_self]
  · simp only [transport,hz,sub_self]

end
end IsingBulk.HT.Tail
