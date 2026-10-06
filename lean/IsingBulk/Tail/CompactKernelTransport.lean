import IsingBulk.Tail.CompactSourceSmooth

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Lie Set Filter
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem transport_congr_joint_germ {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    {A B : ℂ → AngularSpace n → ℂ} (s : ℂ) (x : AngularSpace n)
    (h : Function.uncurry A =ᶠ[𝓝 (s,x)] Function.uncurry B) :
    transport V A s x=transport V B s x := by
  have hp : (fun t => A t x) =ᶠ[𝓝 s] (fun t => B t x) :=
    h.comp_tendsto (continuousAt_id.prodMk continuousAt_const).tendsto
  have hx : A s =ᶠ[𝓝 x] B s :=
    h.comp_tendsto (continuousAt_const.prodMk continuousAt_id).tendsto
  simp only [transport,hp.deriv_eq,hx.fderiv_eq]

theorem transport_cexp {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (s : ℂ) (x : AngularSpace n)
    (hs : DifferentiableAt ℂ (fun t => A t x) s) (hx : DifferentiableAt ℝ (A s) x) :
    transport V (fun t y => Complex.exp (A t y)) s x=
      Complex.exp (A s x)*transport V A s x := by
  simp only [transport,hs.hasDerivAt.cexp.deriv,hx.hasFDerivAt.cexp.fderiv,smul_apply,smul_eq_mul]
  rw [show (∑ i, V s x i*(Complex.exp (A s x)*fderiv ℝ (A s) x (Pi.single i 1)))=
    Complex.exp (A s x)*(∑ i,V s x i*fderiv ℝ (A s) x (Pi.single i 1)) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  ring

theorem transport_const_mul {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (c s : ℂ) (x : AngularSpace n) (hx : DifferentiableAt ℝ (A s) x) :
    transport V (fun t y => c*A t y) s x=c*transport V A s x := by
  simp only [transport,deriv_const_mul_field,(hx.hasFDerivAt.const_mul c).fderiv,smul_apply,smul_eq_mul]
  rw [show (∑ i, V s x i*(c*fderiv ℝ (A s) x (Pi.single i 1)))=
    c*(∑ i,V s x i*fderiv ℝ (A s) x (Pi.single i 1)) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  ring

theorem currentAveragedField_log_phase_transport {n : ℕ}
    (P : Finset (Fin (n+1) × Fin (n+1))) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {s : ℂ} (hs : s ∈ dampingDomain r) (θ : AngularSpace n)
    (hS : pairSquareMass P (fun p => θ p.1-θ p.2) ≠ 0)
    (hC : ∀ p ∈ P, currentAngularDividedDifference f r τ lam s p.1 p.2 θ ≠ 0) :
    transport (currentAveragedField P f r τ lam) (fun _ x => unwrappedLogY f r τ lam x) s θ=0 ∧
    transport (currentAveragedField P f r τ lam) (currentComplexPhase f r τ lam) s θ=0 := by
  have hh := currentAveragedField_freezes (Nat.succ_pos n) P f hf hr hr1 hτ hlam hs.2 θ hS hC
  have hy : (∑ i,currentAveragedField P f r τ lam s θ i*
      fderiv ℝ (unwrappedLogY f r τ lam) θ (Pi.single i 1))=0 := by
    simpa only [complexCoordinateFunctional,LinearMap.coe_mk,AddHom.coe_mk,
      currentAngularLogYCoefficient,mul_comm] using hh.1
  have hz : (∑ i,currentAveragedField P f r τ lam s θ i*
      fderiv ℝ (currentComplexPhase f r τ lam s) θ (Pi.single i 1))=
        deriv (fun z => currentComplexPhase f r τ lam z θ) s := by
    simpa only [complexCoordinateFunctional,LinearMap.coe_mk,AddHom.coe_mk,
      currentAngularPhaseCoefficient,currentPhaseParameterDerivative,mul_comm] using hh.2
  constructor
  · simp only [transport,deriv_const,hy,sub_self]
  · simp only [transport,hz,sub_self]

theorem compact_kernel_frozen_of_phases {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {s : ℂ} (hs : s ∈ dampingDomain r) (θ : AngularSpace n)
    (hfreeze : transport V (fun _ x => unwrappedLogY f r τ lam x) s θ=0 ∧
      transport V (currentComplexPhase f r τ lam) s θ=0) :
    transport V (mixedSimpleKernel f r τ lam) s θ=0 := by
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
  exact simpleKernel_frozen V Z Y s θ (hZ _ hp).2 (hY _ hp).2
    (hZ.angular_differentiableAt hp) (hY.angular_differentiableAt hp)
    (one_sub_coordinateProduct_ne_zero (Nat.succ_pos n) (fun i => interiorRoot_norm_lt_one
      (deformed_sourceW_upper_on_damping (Nat.succ_pos n) f hf hr hr1 hτ hlam hs θ i)))
    (homotopy_y_gap_nonzero (Nat.succ_pos n) f hr hr1 hτ hlam θ hf.p_nonneg hf.m_le_one)
    hZfreeze hYfreeze

/-- The cancellation-safe averaged field freezes the literal two source
poles. This applies equally to the full pair set and to the current pair
set with its named coordinate removed. -/
theorem currentAveragedField_kernel_frozen {n : ℕ}
    (P : Finset (Fin (n+1) × Fin (n+1))) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {s : ℂ} (hs : s ∈ dampingDomain r) (θ : AngularSpace n)
    (hS : pairSquareMass P (fun p => θ p.1-θ p.2) ≠ 0)
    (hC : ∀ p ∈ P, currentAngularDividedDifference f r τ lam s p.1 p.2 θ ≠ 0) :
    transport (currentAveragedField P f r τ lam) (mixedSimpleKernel f r τ lam) s θ=0 :=
  compact_kernel_frozen_of_phases _ f hf hr hr1 hτ hlam hs θ
    (currentAveragedField_log_phase_transport P f hf hr hr1 hτ hlam hs θ hS hC)

end
end IsingBulk.Tail
