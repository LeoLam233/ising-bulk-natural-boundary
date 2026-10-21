import IsingBulk.HT.Lie.SignedTransport
import IsingBulk.HT.Lie.SignedCoarea
import IsingBulk.Tail.AllBranchExteriorKernelFloor
import IsingBulk.Tail.AllBranchExteriorPositiveJacobian
import IsingBulk.Tail.AllBranchExteriorOriginalKernel

/-!
HT signed kernels on the actual angular branch. The phase translation is
performed after differentiating the source. The positive-region coarea
statement below uses the LT proof of the actual Jacobian and injectivity;
neither is an input hypothesis. The two phase shifts have opposite signs
because regularZProduct has phase minus the sum of the angular phases.
-/
namespace IsingBulk.HT.Lie
noncomputable section
open Set MeasureTheory IsingBulk.Tail IsingBulk.Jets IsingBulk.Branch IsingBulk.First
open scoped BigOperators

/-- Both signed product gaps follow from the actual inward moduli. -/
theorem signedRegularKernel_ne_of_norm_lt_one {N : ℕ} (σ s : ℂ)
    (φ : Fin N → ℂ) (hσ : ‖σ‖ = 1)
    (hY : ‖regularYProduct s φ‖ < 1) (hZ : ‖regularZProduct s φ‖ < 1) :
    signedRegularKernel σ s φ ≠ 0 := by
  have hgap (z : ℂ) (hz : ‖z‖ < 1) : 1-σ*z ≠ 0 := by
    intro h
    have hh := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one,norm_mul,hσ,one_mul] at hh
    linarith
  exact mul_ne_zero (hgap _ hY) (hgap _ hZ)

/-- The actual chart has both signed product gaps whenever its Z damping
floor is positive; the Y gap comes from the original radius itself. -/
theorem signed_regular_kernel_ne {n : ℕ} (v θ : ℝ) (s : ℂ)
    (u : Fin (n+1) → ℝ) (σ : ℂ) (hσ : ‖σ‖ = 1) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (u i:ℂ)).re)
    {a : ℝ} (ha : 0 < a)
    (hz : ‖regularZProduct s (chartMap v θ s u)‖ ≤ Real.exp (-a)) :
    signedRegularKernel σ s (chartMap v θ s u) ≠ 0 := by
  apply signedRegularKernel_ne_of_norm_lt_one σ s _ hσ
  · rw [allBranchExterior_regularY_exponent v θ s u hg,Complex.norm_exp]
    apply Real.exp_lt_one_iff.mpr
    simp only [allBranchExteriorYExponent,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,
      zero_mul,mul_zero,sub_zero,add_zero]
    exact mul_neg_of_pos_of_neg (by positivity) hv
  · exact hz.trans_lt (Real.exp_lt_one_iff.mpr (by linarith))

/-- Multiplying an exponential by a unit phase changes only its phase,
so the radial floor and its explicit factor two are unchanged. -/
theorem signed_exp_kernel_floor (z : ℂ) (α : ℝ) {a : ℝ}
    (ha : 0 < a) (hz : ‖Complex.exp z‖ ≤ Real.exp (-a)) :
    ‖1 - Complex.exp (Complex.I*(α:ℂ))*Complex.exp z‖⁻¹ ≤
      2*shiftedPhaseKernel a α z.im := by
  have hn : ‖Complex.exp (z+Complex.I*(α:ℂ))‖ ≤ Real.exp (-a) := by
    simpa only [Complex.norm_exp,Complex.add_re,Complex.mul_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,mul_zero,sub_zero,add_zero] using hz
  have hh := allBranchExterior_exp_kernel_floor (z+Complex.I*(α:ℂ)) ha hn
  have he : Complex.exp (z+Complex.I*(α:ℂ)) =
      Complex.exp (Complex.I*(α:ℂ))*Complex.exp z := by
    rw [Complex.exp_add]
    ring
  simpa only [he,Complex.add_im,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,
    zero_add,shiftedPhaseKernel] using hh

/-- Actual chart kernel floor, including the signed HT denominator.
The Y phase is translated by α and the positive Z phase by minus α. -/
theorem signed_regular_kernel_floor {n : ℕ} (v θ : ℝ) (s : ℂ)
    (u : Fin (n+1) → ℝ) (α : ℝ) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (u i:ℂ)).re)
    {a : ℝ} (ha : 0 < a)
    (hz : ‖regularZProduct s (chartMap v θ s u)‖ ≤ Real.exp (-a)) :
    ‖signedRegularKernel (Complex.exp (Complex.I*(α:ℂ))) s
      (chartMap v θ s u)‖⁻¹ ≤
      4*shiftedTwoPhaseKernel (-v) a α (-α)
        ((∑ i, u i)-(n+1:ℝ)*θ, ∑ i, (chartMap v θ s u i).re) := by
  have hY : ‖Complex.exp (allBranchExteriorYExponent v θ u)‖ ≤ Real.exp v := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [allBranchExteriorYExponent,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,
      zero_mul,mul_zero,sub_zero,add_zero]
    push_cast
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hy := signed_exp_kernel_floor (allBranchExteriorYExponent v θ u) α
    (show 0 < -v by linarith) (by simpa using hY)
  have hz' := signed_exp_kernel_floor
    (-Complex.I*∑ i, chartMap v θ s u i) α ha hz
  have hiZ : (-Complex.I*∑ i, chartMap v θ s u i).im =
      -(∑ i, (chartMap v θ s u i).re) := by simp [Complex.mul_im]
  have hiY : (allBranchExteriorYExponent v θ u).im =
      (∑ i, u i)-(n+1:ℝ)*θ := by simp [allBranchExteriorYExponent]
  have hphase : -(∑ i, (chartMap v θ s u i).re)+α =
      -((∑ i, (chartMap v θ s u i).re)+ -α) := by ring
  unfold shiftedPhaseKernel at hz'
  rw [hiZ,hphase,phaseDenominator_neg] at hz'
  rw [hiY] at hy
  have hh := mul_le_mul hz' hy (inv_nonneg.mpr (norm_nonneg _)) (by
    unfold phaseDenominator
    positivity)
  rw [signedRegularKernel,norm_mul,mul_inv_rev,
    allBranchExterior_regularY_exponent v θ s u hg]
  change ‖1-Complex.exp (Complex.I*(α:ℂ))*
      Complex.exp (-Complex.I*∑ i, chartMap v θ s u i)‖⁻¹ *
    ‖1-Complex.exp (Complex.I*(α:ℂ))*
      Complex.exp (allBranchExteriorYExponent v θ u)‖⁻¹ ≤ _
  apply hh.trans_eq
  unfold shiftedTwoPhaseKernel shiftedPhaseKernel
  dsimp only
  ring

/-- The reflected HT sector has the same damping floors. The negative
sign is represented explicitly by the two opposite π shifts. -/
theorem negative_regular_kernel_floor {n : ℕ} (v θ : ℝ) (s : ℂ)
    (u : Fin (n+1) → ℝ) (hv : v < 0)
    (hg : ∀ i, 0 < (angularG v θ (u i:ℂ)).re)
    {a : ℝ} (ha : 0 < a)
    (hz : ‖regularZProduct s (chartMap v θ s u)‖ ≤ Real.exp (-a)) :
    ‖signedRegularKernel (-1) s (chartMap v θ s u)‖⁻¹ ≤
      4*shiftedTwoPhaseKernel (-v) a Real.pi (-Real.pi)
        ((∑ i, u i)-(n+1:ℝ)*θ, ∑ i, (chartMap v θ s u i).re) := by
  have h := signed_regular_kernel_floor v θ s u Real.pi hv hg ha hz
  rw [mul_comm Complex.I (Real.pi:ℂ),Complex.exp_pi_mul_I] at h
  exact h

/-- The actual radial original-circle chart supplies the damping floors.
The constants are chosen before the unit phase and before particle number;
no signed kernel estimate or product-modulus hypothesis is assumed. -/
theorem signed_original_kernel_gap_and_floor (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ a r : ℝ, 0 < a ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ α : ℝ, ∀ n : ℕ, ∀ u : Fin (n+1) → ℝ, (∀ i, |u i| ≤ r) →
      signedRegularKernel (Complex.exp (Complex.I*(α:ℂ))) (radialParameter d.theta ε)
        (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) ≠ 0 ∧
      ‖signedRegularKernel (Complex.exp (Complex.I*(α:ℂ))) (radialParameter d.theta ε)
        (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)‖⁻¹ ≤
      4*shiftedTwoPhaseKernel (d.c₀*ε) (a*ε) α (-α)
        ((∑ i, u i)-(n+1:ℝ)*d.thetaB,∑ i, (originalPhase d ε (u i)).re) := by
  let f : SelectorFunctions := ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩
  have hθ : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨δ,e,a,hδ,_,he,_,ha,hroot⟩ := original_current_root_modulus d.theta d.c₀ 0 hθ d.c₀_pos hcsmall
    le_rfl f (by intro; rfl) (by intro; norm_num [f]) (by intro; rfl)
    (by intro; norm_num [f]) (by intros; rfl) (by intros; rfl)
  obtain ⟨rC,hrC,hchart⟩ := original_microcore_chart d
  let r := min e rC/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r < e := (half_lt_self (lt_min he hrC)).trans_le (min_le_left _ _)
  have hrc : r < rC := (half_lt_self (lt_min he hrC)).trans_le (min_le_right _ _)
  refine ⟨a,r,ha,hr,?_⟩
  intro ε hε hεr α n u hu
  let s := radialParameter d.theta ε
  let v := -d.c₀*ε
  have hp := hchart ε hε (hεr.trans_lt hrc) n u (fun i => (hu i).trans_lt hrc)
  have hz := (hroot (n+1) (by omega) ε 0 hε (hεr.trans_lt hre) le_rfl (by norm_num)
    (fun i => u i-d.thetaB) s (by dsimp [s]; simpa using (mul_nonneg hδ.le hε.le))).2
  have heq : regularZProduct s (chartMap v d.thetaB s u)=
      coordinateProduct (fun i => selectedContinuedRoot s
        (deformedPoint f (Real.exp (-d.c₀*ε)) 0 0 (fun i => u i-d.thetaB) i)) := by
    rw [regularZProduct_eq_prod,coordinateProduct,deformedPoint_zero]
    apply Finset.prod_congr rfl
    intro i _
    change Complex.exp (-Complex.I*chartPhase s v d.thetaB (u i:ℂ))=
      selectedContinuedRoot s (anglePoint (Real.exp v) (u i-d.thetaB))
    rw [anglePoint_eq_angularY]
    unfold selectedContinuedRoot
    change Complex.exp (-Complex.I*chartPhase s v d.thetaB (u i:ℂ))=continuedRoot (chartW s v d.thetaB (u i:ℂ))
    rw [continuedRoot_eq_interiorRoot (hp.im_pos i)]
    exact (chart_root_eq_physical s v d.thetaB (u i:ℂ)).symm
  rw [← heq] at hz
  have hze : ‖regularZProduct s (chartMap v d.thetaB s u)‖ ≤ Real.exp (-(a*ε)) := by
    apply hz.trans
    apply Real.exp_le_exp.mpr
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    push_cast
    have hprod : 0 ≤ a*ε*(n:ℝ) := by positivity
    nlinarith
  have hv : v < 0 := by dsimp [v]; nlinarith [d.c₀_pos]
  have hphase : ‖Complex.exp (Complex.I*(α:ℂ))‖ = 1 := by
    simp [Complex.norm_exp,Complex.mul_re]
  refine ⟨signed_regular_kernel_ne v d.thetaB s u _ hphase hv hp.g_pos
    (mul_pos ha hε) hze, ?_⟩
  have hh := signed_regular_kernel_floor v d.thetaB s u α
    hv hp.g_pos (mul_pos ha hε) hze
  rw [show -v=d.c₀*ε by dsimp [v]; ring] at hh
  simpa only [s,v,original_chartMap_eq] using hh


/-- The actual positive-region branch map with shifted periodic kernels.
All branch derivatives, Jacobian estimates, real image bounds, and
injectivity come from allBranchExterior_positive_coarea. The remaining
n counts periodic wrapping of the image, not map multiplicity. -/
theorem signed_positive_two_kernel {d : LocalBranchData} (B : BranchEstimates d)
    (ε a gap F₀ G₀ α β shiftY shiftZ : ℝ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (ha : 0 < a) (hgap : 0 < gap)
    (hsmall₁ : B.original.separationThreshold*ε ≤ a)
    (hsmall₂ : 2*B.original.C₀*ε ≤ a)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (n : ℕ) (hn : 2*B.r ≤ (n:ℝ)*(2*Real.pi)) :
    IntegrableOn (fun x =>
      ‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖ *
        shiftedTwoPhaseKernel α β shiftY shiftZ
          (allBranchExteriorPositivePhase d ε F₀ G₀ x))
      (allBranchExteriorPositiveRegion B.r a gap) ∧
    (∫ x in allBranchExteriorPositiveRegion B.r a gap,
      ‖deriv (originalPhase d ε) x.1*deriv (originalPhase d ε) x.2‖ *
        shiftedTwoPhaseKernel α β shiftY shiftZ
          (allBranchExteriorPositivePhase d ε F₀ G₀ x)) ≤
      allBranchExteriorPositiveCost B a gap *
        (((n:ℝ)*simpleKernelConstant*(1+|Real.log α|))*
          (simpleKernelConstant*(1+|Real.log β|))) := by
  have hh := allBranchExterior_positive_coarea B ε a gap F₀ G₀
    hε hεr ha hgap hsmall₁ hsmall₂
    (shiftedTwoPhaseKernel α β shiftY shiftZ)
    (shiftedTwoPhaseKernel_continuous hα hβ shiftY shiftZ)
    (shiftedTwoPhaseKernel_nonneg α β shiftY shiftZ)
  have hi := (shifted_two_kernel_rectangle hα hα1 hβ hβ1 shiftY shiftZ n 1
    (show F₀ ≤ F₀+2*B.r by have := B.r_pos; linarith)
    (show G₀ ≤ G₀+Real.pi by linarith [Real.pi_pos])
    (show F₀+2*B.r ≤ F₀+(n:ℝ)*(2*Real.pi) by linarith)
    (by norm_num; linarith [Real.pi_pos])).2
  have hC : 0 ≤ allBranchExteriorPositiveCost B a gap := by
    have := B.original.C_pos
    have := B.original.k_pos
    have := B.original.a_pos
    unfold allBranchExteriorPositiveCost
    positivity
  refine ⟨hh.1, hh.2.trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  simpa only [Nat.cast_one,one_mul,Set.Icc_prod_eq] using hi

end
end IsingBulk.HT.Lie
