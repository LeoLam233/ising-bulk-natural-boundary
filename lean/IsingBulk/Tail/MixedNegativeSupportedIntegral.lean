import IsingBulk.Tail.MixedNegativeSourceKernel
import IsingBulk.Tail.MixedNegativePhaseIntegral
import IsingBulk.Tail.MixedPositiveSupportedIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter MeasureTheory Function
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def mixedNegativeAngularHalf {N : ℕ} (b : ℝ) (j : Fin N) : Set (Fin N → ℝ) :=
  angleBox N ∩ {θ | θ j+b-2*Real.pi≤0}

theorem mixedNegativeAngularHalf_measurable {N : ℕ} (b : ℝ) (j : Fin N) :
    MeasurableSet (mixedNegativeAngularHalf b j) := by
  exact measurableSet_Icc.inter (isClosed_le
    (((continuous_apply j).add continuous_const).sub continuous_const) continuous_const).measurableSet

def mixedNegativeIntegralBudget (N : ℕ) (a eps C : ℝ) : ℝ :=
  ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
    (2*Real.log ((2*Real.pi+eps)/eps))*C^(N-2)

/-- The source branch support itself supplies the negative-half kernel
and volume geometry. Both original and current supports are accepted;
lambda zero is independent of the auxiliary deformation size. -/
theorem mixed_negative_supported_integral (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (η α : ℝ)
    (hη : 0<η) (hηsmall : η≤Real.sin d.thetaB/4) (hα : 0<α) (hαsmall : α<Real.sin d.thetaB/4) :
    ∃ inner₀ e t₀ C B : ℝ,0< inner₀ ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧ 0<B ∧
      ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (N : ℕ) (J : Finset (Fin N)) (j q : Fin N) (eps τ lam D : ℝ)
        (F : (Fin N → ℝ) → ℂ) (K : Set (Fin N → ℝ)),
      j∈J → q∉J → 0<eps → eps<e → 0≤τ → (lam=0 ∨ τ<t₀) → 0≤lam → lam≤1 → 0≤D →
      IntegrableOn F (angleBox N) → support F⊆K →
      (∀ θ∈angleBox N,θ∈K →
        (θ∈tsupport (angularSelector (constructedSelector d.thetaB η α)) ∨
          θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q))) →
      (∀ θ∈angleBox N,θ∈K → ∀ i∈J,θ i∈tsupport (sectorBranch d.thetaB inner hi)) →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      (∀ θ∈angleBox N,θ∈K → ‖F θ‖≤D*(‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖)) →
      (∫ θ in mixedNegativeAngularHalf d.thetaB j,‖F θ‖)≤
        D*(C*mixedNegativeIntegralBudget N (d.c₀*eps) eps
          (2*Real.pi+4*B*Real.sqrt (2*Real.pi))) := by
  classical
  obtain ⟨B,eV,tV,hB,heV,htV,hVolume⟩ := mixed_actual_source_volume_majorant d
  obtain ⟨iV,hiV,hVolume⟩ := hVolume η α hη hηsmall hα hαsmall
  obtain ⟨C,R,eK,tK,hC,hR,heK,htK,hKernel⟩ := mixed_negative_source_kernel_bound d hcsmall
  obtain ⟨iW,hiW,hWidth⟩ := sector_branch_support_lower_chart d.thetaB_pos d.thetaB_lt
    (lt_min hR (half_pos hη))
  let e := min eV (min eK (1/(d.c₀+1)))
  have he : 0<e := by dsimp [e]; positivity [d.c₀_pos]
  refine ⟨min iV iW,e,min tV tK,C,B,lt_min hiV hiW,he,lt_min htV htK,hC,hB,?_⟩
  intro inner hi hinner N J j q eps τ lam D F K hj hq heps heSmall hτ hτSmall hl0 hl1 hD hF hSupp hSource hBranch
  dsimp only
  intro hPoint
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let L := mixedNegativePhaseMajorant d.thetaB B eps (d.c₀*eps) j q
  have hN : 0<N := by have := j.isLt; omega
  have hjq : j≠q := by intro heq; exact hq (heq ▸ hj)
  have hf := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have heV' := heSmall.trans_le (min_le_left _ _)
  have heK' := heSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ha1 : d.c₀*eps≤1 := by
    have hh := heSmall.le.trans ((min_le_right eV _).trans (min_le_right eK _))
    have hh' := (le_div_iff₀ (show 0<d.c₀+1 by linarith [d.c₀_pos])).mp hh
    nlinarith
  have hInt := mixed_negative_phase_integral j q hjq d.thetaB_pos.le
    (show d.thetaB≤2*Real.pi by linarith [d.thetaB_lt,Real.pi_pos]) hB.le heps (mul_pos d.c₀_pos heps) ha1
  have hL0 (θ : Fin N → ℝ) : 0≤L θ := by
    apply mul_nonneg
    · exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (by positivity))
    · exact Finset.prod_nonneg (fun i _ => zero_le_one.trans (mixedSpectatorMajorant_one_le d.thetaB hB.le (θ i)))
  have hpoint (θ : Fin N → ℝ) (hθ : θ∈mixedNegativeAngularHalf d.thetaB j) (hK : θ∈K) :
      ‖F θ‖≤(D*C)*L θ := by
    have hSource' := hSource θ hθ.1 hK
    have hBranch' := hBranch θ hθ.1 hK
    have hsin : Real.sin (θ j)≤3*α/2 := by
      rcases hSource' with hO | hC
      · exact constructed_original_support_sine_upper d.thetaB η α hα j hO
      · exact constructed_current_support_sine_upper d.thetaB η α hα q j hC
    have hu := hWidth inner hi (hinner.trans (min_le_right _ _)) (θ j) (hθ.1.1 j) (hθ.1.2 j)
      (show Real.sin (θ j)≤Real.sin d.thetaB/2 by linarith [d.a_pos]) (hBranch' j hj)
    obtain ⟨hp,hm⟩ := mixed_lower_angular_plateau d.a_pos hη hηsmall hα
      (half_pos hη).le le_rfl (hu.le.trans (min_le_right _ _))
    have hV : ‖mixedHybridVolume J f r τ lam s θ‖≤
        ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
          ∏ i∈(Finset.univ.erase j).erase q,mixedSpectatorMajorant d.thetaB B eps (θ i) := by
      rcases hτSmall with hzero | ht
      · subst lam
        have hh := hVolume inner hi (hinner.trans (min_le_left _ _)) N eps 0 0 θ J j q hN heps heV'
          le_rfl htV le_rfl zero_le_one hθ.1 hj hq hSource' hBranch'
        simpa only [mixedHybridVolume,deformedPoint_zero] using hh
      · exact hVolume inner hi (hinner.trans (min_le_left _ _)) N eps τ lam θ J j q hN heps heV'
          hτ (ht.trans_le (min_le_left _ _)) hl0 hl1 hθ.1 hj hq hSource' hBranch'
    have hKn : ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*‖mixedSimpleKernel f r τ lam s θ‖≤
        C*((phaseDenominator (Real.exp (-(d.c₀*eps))) (∑ i,θ i))⁻¹*(|θ j+d.thetaB-2*Real.pi|+eps)⁻¹) := by
      rcases hτSmall with hzero | ht
      · subst lam
        have hh := hKernel N eps 0 0 f θ j (by omega) heps heK' le_rfl htK le_rfl zero_le_one hf
          (fun _ => (thresholdStep_range _ _ _).2) (fun _ => Real.smoothTransition.le_one _)
          hp.eq_of_nhds hm.eq_of_nhds hθ.2 (hu.trans_le (min_le_left _ _))
        simpa only [mixedSimpleKernel,deformedPoint_zero] using hh
      · exact hKernel N eps τ lam f θ j (by omega) heps heK' hτ (ht.trans_le (min_le_right _ _)) hl0 hl1 hf
          (fun _ => (thresholdStep_range _ _ _).2) (fun _ => Real.smoothTransition.le_one _)
          hp.eq_of_nhds hm.eq_of_nhds hθ.2 (hu.trans_le (min_le_left _ _))
    let P := ∏ i∈(Finset.univ.erase j).erase q,mixedSpectatorMajorant d.thetaB B eps (θ i)
    have hP : 0≤P := Finset.prod_nonneg (fun i _ => zero_le_one.trans (mixedSpectatorMajorant_one_le d.thetaB hB.le (θ i)))
    have hv := mul_le_mul_of_nonneg_left hV (norm_nonneg (mixedSimpleKernel f r τ lam s θ))
    have hk := mul_le_mul_of_nonneg_right hKn hP
    have hfull : ‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖≤C*L θ := by
      calc
        _ ≤ (‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*‖mixedSimpleKernel f r τ lam s θ‖)*P :=
          hv.trans_eq (by dsimp [P]; ring)
        _ ≤ _ := hk.trans_eq (by
          have heq : (Finset.univ.erase j).erase q=(Finset.univ.erase q).erase j := by ext i; simp [and_comm]
          dsimp [P,L,mixedNegativePhaseMajorant]
          rw [heq]
          ring)
    exact (hPoint θ hθ.1 hK).trans ((mul_le_mul_of_nonneg_left hfull hD).trans_eq (by ring))
  have hh := finite_cover_integral_norm_le volume ({()} : Finset Unit) (mixedNegativeAngularHalf d.thetaB j)
    K (fun _ => angleBox N) F L (mixedNegativeAngularHalf_measurable _ _) (hF.mono_set (fun _ hθ => hθ.1))
    (mul_nonneg hD hC.le) hL0 (fun _ _ => measurableSet_Icc) (fun _ _ => hInt.1) (fun _ _ => hInt.2)
    hSupp (fun _ hθ _ => ⟨(),by simp,hθ.1⟩) hpoint
  simpa only [Finset.card_singleton,Nat.cast_one,one_mul,mixedNegativeIntegralBudget,mul_assoc] using hh

end
end IsingBulk.Tail
