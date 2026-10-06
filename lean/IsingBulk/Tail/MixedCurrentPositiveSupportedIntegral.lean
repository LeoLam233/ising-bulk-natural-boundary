import IsingBulk.Tail.MixedPositiveSupportedIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter MeasureTheory Function
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Actual named-current support attachment for positive integration.
The auxiliary nested-partition anchor is retained independently of the
current's compact anchor, and constants are uniform in lambda. -/
theorem mixed_current_positive_supported_integral (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (η α : ℝ)
    (hη : 0<η) (hηsmall : η≤Real.sin d.thetaB/4) (hα : 0<α) (hαsmall : α<Real.sin d.thetaB/4) :
    ∃ (inner₀ t₀ B : ℝ) (M : ℕ),0< inner₀ ∧ 0<t₀ ∧ 0<B ∧
      ∀ τ : ℝ,0≤τ → τ<t₀ → ∃ a e : ℝ,0<a ∧ 0<e ∧
      ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ → ∀ (outer : ℝ) (ho : 0<outer),
      ∀ (N : ℕ) (j q qA : Fin N) (sigma : Fin N → Fin 3) (eps lam D : ℝ) (F : (Fin N → ℝ) → ℂ),
      sigma j=2 → sigma q≠2 → 0<eps → eps<e → 0≤lam → lam≤1 → 0≤D →
      IntegrableOn F (angleBox N) →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      let K := tsupport (fun θ => namedSelectorDerivative f q θ*nestedSectorWeight d.thetaB outer inner ho hi qA sigma θ)
      support F⊆K →
      (∀ θ∈angleBox N,θ∈K → ‖F θ‖≤D*(‖mixedSimpleKernel f r τ lam s θ‖*
        ‖mixedHybridVolume (mixedBranchIndexSet sigma) f r τ lam s θ‖)) →
      (∫ θ in mixedPositiveAngularHalf d.thetaB j,‖F θ‖)≤
        D*((M:ℝ)*mixedPositiveIntegralBudget N (d.c₀*eps) (a*eps)
          (2*Real.pi+4*B*Real.sqrt (2*Real.pi))) := by
  obtain ⟨B,eV,tV,hB,heV,htV,hVolume⟩ := mixed_actual_source_volume_majorant d
  obtain ⟨iV,hiV,hVolume⟩ := hVolume η α hη hηsmall hα hαsmall
  obtain ⟨R,tP,T,hR,htP,hCover,hIntegral⟩ := mixed_current_positive_kernel_cover d hcsmall
    η α B hη hηsmall hα hαsmall hB.le
  obtain ⟨iW,hiW,hWidth⟩ := current_sector_branch_lower_chart d.thetaB_pos d.thetaB_lt hR
  refine ⟨min iV iW,min tV tP,B,T.card,lt_min hiV hiW,lt_min htV htP,hB,?_⟩
  intro τ hτ hτSmall
  obtain ⟨a,eP,ha,heP,hIntegral⟩ := hIntegral τ hτ (hτSmall.trans_le (min_le_right _ _))
  refine ⟨a,min eV eP,ha,lt_min heV heP,?_⟩
  intro inner hi hinner outer ho N j q qA sigma eps lam D F hσj hσq he heSmall hl0 hl1 hD hF
  dsimp only
  intro hSupp hPoint
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let J := mixedBranchIndexSet sigma
  let K := tsupport (fun θ => namedSelectorDerivative f q θ*nestedSectorWeight d.thetaB outer inner ho hi qA sigma θ)
  let cell := fun I => mixedAngularCell j q (2*Real.pi-d.thetaB,2*Real.pi-d.thetaB+R) I
  let L := mixedPositiveKernelMajorant d η α B eps τ lam j q
  have hj : j∈J := by simp [J,mixedBranchIndexSet,hσj]
  have hq : q∉J := by simpa [J,mixedBranchIndexSet] using hσq
  have hjq : j≠q := by intro heq; exact hq (heq ▸ hj)
  have hCells (I : ℝ×ℝ) (hI : I∈T) := hIntegral N j q hjq I hI eps lam he
    (heSmall.trans_le (min_le_right _ _)) hl0 hl1
  have hL0 (θ : Fin N → ℝ) : 0≤L θ := by
    apply mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    exact Finset.prod_nonneg (fun i _ => zero_le_one.trans (mixedSpectatorMajorant_one_le d.thetaB hB.le (θ i)))
  have hV (θ : Fin N → ℝ) (hθ : θ∈angleBox N) (hK : θ∈K) :
      ‖mixedHybridVolume J f r τ lam s θ‖≤
        ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
          ∏ i∈(Finset.univ.erase j).erase q,mixedSpectatorMajorant d.thetaB B eps (θ i) := by
    exact hVolume inner hi (hinner.trans (min_le_left _ _)) N eps τ lam θ J j q
      (by have := j.isLt; omega) he (heSmall.trans_le (min_le_left _ _)) hτ
      (hτSmall.trans_le (min_le_left _ _)) hl0 hl1 hθ hj hq (Or.inr (tsupport_mul_subset_left hK))
      (nested_sector_branch_support d.thetaB outer inner ho hi qA sigma (tsupport_mul_subset_right hK))
  apply finite_cover_integral_norm_le volume T (mixedPositiveAngularHalf d.thetaB j) K cell F L
    (mixedPositiveAngularHalf_measurable _ _) (hF.mono_set (fun _ hθ => hθ.1)) hD hL0
    (fun I _ => mixedAngularCell_measurable _ _ _ _) (fun I hI => (hCells I hI).1)
    (fun I hI => (hCells I hI).2) hSupp
  · intro θ hθ hK
    have hSource := tsupport_mul_subset_left hK
    obtain ⟨_,_,hlo,hhi,_⟩ := constructed_current_support_geometry d.thetaB η α d.a_pos
      hη hηsmall hα q hSource
    obtain ⟨I,hI,hθq⟩ := hCover (θ q) ⟨hθ.1.1 q,hθ.1.2 q⟩ hlo (hhi q)
    have hu := hWidth inner hi (hinner.trans (min_le_right _ _)) N η α hα hαsmall θ hθ.1 q hSource
      j (nested_sector_branch_support d.thetaB outer inner ho hi qA sigma (tsupport_mul_subset_right hK) j hj)
    refine ⟨I,hI,⟨⟨hθ.1,?_,?_⟩,hθq⟩⟩
    · have hu0 := hθ.2; dsimp at hu0 ⊢; linarith
    · dsimp
      linarith [(abs_lt.mp hu).2]
  · intro θ hθ hK
    have hh := hPoint θ hθ.1 hK
    apply hh.trans
    have hv := mul_le_mul_of_nonneg_left (hV θ hθ.1 hK) (norm_nonneg (mixedSimpleKernel f r τ lam s θ))
    have hv' := mul_le_mul_of_nonneg_left hv hD
    exact hv'.trans_eq (by dsimp [L,mixedPositiveKernelMajorant,f,r,s]; ring)

end
end IsingBulk.Tail
