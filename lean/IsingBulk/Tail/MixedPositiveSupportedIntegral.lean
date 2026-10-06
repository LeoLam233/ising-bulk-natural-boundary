import IsingBulk.Tail.MixedPositiveKernelCover
import IsingBulk.Tail.FiniteCoverIntegral
import IsingBulk.Tail.MixedOriginalPointwise

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter MeasureTheory Function
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def mixedPositiveAngularHalf {N : ℕ} (b : ℝ) (j : Fin N) : Set (Fin N → ℝ) :=
  angleBox N ∩ {θ | 0≤θ j+b-2*Real.pi}

theorem mixedPositiveAngularHalf_measurable {N : ℕ} (b : ℝ) (j : Fin N) :
    MeasurableSet (mixedPositiveAngularHalf b j) := by
  exact measurableSet_Icc.inter (isClosed_le continuous_const
    (((continuous_apply j).add continuous_const).sub continuous_const)).measurableSet

theorem nested_sector_branch_support {N : ℕ} (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner)
    (a : Fin N) (sigma : Fin N → Fin 3) {θ : Fin N → ℝ}
    (hθ : θ∈tsupport (nestedSectorWeight b outer inner ho hi a sigma)) :
    ∀ i∈mixedBranchIndexSet sigma,θ i∈tsupport (sectorBranch b inner hi) := by
  intro i hiJ
  have hσ : sigma i=2 := by simpa [mixedBranchIndexSet] using hiJ
  have hh := sector_assignment_tsupport b inner hi sigma
    (nested_sector_jet_support b outer inner ho hi a sigma [] hθ).2 i
  rw [hσ] at hh
  have heq : sectorLabel b inner hi (2:Fin 3)=sectorBranch b inner hi := by funext x; simp [sectorLabel]
  rwa [heq] at hh

/-- Attach the finite positive cover and branch-volume majorant to the
literal original source support. The scalar pointwise bound is supplied
by the already proved density estimate, independently of this integration. -/
theorem mixed_original_positive_supported_integral (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (η α outer : ℝ) (ho : 0<outer)
    (hη : 0<η) (hηsmall : η≤Real.sin d.thetaB/4) (hα : 0<α) (hαsmall : α<Real.sin d.thetaB/4) :
    ∃ (inner₀ e a B : ℝ) (M : ℕ),0< inner₀ ∧ 0<e ∧ 0<a ∧ 0<B ∧
      ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (N : ℕ) (j q : Fin N) (sigma : Fin N → Fin 3) (eps τ D : ℝ) (F : (Fin N → ℝ) → ℂ),
      sigma j=2 → sigma q≠2 → 0<eps → eps<e → 0≤D →
      IntegrableOn F (angleBox N) →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      let K := tsupport (fun θ => angularSelector f θ*nestedSectorWeight d.thetaB outer inner ho hi q sigma θ)
      support F⊆K →
      (∀ θ∈angleBox N,θ∈K → ‖F θ‖≤D*(‖mixedSimpleKernel f r τ 0 s θ‖*
        ‖mixedHybridVolume (mixedBranchIndexSet sigma) f r τ 0 s θ‖)) →
      (∫ θ in mixedPositiveAngularHalf d.thetaB j,‖F θ‖)≤
        D*((M:ℝ)*mixedPositiveIntegralBudget N (d.c₀*eps) (a*eps)
          (2*Real.pi+4*B*Real.sqrt (2*Real.pi))) := by
  obtain ⟨B,eV,tV,hB,heV,htV,hVolume⟩ := mixed_actual_source_volume_majorant d
  obtain ⟨iV,hiV,hVolume⟩ := hVolume η α hη hηsmall hα hαsmall
  obtain ⟨R,a,eP,T,hR,ha,heP,hCover,hIntegral⟩ := mixed_original_positive_kernel_cover d hcsmall
    η α outer B hη hηsmall hα ho hB.le
  obtain ⟨iW,hiW,hWidth⟩ := original_sector_branch_lower_chart d.thetaB_pos d.thetaB_lt hR
  refine ⟨min iV iW,min eV eP,a,B,T.card,lt_min hiV hiW,lt_min heV heP,ha,hB,?_⟩
  intro inner hi hinner N j q sigma eps τ D F hσj hσq he heSmall hD hF
  dsimp only
  intro hSupp hPoint
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let J := mixedBranchIndexSet sigma
  let K := tsupport (fun θ => angularSelector f θ*nestedSectorWeight d.thetaB outer inner ho hi q sigma θ)
  let cell := fun I => mixedAngularCell j q (2*Real.pi-d.thetaB,2*Real.pi-d.thetaB+R) I
  let L := mixedPositiveKernelMajorant d η α B eps τ 0 j q
  have hj : j∈J := by simp [J,mixedBranchIndexSet,hσj]
  have hq : q∉J := by simpa [J,mixedBranchIndexSet] using hσq
  have hjq : j≠q := by intro heq; exact hq (heq ▸ hj)
  have hCells (I : ℝ×ℝ) (hI : I∈T) := hIntegral N j q hjq I hI eps τ he
    (heSmall.trans_le (min_le_right _ _))
  have hL0 (θ : Fin N → ℝ) : 0≤L θ := by
    apply mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    exact Finset.prod_nonneg (fun i _ => zero_le_one.trans (mixedSpectatorMajorant_one_le d.thetaB hB.le (θ i)))
  have hV (θ : Fin N → ℝ) (hθ : θ∈angleBox N) (hK : θ∈K) :
      ‖mixedHybridVolume J f r τ 0 s θ‖≤
        ‖mixedSourceSlope s (deformedPoint f r τ 0 θ j)‖*
          ∏ i∈(Finset.univ.erase j).erase q,mixedSpectatorMajorant d.thetaB B eps (θ i) := by
    have hh := hVolume inner hi (hinner.trans (min_le_left _ _)) N eps 0 0 θ J j q
      (by have := j.isLt; omega) he (heSmall.trans_le (min_le_left _ _)) le_rfl htV le_rfl zero_le_one
      hθ hj hq (Or.inl (tsupport_mul_subset_left hK))
      (nested_sector_branch_support d.thetaB outer inner ho hi q sigma (tsupport_mul_subset_right hK))
    simpa only [mixedHybridVolume,deformedPoint_zero] using hh
  apply finite_cover_integral_norm_le volume T (mixedPositiveAngularHalf d.thetaB j) K cell F L
    (mixedPositiveAngularHalf_measurable _ _) (hF.mono_set (fun _ hθ => hθ.1)) hD hL0
    (fun I _ => mixedAngularCell_measurable _ _ _ _) (fun I hI => (hCells I hI).1)
    (fun I hI => (hCells I hI).2) hSupp
  · intro θ hθ hK
    have hNest := tsupport_mul_subset_right hK
    have hAnchor := (nested_sector_jet_support d.thetaB outer inner ho hi q sigma [] hNest).1
    obtain ⟨I,hI,hθq⟩ := hCover (θ q) ⟨hθ.1.1 q,hθ.1.2 q⟩
      (sectorOuterAnchor_tsupport d.thetaB outer ho q hAnchor)
    have hu := hWidth inner hi (hinner.trans (min_le_right _ _)) N η α hα hαsmall θ hθ.1
      (tsupport_mul_subset_left hK) j (nested_sector_branch_support d.thetaB outer inner ho hi q sigma hNest j hj)
    refine ⟨I,hI,⟨⟨hθ.1,?_,?_⟩,hθq⟩⟩
    · have hu0 := hθ.2; dsimp at hu0 ⊢; linarith
    · dsimp
      linarith [(abs_lt.mp hu).2]
  · intro θ hθ hK
    have hh := hPoint θ hθ.1 hK
    apply hh.trans
    have hv := mul_le_mul_of_nonneg_left (hV θ hθ.1 hK) (norm_nonneg (mixedSimpleKernel f r τ 0 s θ))
    have hv' := mul_le_mul_of_nonneg_left hv hD
    exact hv'.trans_eq (by dsimp [L,mixedPositiveKernelMajorant,f,r,s]; ring)

end
end IsingBulk.Tail
