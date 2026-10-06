import IsingBulk.Analysis.BranchAsymptotic
import IsingBulk.Analysis.BranchLength
import IsingBulk.Analysis.BranchSourceRange

/-! Source-facing branch geometry. The conclusion bundle is constructed from
the actual dispersion and sheet proofs; it is never an input assumption. -/
namespace IsingBulk.Branch
noncomputable section
open MeasureTheory Set

def CurrentParameters (d : LocalBranchData) (ε₀ ε lam ρ : ℝ) : Prop :=
  0 < ε ∧ ε ≤ ε₀ ∧ 0 ≤ lam ∧ lam ≤ ε^d.alpha ∧ 0 ≤ ρ ∧ ρ ≤ 1

structure BranchEstimates (d : LocalBranchData) where
  original : OriginalQuotientData d
  r : ℝ
  ε₀ : ℝ
  normalC : ℝ
  magnitudeLower : ℝ
  magnitudeUpper : ℝ
  attenuationLower : ℝ
  lengthC : ℝ
  r_pos : 0 < r
  ε₀_pos : 0 < ε₀
  ε₀_le_r : ε₀ ≤ r
  original_radius : r < original.r
  normalC_pos : 0 < normalC
  magnitudeLower_pos : 0 < magnitudeLower
  magnitudeUpper_pos : 0 < magnitudeUpper
  attenuationLower_pos : 0 < attenuationLower
  lengthC_pos : 0 < lengthC
  normal : ∀ ε u, 0 < ε → ε ≤ ε₀ → |u| ≤ r →
    ‖originalD d ε u-((d.a:ℂ)*u-Complex.I*(d.b:ℂ)*ε)‖ ≤ normalC*(u^2+ε*|u|+ε^2)
  quadrant : ∀ ε u, 0 < ε → ε ≤ ε₀ → |u| ≤ r →
    0 < (originalW d ε u).re ∧ 0 < (originalW d ε u).im
  magnitude : ∀ ε u, 0 < ε → ε ≤ ε₀ → |u| ≤ r →
    magnitudeLower/Real.sqrt (|u|+ε) ≤ ‖deriv (originalPhase d ε) u‖ ∧
      ‖deriv (originalPhase d ε) u‖ ≤ magnitudeUpper/Real.sqrt (|u|+ε)
  attenuation : ∀ ε u, 0 < ε → ε ≤ ε₀ → u ≤ 0 → |u| ≤ r →
    attenuationLower*Real.sqrt (|u|+ε) ≤ -(originalPhase d ε u).im
  length : ∀ ε, 0 < ε → ε ≤ ε₀ →
    IntervalIntegrable (fun u => ‖deriv (originalPhase d ε) u‖) volume (-r) r ∧
      (∫ u in -r..r, ‖deriv (originalPhase d ε) u‖) ≤ lengthC
  current_range : ∀ ε lam ρ, CurrentParameters d ε₀ ε lam ρ → 0 ≤ lam*ρ ∧ lam*ρ < r
  current : ∀ ε lam ρ u, CurrentParameters d ε₀ ε lam ρ → |u| ≤ r →
    (0 < (currentW d ε (lam*ρ) u).re ∧ 0 < (currentW d ε (lam*ρ) u).im) ∧
    (magnitudeLower/Real.sqrt (|u|+ε+lam*ρ) ≤ ‖deriv (currentPhase d ε (lam*ρ)) u‖ ∧
      ‖deriv (currentPhase d ε (lam*ρ)) u‖ ≤ magnitudeUpper/Real.sqrt (|u|+ε+lam*ρ)) ∧
    (u ≤ 0 → attenuationLower*Real.sqrt (|u|+ε+lam*ρ) ≤ -(currentPhase d ε (lam*ρ) u).im) ∧
    (0 ≤ u → (2/3:ℝ)*‖deriv (currentPhase d ε (lam*ρ)) u‖ ≤ (deriv (currentPhase d ε (lam*ρ)) u).re)

/-- The complete local manuscript branch estimates, with all margins and
thresholds fixed before epsilon, dimension, occupancy and deformation. -/
theorem lemma_branch (d : LocalBranchData) : Nonempty (BranchEstimates d) := by
  obtain ⟨B⟩ := original_quotient_data d
  obtain ⟨Cn,rn,hCn,hrn,hnormal⟩ := original_normal_form d
  obtain ⟨cm,Cm,rm,hcm,hCm,hrm,hmag⟩ := current_derivative_magnitude d
  obtain ⟨ca,ra,hca,hra,hatt⟩ := current_negative_attenuation d
  obtain ⟨rc,hrc,hcone⟩ := current_positive_cone d
  obtain ⟨rb,hrb,hbranch⟩ := current_branch_inclusion d
  obtain ⟨Cl,rl,el,hCl,hrl,hel,hlength⟩ := original_branch_length d
  have hrB := B.r_pos
  let R := min B.r (min rn (min rm (min ra (min rc (min rb rl)))))
  have hR : 0 < R := by dsimp [R]; positivity
  let r := R/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr : r < R := by dsimp [r]; linarith
  have hrs : r < B.r ∧ r < rn ∧ r < rm ∧ r < ra ∧ r < rc ∧ r < rb ∧ r < rl := by
    simpa only [R,lt_min_iff] using hrr
  obtain ⟨hrB',hrn',hrm',hra',hrc',hrb',hrl'⟩ := hrs
  obtain ⟨er,her,hrange⟩ := source_current_range d r hr
  let ε₀ := min r (min el er)
  have hε₀ : 0 < ε₀ := lt_min hr (lt_min hel her)
  have her₁ : ε₀ ≤ r := min_le_left _ _
  have her₂ : ε₀ ≤ el := (min_le_right _ _).trans (min_le_left _ _)
  have her₃ : ε₀ ≤ er := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨⟨B,r,ε₀,Cn,cm,Cm,ca,Cl,hr,hε₀,her₁,hrB',hCn,hcm,hCm,hca,hCl,
    ?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro ε u hε hεr hur
    exact hnormal ε u hε.le ((hεr.trans her₁).trans_lt hrn') (hur.trans_lt hrn')
  · intro ε u hε hεr hur
    exact hbranch ε 0 u hε ((hεr.trans her₁).trans_lt hrb') le_rfl hrb (hur.trans_lt hrb')
  · intro ε u hε hεr hur
    have he : originalPhase d ε = currentPhase d ε 0 := by funext v; rfl
    rw [he]
    simpa only [add_zero] using hmag ε 0 u hε ((hεr.trans her₁).trans_lt hrm') le_rfl hrm (hur.trans_lt hrm')
  · intro ε u hε hεr hu hur
    change ca*Real.sqrt (|u|+ε) ≤ -(currentPhase d ε 0 u).im
    simpa only [add_zero] using hatt ε 0 u hε ((hεr.trans her₁).trans_lt hra') le_rfl hra hu (hur.trans_lt hra')
  · intro ε hε hεr
    obtain ⟨hi,hbound⟩ := hlength ε hε (hεr.trans her₂)
    have hsub : uIcc (-r) r ⊆ uIcc (-rl) rl := by
      rw [uIcc_of_le (by linarith : -r ≤ r),uIcc_of_le (by linarith : -rl ≤ rl)]
      exact Icc_subset_Icc (by linarith) hrl'.le
    refine ⟨hi.mono_set hsub,?_⟩
    exact (intervalIntegral.integral_mono_interval (by linarith) (by linarith) hrl'.le
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hi).trans hbound
  · intro ε lam ρ h
    exact hrange ε lam ρ h.1 (h.2.1.trans her₃) h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  · intro ε lam ρ u h hur
    have ht := hrange ε lam ρ h.1 (h.2.1.trans her₃) h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    have he : ε ≤ r := h.2.1.trans her₁
    refine ⟨hbranch ε (lam*ρ) u h.1 (he.trans_lt hrb') ht.1 (ht.2.trans hrb') (hur.trans_lt hrb'),
      hmag ε (lam*ρ) u h.1 (he.trans_lt hrm') ht.1 (ht.2.trans hrm') (hur.trans_lt hrm'),
      fun hu => hatt ε (lam*ρ) u h.1 (he.trans_lt hra') ht.1 (ht.2.trans hra') hu (hur.trans_lt hra'),?_⟩
    intro hu
    exact hcone ε (lam*ρ) u h.1 (he.trans_lt hrc') ht.1 (ht.2.trans hrc') hu
      (by simpa [abs_of_nonneg hu] using hur.trans_lt hrc')

end
end IsingBulk.Branch
