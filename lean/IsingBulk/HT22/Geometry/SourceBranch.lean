import IsingBulk.HT22.Geometry.SourceInverse

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology
open Filter IsingBulk.Preferred22

theorem sourceInverseSlope_relative_cone (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      (1/5:ℝ)*‖sourceInverseSlopeDerivative d ε δ u‖ ≤
        (covarianceDirection*sourceInverseSlopeDerivative d ε δ u).re := by
  obtain ⟨r₁,hr₁,hproj⟩ := sourceInverseSlope_projection d
  obtain ⟨r₂,hr₂,hfactor⟩ := sourceInverseSlopeFactor_small d
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,?_⟩
  intro ε δ u hε hεr hδ hδr hu
  have hp := hproj ε δ u hε (hεr.trans_le (min_le_left _ _)) hδ
    (hδr.trans_le (min_le_left _ _)) (hu.trans_le (min_le_left _ _))
  have hf := hfactor ε δ u
    (by simpa [abs_of_pos hε] using hεr.trans_le (min_le_right r₁ r₂))
    (by simpa [abs_of_nonneg hδ] using hδr.trans_le (min_le_right r₁ r₂))
    (hu.trans_le (min_le_right _ _))
  have hn : ‖sourceInverseSlopeFactor d ε δ u‖ ≤ (5/4:ℝ) := by
    have hh := norm_add_le (sourceInverseSlopeFactor d ε δ u-1) (1:ℂ)
    simp only [sub_add_cancel, norm_one] at hh
    linarith
  have hprod := mul_le_mul_of_nonneg_right hn
    (norm_nonneg ((Complex.sin (outwardPlateauPhase d ε δ u))⁻¹))
  have he : ‖sourceInverseSlopeDerivative d ε δ u‖ =
      ‖sourceInverseSlopeFactor d ε δ u‖*‖(Complex.sin (outwardPlateauPhase d ε δ u))⁻¹‖ := by
    simp only [sourceInverseSlopeDerivative, div_eq_mul_inv, norm_mul]
  rw [he]
  nlinarith

theorem sourceInverseV_hasDeriv (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      HasDerivAt (sourceInverseV d ε δ) (sourceInverseSlopeDerivative d ε δ u) u := by
  obtain ⟨r₁,hr₁,hratio⟩ := sourceInverseV_eq_ratio d
  obtain ⟨r₂,hr₂,hW⟩ := preferred_outward_branch_domain d
  obtain ⟨_,r₃,_,hr₃,hden⟩ := sourceInverseSlope_denominator_bound d
  obtain ⟨_,_,r₄,_,_,hr₄,hsine⟩ := outward_sine_all_signs d
  let r := min r₁ (min r₂ (min r₃ r₄))
  refine ⟨r,lt_min hr₁ (lt_min hr₂ (lt_min hr₃ hr₄)),?_⟩
  intro ε δ u hε hεr hδ hδr hu
  have h1 : r ≤ r₁ := min_le_left _ _
  have h2 : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : r ≤ r₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : r ≤ r₄ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hwr,hwi⟩ := hW ε δ u hε (hεr.trans_le h2) hδ (hδr.trans_le h2) (hu.trans_le h2)
  have hd := (hden ε δ u (by simpa [abs_of_pos hε] using hεr.trans_le h3)
    (by simpa [abs_of_nonneg hδ] using hδr.trans_le h3) (hu.trans_le h3)).1
  have hsr := (hsine ε δ u hε (hεr.trans_le h4) hδ (hδr.trans_le h4) (hu.trans_le h4)).2.2.1
  have hs : Complex.sin (outwardPlateauPhase d ε δ u) ≠ 0 := by
    intro hz
    rw [hz,Complex.zero_re] at hsr
    exact (lt_irrefl 0) hsr
  have he : sourceInverseV d ε δ =ᶠ[𝓝 u] sourceInverseSlopeValue d ε δ := by
    have hnear : ∀ᶠ x : ℝ in 𝓝 u, |x| < r₁ :=
      continuous_abs.continuousAt.eventually_lt continuousAt_const (hu.trans_le h1)
    filter_upwards [hnear] with x hx
    exact hratio ε δ x hε (hεr.trans_le h1) hδ (hδr.trans_le h1) hx
  exact (sourceInverseSlope_hasDerivAt d ε δ u hwr hwi hs hd).congr_of_eventuallyEq he

/-- All three genuine source estimates, on the negative sliver as well as
on the positive side. These are for canonical literal Uv, not a moving-q
surrogate or a postulated sector. -/
theorem sourceInverseV_branch_estimates (d : PreferredBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε δ u : ℝ,
      0 < ε → ε < r → 0 ≤ δ → δ < r → |u| < r →
      HasDerivAt (sourceInverseV d ε δ) (sourceInverseSlopeDerivative d ε δ u) u ∧
      (1/5:ℝ)*‖sourceInverseSlopeDerivative d ε δ u‖ ≤
        (covarianceDirection*sourceInverseSlopeDerivative d ε δ u).re ∧
      c/Real.sqrt (|u|+ε+δ) ≤
        (covarianceDirection*sourceInverseSlopeDerivative d ε δ u).re ∧
      ‖sourceInverseV d ε δ u‖ ≤ C*Real.sqrt (|u|+ε+δ) := by
  obtain ⟨r₁,hr₁,hder⟩ := sourceInverseV_hasDeriv d
  obtain ⟨r₂,hr₂,hcone⟩ := sourceInverseSlope_relative_cone d
  obtain ⟨c,r₃,hc,hr₃,hlower⟩ := sourceInverseSlope_lower d
  obtain ⟨C,r₄,hC,hr₄,hupper⟩ := sourceInverseSlope_upper d
  obtain ⟨r₅,hr₅,hratio⟩ := sourceInverseV_eq_ratio d
  let r := min r₁ (min r₂ (min r₃ (min r₄ r₅)))
  refine ⟨c,C,r,hc,hC,lt_min hr₁ (lt_min hr₂ (lt_min hr₃ (lt_min hr₄ hr₅))),?_⟩
  intro ε δ u hε hεr hδ hδr hu
  have h1 : r ≤ r₁ := min_le_left _ _
  have h2 : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : r ≤ r₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : r ≤ r₄ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have h5 : r ≤ r₅ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨hder ε δ u hε (hεr.trans_le h1) hδ (hδr.trans_le h1) (hu.trans_le h1),
    hcone ε δ u hε (hεr.trans_le h2) hδ (hδr.trans_le h2) (hu.trans_le h2),
    hlower ε δ u hε (hεr.trans_le h3) hδ (hδr.trans_le h3) (hu.trans_le h3),?_⟩
  rw [hratio ε δ u hε (hεr.trans_le h5) hδ (hδr.trans_le h5) (hu.trans_le h5)]
  exact hupper ε δ u hε (hεr.trans_le h4) hδ (hδr.trans_le h4) (hu.trans_le h4)

end
end IsingBulk.HT22.Geometry
