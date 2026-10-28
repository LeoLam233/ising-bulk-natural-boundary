import IsingBulk.HT22.Geometry.SignedAffineCharts
import IsingBulk.HT22.First.LocalLimit.SignedContourBound
import IsingBulk.Preferred22.PhaseAttenuation

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set IsingBulk.Preferred22 IsingBulk.First IsingBulk.Branch LocalLimit
open scoped BigOperators

/-- The actual balanced complex contour in a fixed equality shape chart. -/
def balancedEqualityChart {n : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (μ : ℝ)
    (u : Fin n → ℝ) : Fin (n+1) → ℂ :=
  deformedAngles τ p m (fun i => μ+shapeExtend u i)

theorem balancedEqualityChart_zero (n : ℕ) (τ : ℝ) (p m : ℝ → ℝ) (μ : ℝ) :
    balancedEqualityChart τ p m μ (0:Fin n → ℝ)=fun _ => (μ:ℂ) := by
  have hz : shapeExtend (0:Fin n → ℝ)=0 := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [shapeExtend]
  funext i
  simp only [balancedEqualityChart,hz,Pi.zero_apply,add_zero,deformedAngles,
    balancedShift_at_equality,Complex.ofReal_zero,mul_zero,sub_zero]

theorem balancedEqualityChart_continuous (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ μ : ℝ) :
    Continuous (@balancedEqualityChart n τ B.p B.m μ) := by
  have hp := B.smooth.continuous
  have hm := B.m_smooth.continuous
  have hshape : Continuous (shapeExtend : (Fin n → ℝ) → (Fin (n+1) → ℝ)) := by
    unfold shapeExtend
    fun_prop
  unfold balancedEqualityChart deformedAngles balancedShift occupancy
  fun_prop

/-- The physical upper-sheet condition holds on the entire actual chart,
not merely on an assumed local closed ball. -/
theorem balancedEqualityChart_upper (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {τ ε : ℝ} (hτ : 0≤τ) (hε : 0<ε)
    (μ : ℝ) (u : Fin n → ℝ) (i : Fin (n+1)) :
    0<(temperatureTrace (radialParameter d.alpha ε)-Complex.cos (balancedEqualityChart τ B.p B.m μ u i)).im := by
  have hs : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  exact (mul_pos hε hs).trans_le (preferredActualW_im_lower d B hε.le hτ
    (fun i => μ+shapeExtend u i) i)

/-- Genuine bounded derivatives of localized actual balanced signed
contours; the upper-sheet geometry is discharged, not assumed. -/
theorem balanced_signed_local_derivatives_bounded (n : ℕ) (negative : Bool)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (μ β : ℝ) (hβ : 0<β) (hβπ : β<Real.pi)
    (hrel : 2*Real.cos d.alpha-Real.cos μ=Real.cos β)
    (hgap : 1-Physical.constraintSign negative*(Complex.exp (-(β:ℂ)*Complex.I))^(n+1)≠0) :
    ∃ R : ℝ,0<R ∧ ∀ χ : (Fin n → ℝ) → ℂ,Continuous χ →
      (∀ u,χ u≠0 → ‖u‖<R) → ∀ j : ℕ,
      ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      ‖(deriv^[j] (fun t => ∫ u,χ u*Physical.complexSignedDensity negative
        (t,balancedEqualityChart τ B.p B.m μ u))) (radialParameter d.alpha ε)‖≤C := by
  obtain ⟨R,hR,hbound⟩ := signed_local_contour_derivatives_bounded negative d.alpha μ β hβ hβπ hrel hgap
    (balancedEqualityChart τ B.p B.m μ) (balancedEqualityChart_continuous n d B τ μ)
    (balancedEqualityChart_zero n τ B.p B.m μ)
  refine ⟨R,hR,?_⟩
  intro χ hχ hs j
  exact hbound χ hχ hs 1 zero_lt_one
    (fun ε hε _ u _ i => balancedEqualityChart_upper n d B hτ hε μ u i) j

end
end IsingBulk.HT22.Geometry
