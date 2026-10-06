import IsingBulk.Tail.AllBranchExteriorPositiveJacobian

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set Filter
open scoped Topology BigOperators

def allBranchExteriorCurvature {d : LocalBranchData} (B : BranchEstimates d) : ℝ :=
  B.original.k*B.r^(-(3/2:ℝ))

theorem allBranchExterior_curvature_pos {d : LocalBranchData} (B : BranchEstimates d) :
    0 < allBranchExteriorCurvature B :=
  mul_pos B.original.k_pos (Real.rpow_pos_of_pos B.r_pos _)

theorem allBranchExterior_realPhase_deriv_differentiable {d : LocalBranchData}
    (B : BranchEstimates d) (ε u : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀)
    (hu : 0 ≤ u) (hur : u ≤ B.r) :
    DifferentiableAt ℝ (deriv (originalRealPhase d ε)) u := by
  obtain ⟨hre,him⟩ := B.quadrant ε u hε hεr (by simpa [abs_of_nonneg hu] using hur)
  have hd := currentPhase_second_hasDerivAt d ε 0 u hre him
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd
  have he : deriv (originalRealPhase d ε) =ᶠ[𝓝 u]
      (fun v => (deriv (currentPhase d ε 0) v).re) := by
    filter_upwards [current_phase_quadrant_near d ε 0 u hre him] with v hv
    exact realPhase_deriv d ε 0 v hv.1 hv.2
  exact (hr.congr_of_eventuallyEq he).differentiableAt

theorem allBranchExterior_actual_slope_gap {d : LocalBranchData} (B : BranchEstimates d)
    (ε x y : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀)
    (hx : B.original.C₀*ε ≤ x) (hxy : x ≤ y) (hy : y ≤ B.r) :
    allBranchExteriorCurvature B*(y-x) ≤
      deriv (originalRealPhase d ε) x-deriv (originalRealPhase d ε) y := by
  have hxp : 0 < x := (mul_pos B.original.C₀_pos hε).trans_le hx
  have hd (u : ℝ) (hu : u ∈ Icc x y) :
      DifferentiableAt ℝ (deriv (originalRealPhase d ε)) u :=
    allBranchExterior_realPhase_deriv_differentiable B ε u hε hεr
      (hxp.le.trans hu.1) (hu.2.trans hy)
  have hc : ContinuousOn (deriv (originalRealPhase d ε)) (Icc x y) :=
    fun u hu => (hd u hu).continuousAt.continuousWithinAt
  have hf : DifferentiableOn ℝ (deriv (originalRealPhase d ε)) (interior (Icc x y)) :=
    fun u hu => (hd u (interior_subset hu)).differentiableWithinAt
  have hb : ∀ u ∈ interior (Icc x y),
      deriv (deriv (originalRealPhase d ε)) u ≤ -allBranchExteriorCurvature B := by
    intro u hu
    have hui := interior_subset hu
    have hconc := B.concavity ε u hε hεr (hx.trans hui.1) (hui.2.trans hy)
    have hp := Real.rpow_le_rpow_of_nonpos (hxp.trans_le hui.1) (hui.2.trans hy)
      (by norm_num : -(3/2:ℝ) ≤ 0)
    have hm := mul_le_mul_of_nonneg_left hp B.original.k_pos.le
    dsimp [allBranchExteriorCurvature]
    linarith
  have hh := (convex_Icc x y).image_sub_le_mul_sub_of_deriv_le hc hf hb
    x ⟨le_rfl,hxy⟩ y ⟨hxy,le_rfl⟩ hxy
  linarith

def allBranchExteriorShapePhase {N : ℕ} (d : LocalBranchData) (ε t : ℝ)
    (ω : Fin N → ℝ) (ρ : ℝ) : ℝ := ∑ i, originalRealPhase d ε (t+ρ*ω i)

theorem allBranchExterior_shape_hasDerivAt {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε t ρ : ℝ) (ω : Fin N → ℝ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀)
    (hu : ∀ i, 0 ≤ t+ρ*ω i ∧ t+ρ*ω i ≤ B.r) :
    HasDerivAt (allBranchExteriorShapePhase d ε t ω)
      (∑ i, deriv (originalRealPhase d ε) (t+ρ*ω i)*ω i) ρ := by
  apply HasDerivAt.fun_sum
  intro i _
  have hh := (allBranchExterior_realPhase_differentiable B ε (t+ρ*ω i) hε hεr
    (hu i).1 (hu i).2).hasDerivAt
  have hl : HasDerivAt (fun x : ℝ => t+x*ω i) (ω i) ρ := by
    simpa using ((hasDerivAt_id ρ).mul_const (ω i)).const_add t
  exact hh.comp ρ hl

theorem allBranchExterior_shape_radial_bound {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε t ρ : ℝ) (ω : Fin N → ℝ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (hρ : 0 ≤ ρ)
    (hzero : ∑ i, ω i=0) (hunit : ∑ i, (ω i)^2=1)
    (ht : B.original.C₀*ε ≤ t) (htr : t ≤ B.r)
    (hu : ∀ i, B.original.C₀*ε ≤ t+ρ*ω i ∧ t+ρ*ω i ≤ B.r) :
    allBranchExteriorCurvature B*ρ ≤ -deriv (allBranchExteriorShapePhase d ε t ω) ρ := by
  have hi (i : Fin N) : allBranchExteriorCurvature B*ρ*(ω i)^2 ≤
      (deriv (originalRealPhase d ε) t-deriv (originalRealPhase d ε) (t+ρ*ω i))*ω i := by
    by_cases hw : 0 ≤ ω i
    · have horder : t ≤ t+ρ*ω i := by nlinarith
      have hh := mul_le_mul_of_nonneg_right
        (allBranchExterior_actual_slope_gap B ε t (t+ρ*ω i) hε hεr ht horder (hu i).2) hw
      nlinarith
    · have hw' : ω i ≤ 0 := le_of_not_ge hw
      have horder : t+ρ*ω i ≤ t := by nlinarith
      have hh := mul_le_mul_of_nonpos_right
        (allBranchExterior_actual_slope_gap B ε (t+ρ*ω i) t hε hεr (hu i).1 horder htr) hw'
      nlinarith
  have hd := allBranchExterior_shape_hasDerivAt B ε t ρ ω hε hεr
    (fun i => ⟨(mul_pos B.original.C₀_pos hε).le.trans (hu i).1,(hu i).2⟩)
  rw [hd.deriv]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_sub_distrib,sub_mul,← Finset.mul_sum,hzero,hunit,mul_zero,mul_one,
    zero_sub] at hh
  exact hh

theorem allBranchExterior_shape_jacobian {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε t ρ : ℝ) (ω : Fin N → ℝ)
    (hε : 0 < ε) (hεr : ε ≤ B.ε₀) (hρ : 0 ≤ ρ)
    (hzero : ∑ i, ω i=0) (hunit : ∑ i, (ω i)^2=1)
    (ht : B.original.C₀*ε ≤ t) (htr : t ≤ B.r)
    (hu : ∀ i, B.original.C₀*ε ≤ t+ρ*ω i ∧ t+ρ*ω i ≤ B.r) :
    (N:ℝ)*allBranchExteriorCurvature B*ρ ≤
      |(N:ℝ)*deriv (allBranchExteriorShapePhase d ε t ω) ρ| := by
  have hh := mul_le_mul_of_nonneg_left
    (allBranchExterior_shape_radial_bound B ε t ρ ω hε hεr hρ hzero hunit ht htr hu)
    (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  calc
    _ ≤ -((N:ℝ)*deriv (allBranchExteriorShapePhase d ε t ω) ρ) := by nlinarith
    _ ≤ _ := neg_le_abs _

end
end IsingBulk.Tail
