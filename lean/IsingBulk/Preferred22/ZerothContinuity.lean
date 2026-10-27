import IsingBulk.Preferred22.ZerothSourceBound
import IsingBulk.Preferred22.ShellIntegration

/-! Actual integrability of the physical j=0 density on every right shell.
Continuity is proved from the selected physical roots and the rational gauge
determinant identity; no regular-coordinate or tail bound is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ContDiff

set_option maxHeartbeats 1400000 in
theorem preferred_physical_seed_continuous {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0<ε) (hτ : 0≤τ) (η rcut : ℝ → ℝ) (hη : Continuous η) (hrcut : Continuous rcut) :
    Continuous (fun θ : Fin N → ℝ => preferredPhysicalSeed .right τ η B.p B.m rcut
      (IsingBulk.Branch.radialParameter d.alpha ε) θ) := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let y := fun (θ : Fin N → ℝ) i => Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i)
  let z := fun (θ : Fin N → ℝ) i => physicalRoot (preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i))
  have hw (i : Fin N) : Continuous (fun θ : Fin N → ℝ => deformedAngles τ B.p B.m θ i) :=
    (preferred_deformed_source_smooth d B τ i).continuous
  have hs : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hW (θ : Fin N → ℝ) (i : Fin N) :
      0<(preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)).im :=
    (mul_pos hε hs).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)
  have hy (i : Fin N) : Continuous (fun θ => y θ i) := by dsimp [y]; fun_prop
  have hynz (θ : Fin N → ℝ) (i : Fin N) : y θ i≠0 := Complex.exp_ne_zero _
  have hz (i : Fin N) : Continuous (fun θ => z θ i) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact ContinuousAt.comp
      (f := fun θ : Fin N → ℝ => preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i))
      (g := physicalRoot) (physicalRoot_analyticAt (Or.inl (hW θ i).ne')).continuousAt
      ((continuous_const.sub (Complex.continuous_cos.comp (hw i))).continuousAt)
  have hzlt (θ : Fin N → ℝ) (i : Fin N) : ‖z θ i‖<1 := physicalRoot_inside (Or.inl (hW θ i).ne')
  have hpair (θ : Fin N → ℝ) (i j : Fin N) : 1-z θ i*z θ j≠0 := by
    intro h
    have he : z θ i*z θ j=1 := (sub_eq_zero.mp h).symm
    have hn : ‖z θ i*z θ j‖<1 := by
      rw [norm_mul]
      calc
        _ ≤ ‖z θ i‖*1 := mul_le_mul_of_nonneg_left (hzlt θ j).le (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hzlt θ i
    rw [he,norm_one] at hn
    exact (lt_irrefl 1) hn
  have hK (i j : Fin N) : Continuous (fun θ => rationalKernel (y θ) (z θ) i j) :=
    ((hy i).sub (hy j)).div (continuous_const.sub ((hz i).mul (hz j))) (fun θ => hpair θ i j)
  have hdetR : Continuous (fun θ => (rationalKernel (y θ) (z θ)).det) :=
    (continuous_pi (fun i => continuous_pi (fun j => hK i j))).matrix_det
  have hquotprod : Continuous (fun θ => ∏ i,z θ i/y θ i) :=
    continuous_finsetProd _ (fun i _ => (hz i).div (hy i) (fun θ => hynz θ i))
  have hdetK : Continuous (fun θ => (gaugeKernel (y θ) (z θ)).det) := by
    simp_rw [gaugeKernel_det_normalization]
    exact (continuous_const.mul hquotprod).mul hdetR
  have hbody (i : Fin N) : Continuous (fun θ => oneBody (z θ i)) := by
    unfold oneBody
    exact (continuous_const.mul (hz i)).div (continuous_const.sub ((hz i).pow 2))
      (fun θ => by simpa only [pow_two] using hpair θ i i)
  have hZ : Continuous (fun θ => ∏ i,z θ i) := continuous_finsetProd _ (fun i _ => hz i)
  have hZden (θ : Fin N → ℝ) : 1-∏ i,z θ i≠0 :=
    norm_ne_zero_iff.mp (preferred_actual_denominator_ne_zero hN d B hε hτ θ)
  have hD : Continuous (fun θ : Fin N → ℝ => preferredDeformedPhysicalDensity τ B.p B.m s θ) := by
    change Continuous (fun θ : Fin N → ℝ => (1+∏ i,z θ i)/(1-∏ i,z θ i) *
      (gaugeKernel (y θ) (z θ)).det * ∏ i,oneBody (z θ i))
    exact (((continuous_const.add hZ).div (continuous_const.sub hZ) hZden).mul hdetK).mul
      (continuous_finsetProd _ (fun i _ => hbody i))
  have hM : Continuous (fun θ : Fin N → ℝ => (preferredContourMatrix τ B.p B.m θ).det) := by
    simp_rw [preferredContourMatrix_eq_full]
    exact (fullAngularJacobian_det_contDiff 1 τ B.p B.m B.smooth B.m_smooth).continuous
  have hweight : Continuous (fun θ : Fin N → ℝ => preferredCellWeight .right η B.p B.m rcut θ) := by
    have hp := B.smooth.continuous
    have hm := B.m_smooth.continuous
    unfold preferredCellWeight preferredLowerWeight preferredRightWeight lowerWeight occupancy
    fun_prop
  unfold preferredPhysicalSeed
  exact (((Complex.continuous_ofReal.comp hweight).mul hM).mul hD).div_const _

theorem preferredLinearRightShell_isCompact {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB r : ℝ) (l : ℤ) (i j : Fin (n+1)) :
    IsCompact (preferredLinearRightShell d B δB r l i j) := by
  apply (isCompact_univ_pi (fun _ : Fin n => (isCompact_Icc : IsCompact (Icc (-d.b-δB) B.delta)))).of_isClosed_subset
    (preferredLinearRightShell_isClosed d B δB r l i j)
  intro θ hθ v _
  simpa only [constrainedAtTotal,Fin.snoc_castSucc] using hθ.1 v.castSucc

/-- Actual j=0 integrability, independently of the quantitative shell bound. -/
theorem preferred_zeroth_right_shell_integrable {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ δB : ℝ} (hε : 0<ε) (hτ : 0≤τ)
    (hδB : δB<B.delta) (η rcut : ℝ → ℝ) (hη : Continuous η) (hrcut : Continuous rcut)
    (r : ℝ) (l : ℤ) (i j : Fin (n+1)) :
    IntegrableOn (fun x : Fin n → ℝ => preferredTransportedDensity .right τ η B.p B.m rcut 0
      (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x)))
        (preferredRightShell d B δB r l i j) := by
  rw [preferredRightShell_eq_linear d B hδB]
  have hc : Continuous (constrainedAtTotal (n := n) (2*Real.pi*(l:ℝ))) := by
    unfold constrainedAtTotal
    fun_prop
  have hseed := preferred_physical_seed_continuous (by omega : 0<n+1) d B hε hτ η rcut hη hrcut
  have hi := (hseed.comp hc).continuousOn.integrableOn_compact (μ := volume)
    (preferredLinearRightShell_isCompact d B δB r l i j)
  apply hi.congr_fun _ (preferredLinearRightShell_isClosed d B δB r l i j).measurableSet
  intro x hx
  dsimp only
  rw [(preferred_lift_eq_affine_from_right d B hδB l x hx.1).2]
  rfl

end
end IsingBulk.Preferred22
