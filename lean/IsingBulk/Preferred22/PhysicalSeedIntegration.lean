import IsingBulk.Preferred22.PhysicalDensityRegularity
import IsingBulk.Preferred22.VerticalLattice

/-! Actual compact angular integrability for every physical cutoff cell.
This uses the full physical density, not any transport-envelope hypothesis. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ContDiff

/-- Every literal right or anchor seed is globally C∞ in its real angular
arguments at a positive radial displacement on the balanced contour. -/
theorem preferredPhysicalSeed_radial_contDiff {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (cell : PreferredTransportCell N)
    {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ) (η rcut : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hr : ContDiff ℝ ∞ rcut) :
    ContDiff ℝ ∞ (fun θ : Fin N → ℝ => preferredPhysicalSeed cell τ η B.p B.m rcut
      (IsingBulk.Branch.radialParameter d.alpha ε) θ) := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hSi : 0<(temperatureTrace s).im := preferredRadialTrace_im_pos d hε
  have hs : s≠0 := by intro he; rw [he] at hSi; simp [temperatureTrace] at hSi
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hW (i : Fin N) : OffRealSegment (temperatureTrace s-Complex.cos (deformedAngles τ B.p B.m θ i)) := by
    left
    have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
      (by linarith [d.alpha_lt,Real.pi_pos])
    exact ((mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ θ i)).ne'
  exact ContDiffAt.comp (f := fun θ : Fin N → ℝ => (s,θ))
    (g := fun z : ℂ × (Fin N → ℝ) => preferredPhysicalSeed cell τ η B.p B.m rcut z.1 z.2) θ
    (preferredPhysicalSeed_contDiffAt hN cell τ η B.p B.m rcut hη B.smooth B.m_smooth hr s θ hs hW)
    (contDiffAt_const.prodMk contDiffAt_id)

/-- Actual Haar-box integrability after the full coupled constraint map,
for the right cell and every named anchor. -/
theorem preferredPhysicalSeed_integrableOn_angularBox (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (cell : PreferredTransportCell (n+1))
    {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ) (η rcut : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hr : ContDiff ℝ ∞ rcut) :
    IntegrableOn (fun θ : Fin n → ℝ => preferredPhysicalSeed cell τ η B.p B.m rcut
      (IsingBulk.Branch.radialParameter d.alpha ε) (constrainedAngles θ)) (angularBox n) :=
  continuous_integrableOn_angularBox
    ((preferredPhysicalSeed_radial_contDiff (by omega) d B cell hε hτ η rcut hη hr).continuous.comp
      (constrainedAngles_continuous n))

/-- The same compact integral is absolutely integrable. -/
theorem preferredPhysicalSeed_norm_integrableOn_angularBox (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (cell : PreferredTransportCell (n+1))
    {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ) (η rcut : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hr : ContDiff ℝ ∞ rcut) :
    IntegrableOn (fun θ : Fin n → ℝ => ‖preferredPhysicalSeed cell τ η B.p B.m rcut
      (IsingBulk.Branch.radialParameter d.alpha ε) (constrainedAngles θ)‖) (angularBox n) :=
  (preferredPhysicalSeed_integrableOn_angularBox n d B cell hε hτ η rcut hη hr).norm

end
end IsingBulk.Preferred22
