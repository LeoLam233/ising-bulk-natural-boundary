import IsingBulk.Preferred22.CellRegularity
import IsingBulk.Preferred22.LiftedTransportCalculus
import IsingBulk.Preferred22.AngularInverseJets

/-! Actual named-anchor geometry at positive physical epsilon. The anchor
uses its own nonzero inverse-coordinate derivative and has no equality
puncture. Upper population support removes the modular seam exactly. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- One positive-epsilon source regime gives genuine anchor regularity and
ambient tangency on the complete one-sided physical interval, before N. -/
theorem preferred_actual_anchor_geometry (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ τ₀ ε₀ : ℝ,0<τ₀ ∧ 0<ε₀ ∧ ∀ N : ℕ,0<N →
      ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ a : Fin N,
      (IsingBulk.Branch.radialParameter d.alpha ε,θ)∈preferredCellRegularDomain (.anchor a) τ B.p B.m ∧
      (∑ i,preferredSourceAngularField (.anchor a) τ B.p B.m
        (IsingBulk.Branch.radialParameter d.alpha ε) θ i)=0 := by
  obtain ⟨ε₀,hε₀,hmargin⟩ := preferred_radial_one_sided_margins d B.delta B.delta_pos
    (B.delta_alpha.trans (half_lt_self d.alpha_pos))
  obtain ⟨τ₀,hτ₀,hMrow⟩ := preferredContourMatrix_uniform_half_row B.p B.m B.smooth B.m_smooth
    B.periodic B.m_periodic
    (fun x => by rw [abs_of_nonneg (B.lower_bound x)]; exact B.upper_bound x)
    (fun x => by change |B.p (-x)|≤1; rw [abs_of_nonneg (B.lower_bound (-x))]; exact B.upper_bound (-x))
  refine ⟨τ₀,ε₀,hτ₀,hε₀,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ a
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  obtain ⟨hS,hSi,hSδ⟩ := hmargin ε hε hεr
  have hδπ : B.delta<Real.pi/2 := (B.delta_alpha.trans (half_lt_self d.alpha_pos)).trans d.alpha_lt
  have hM : (preferredContourMatrix τ B.p B.m θ).det≠0 :=
    (preferred_matrix_inverse_of_row_three_quarters _
      (fun i => (hMrow τ hτ hτr.le N hN θ i).trans (by norm_num))).1
  have hW (i : Fin N) : 0<(temperatureTrace s-Complex.cos (deformedAngles τ B.p B.m θ i)).im := by
    have hh := homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1) B.p B.m θ
      B.lower_bound (fun x => B.lower_bound (-x))
      (fun x hx => B.p_zero_of_sin_nonpos hx) (fun x hx => B.m_zero_of_sin_nonneg hx) i
    simpa only [complexW_homotopyRoot_eq] using hh
  have hwre (i : Fin N) : (deformedAngles τ B.p B.m θ i).re=θ i := by
    simp [deformedAngles,Complex.mul_re]
  have ha : preferredSourceUQ s (preferredSourceCoordinate τ B.p B.m s θ a)≠0 :=
    (preferred_global_one_sided_q_regular s (deformedAngles τ B.p B.m θ a) B.delta B.delta_pos hδπ hS hSδ
      (by rw [hwre]; exact (hθ a).1) (by rw [hwre]; exact (hθ a).2) (hW a)).2
  exact ⟨preferredCellRegularDomain_anchor_of_oneSided a τ B.delta B.p B.m s θ
    B.delta_pos hδπ hS hSi hSδ hθ hW hM,
    preferredSourceAngularField_anchor_tangent τ B.p B.m s θ a hM ha⟩

/-- Ordinary smoothness on the physical lower interval extends to the
entire one-sided period because the upper particle population kills the
function on a genuine neighborhood. -/
theorem preferredLowerSupportedFunction_contDiffAt {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (F : ℂ × (Fin N → ℝ) → ℂ)
    (hzero : ∀ s θ i,1/2<B.p (θ i) → F (s,θ)=0)
    (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta))
    (hcore : (∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) → ContDiffAt ℝ ∞ F (s,θ)) :
    ContDiffAt ℝ ∞ F (s,θ) := by
  classical
  by_cases hu : ∀ i,θ i≤B.delta
  · exact hcore (fun i => ⟨(hθ i).1.le,hu i⟩)
  · obtain ⟨i,hi⟩ := not_forall.mp hu
    have hp : 1/2<B.p (θ i) := by
      rw [B.plateau (θ i) ⟨(lt_of_not_ge hi).le,(hθ i).2⟩]
      norm_num
    exact contDiffAt_const.congr_of_eventuallyEq (preferredUpperParticle_zero_germ d B F hzero s θ i hp)

/-- The exact named-anchor current for the original scalar recurrence. -/
def preferredAnchorCurrent {N : ℕ} (a : Fin N) (τ : ℝ) (p m rcut : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  preferredSourceAngularField (.anchor a) τ p m s θ i*
    preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff p m rcut j s θ

theorem preferredAnchorCurrent_upper_zero {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (a : Fin N) (τ : ℝ) (rcut : ℝ → ℝ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (v : Fin N) (hv : 1/2<B.p (θ v)) (i : Fin N) :
    preferredAnchorCurrent a τ B.p B.m rcut j s θ i=0 := by
  unfold preferredAnchorCurrent
  rw [preferredTransportedDensity_cell_zero_of_upper_particle (.anchor a) d B τ rcut j s θ v hv,mul_zero]

/-- Genuine ambient smoothness of every anchor density and current on the
one-sided interval. It includes total equality and the upper period endpoint. -/
theorem preferredAnchor_density_current_contDiffAt {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (a : Fin N) (τ : ℝ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) (s : ℂ) (j : ℕ)
    (hreg : ∀ x : Fin N → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (s,x)∈preferredCellRegularDomain (.anchor a) τ B.p B.m)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff B.p B.m rcut j z.1 z.2) (s,θ) ∧
    ∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredAnchorCurrent a τ B.p B.m rcut j z.1 z.2 i) (s,θ) := by
  have hp (x : Fin N → ℝ) (hx : ∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) :=
    preferredTransportedDensity_mixed_cellDomain (.anchor a) hN τ preferredPopulationCutoff B.p B.m rcut
      preferredPopulationCutoff_smooth B.smooth B.m_smooth hr j (s,x) (hreg x hx)
  constructor
  · exact preferredLowerSupportedFunction_contDiffAt d B _
      (fun t x i hi => preferredTransportedDensity_cell_zero_of_upper_particle (.anchor a) d B τ rcut j t x i hi)
      s θ hθ (fun hx => (hp θ hx).1)
  · intro i
    apply preferredLowerSupportedFunction_contDiffAt d B _
      (fun t x v hv => preferredAnchorCurrent_upper_zero d B a τ rcut j t x v hv i) s θ hθ
    intro hx
    exact ((preferredSourceAngularField_mixed_cellDomain (.anchor a) τ B.p B.m B.smooth B.m_smooth i
      (s,θ) (hreg θ hx)).1).mul (hp θ hx).1

/-- The actual one-sided lift of each named-anchor density/current is
jointly smooth on the original complete torus; no puncture is required. -/
theorem preferredAnchor_density_current_lift_contDiffAt {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (a : Fin N) (τ : ℝ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) (s : ℂ) (j : ℕ)
    (hreg : ∀ x : Fin N → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (s,x)∈preferredCellRegularDomain (.anchor a) τ B.p B.m)
    (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff B.p B.m rcut j z.1
        (preferredLiftedAngles B.delta z.2)) (s,θ) ∧
    ∀ i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredAnchorCurrent a τ B.p B.m rcut j z.1 (preferredLiftedAngles B.delta z.2) i) (s,θ) := by
  have hlocal := preferredAnchor_density_current_contDiffAt hN d B a τ rcut hr s j hreg
    (preferredLiftedAngles B.delta θ) (preferredLiftedAngles_mem_oneSided B.delta θ)
  constructor
  · exact preferredLiftedFunction_contDiffAt d B _
      (fun t x i hi => preferredTransportedDensity_cell_zero_of_upper_particle (.anchor a) d B τ rcut j t x i hi)
      s θ (fun _ => hlocal.1)
  · intro i
    exact preferredLiftedFunction_contDiffAt d B _
      (fun t x v hv => preferredAnchorCurrent_upper_zero d B a τ rcut j t x v hv i)
      s θ (fun _ => hlocal.2 i)

/-- The anchor current is tangent throughout the true period interval,
including configurations excluded by the upper population cutoff. -/
theorem preferredAnchorCurrent_tangent {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (a : Fin N) (τ : ℝ) (rcut : ℝ → ℝ)
    (s : ℂ) (j : ℕ)
    (htan : ∀ x : Fin N → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (∑ i,preferredSourceAngularField (.anchor a) τ B.p B.m s x i)=0)
    (θ : Fin N → ℝ) (hθ : ∀ i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) :
    (∑ i,preferredAnchorCurrent a τ B.p B.m rcut j s θ i)=0 := by
  classical
  by_cases hu : ∀ i,θ i≤B.delta
  · simp only [preferredAnchorCurrent,←Finset.sum_mul,htan θ (fun i => ⟨(hθ i).1.le,hu i⟩),zero_mul]
  · obtain ⟨v,hv⟩ := not_forall.mp hu
    have hp : 1/2<B.p (θ v) := by
      rw [B.plateau (θ v) ⟨(lt_of_not_ge hv).le,(hθ v).2.le⟩]
      norm_num
    exact Finset.sum_eq_zero (fun i _ => preferredAnchorCurrent_upper_zero d B a τ rcut j s θ v hp i)

end
end IsingBulk.Preferred22
