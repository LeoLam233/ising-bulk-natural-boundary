import IsingBulk.Preferred22.FramePullback
import IsingBulk.Preferred22.BalancedPairGeometry
import IsingBulk.Preferred22.BumpCoarea

/-! Uniform actual source geometry for the exact frame calculus. The
occupancy matrix is proved invertible from the original periodic bumps. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_bump_matrix_uniform (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ τ₀ : ℝ, 0<τ₀ ∧ ∀ N : ℕ, 0<N → ∀ τ : ℝ, 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ, (preferredContourMatrix τ B.p B.m θ).det≠0 := by
  have hmp : Function.Periodic B.m (2*Real.pi) := by
    intro x
    change B.p (-(x+2*Real.pi))=B.p (-x)
    convert (B.periodic (-x-2*Real.pi)).symm using 1 <;> congr 1 <;> ring
  obtain ⟨Bp,hBp,hpjet⟩ := bump_finite_jets B.p B.smooth B.periodic 1
  obtain ⟨Bm,hBm,hmjet⟩ := bump_finite_jets B.m B.m_smooth hmp 1
  let C := max Bp Bm
  have hC : 0<C := hBp.trans_le (le_max_left _ _)
  have hdp (x : ℝ) : |deriv B.p x|≤C := by
    rw [←Real.norm_eq_abs,norm_deriv_eq_norm_fderiv]
    have hh : ‖fderiv ℝ B.p x‖≤Bp := by
      simpa only [norm_iteratedFDeriv_one] using hpjet 1 (by omega) x
    exact hh.trans (le_max_left _ _)
  have hdm (x : ℝ) : |deriv B.m x|≤C := by
    rw [←Real.norm_eq_abs,norm_deriv_eq_norm_fderiv]
    have hh : ‖fderiv ℝ B.m x‖≤Bm := by
      simpa only [norm_iteratedFDeriv_one] using hmjet 1 (by omega) x
    exact hh.trans (le_max_right _ _)
  refine ⟨1/(8*C),by positivity,?_⟩
  intro N hN τ hτ hτr θ
  have hs : 4*τ*C≤(1/2:ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0<8*C)).mp hτr.le
    nlinarith
  exact (preferredContourMatrix_inverse_bound hN τ C hτ hC.le hs B.p B.m θ
    (fun i => by rw [abs_of_nonneg (B.lower_bound _)]; exact B.upper_bound _)
    (fun i => by
      change |B.p (-(θ i))|≤1
      rw [abs_of_nonneg (B.lower_bound _)]; exact B.upper_bound _)
    (fun i => hdp (θ i)) (fun i => hdm (θ i))).1

/-- One enlarged physical angular window contains every complete right
source point strictly. The same matrix/parameter thresholds precede N. -/
theorem preferred_actual_frame_points (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ δ ε₀ τ₀ : ℝ, 0<δ ∧ δ<d.alpha ∧ 0<ε₀ ∧ 0<τ₀ ∧
      ∀ δB : ℝ, 0<δB → δB<B.delta → ∀ N : ℕ, 0<N →
      ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
      PreferredFramePoint τ δ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ ∧
        (∀ i, θ i∈Ioo (-Real.pi-δ) δ) := by
  let δ := (B.delta+d.alpha)/2
  have hδ : 0<δ := by dsimp [δ]; linarith [B.delta_pos,d.alpha_pos]
  have hδa : δ<d.alpha := by dsimp [δ]; linarith [B.delta_alpha,d.alpha_pos]
  have hBδ : B.delta<δ := by dsimp [δ]; linarith [B.delta_alpha,d.alpha_pos]
  obtain ⟨ε₀,hε₀,hmargin⟩ := preferred_radial_one_sided_margins d δ hδ hδa
  obtain ⟨τ₀,hτ₀,hM⟩ := preferred_bump_matrix_uniform d B
  refine ⟨δ,ε₀,τ₀,hδ,hδa,hε₀,hτ₀,?_⟩
  intro δB hδB hδBB N hN ε τ hε hεr hτ hτr θ hθ
  obtain ⟨hSr,hSi,hSδ⟩ := hmargin ε hε hεr
  have hθ' (i : Fin N) : θ i∈Ioo (-Real.pi-δ) δ := by
    have hh := hθ i
    constructor <;> linarith [B.branch_plateau]
  refine ⟨⟨hδ,hδa.trans d.alpha_lt,hSr,hSi,hSδ,
    fun i => ⟨(hθ' i).1.le,(hθ' i).2.le⟩,?_,hM N hN τ hτ hτr θ⟩,hθ'⟩
  intro i
  have hh := homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1) B.p B.m θ
    B.lower_bound (fun x => B.lower_bound (-x))
    (fun _ hx => B.p_zero_of_sin_nonpos hx) (fun _ hx => B.m_zero_of_sin_nonneg hx) i
  simpa only [complexW_homotopyRoot_eq] using hh

end
end IsingBulk.Preferred22
