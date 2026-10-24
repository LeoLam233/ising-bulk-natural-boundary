import IsingBulk.Anisotropic.Geometry.LocallyFinite
import Mathlib.Analysis.Complex.AbsMax

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

/-- A small value inside a disk, below every boundary modulus, forces a zero.
This is the minimum-modulus form of zero persistence and also applies to multiple zeros. -/
theorem exists_zero_closedBall_of_boundary_bound {g : ℂ→ℂ} (hg : Differentiable ℂ g)
    {z : ℂ} {r m : ℝ} (hr : 0<r) (hm : 0<m) (hc : ‖g z‖<m)
    (hb : ∀w∈Metric.sphere z r,m≤‖g w‖) :
    ∃w∈Metric.closedBall z r,g w=0 := by
  by_contra hn
  push Not at hn
  have hi : DiffContOnCl ℂ (fun w => (g w)⁻¹) (Metric.ball z r) := by
    constructor
    · intro w hw
      exact ((hg w).inv (hn w (Metric.ball_subset_closedBall hw))).differentiableWithinAt
    · intro w hw
      rw [closure_ball z hr.ne'] at hw
      exact ((hg w).continuousAt.inv₀ (hn w hw)).continuousWithinAt
  have hb' : ∀w∈frontier (Metric.ball z r), ‖(g w)⁻¹‖≤m⁻¹ := by
    intro w hw
    rw [frontier_ball z hr.ne'] at hw
    rw [norm_inv]
    exact inv_anti₀ hm (hb w hw)
  have hc' := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hi hb'
    (subset_closure (Metric.mem_ball_self hr))
  rw [norm_inv] at hc'
  have hnz : 0<‖g z‖ := norm_pos_iff.mpr (hn z (Metric.mem_closedBall_self hr.le))
  have hle : m≤‖g z‖ := (inv_le_inv₀ hnz hm).mp hc'
  exact (not_le_of_gt hc) hle


/-- Joint continuity of a holomorphic family preserves at least one zero in a disk.
No simplicity of the original zero is required. -/
theorem eventually_exists_zero_closedBall {P : Type*} [TopologicalSpace P]
    {F : P → ℂ → ℂ} (hF : Continuous (fun pz : P × ℂ => F pz.1 pz.2))
    (hhol : ∀p,Differentiable ℂ (F p)) {p₀ : P} {z : ℂ} {r : ℝ}
    (hr : 0<r) (hz : F p₀ z=0) (hs : ∀w∈Metric.sphere z r,F p₀ w≠0) :
    ∀ᶠ p in 𝓝 p₀, ∃w∈Metric.closedBall z r,F p w=0 := by
  have hcont : Continuous (F p₀) := hF.comp (continuous_const.prodMk continuous_id)
  rcases (isCompact_sphere z r).exists_isMinOn (NormedSpace.sphere_nonempty.mpr hr.le)
    hcont.norm.continuousOn with ⟨v,hv,hmin⟩
  let m := ‖F p₀ v‖
  have hm : 0<m := norm_pos_iff.mpr (hs v hv)
  have herr : ∀ᶠ p in 𝓝 p₀, ∀w∈Metric.sphere z r, ‖F p₀ w-F p w‖<m/2 := by
    apply (isCompact_sphere z r).eventually_forall_of_forall_eventually
    intro w _
    have hc : Continuous (fun pw : P × ℂ => ‖F p₀ pw.2-F pw.1 pw.2‖) :=
      ((hcont.comp continuous_snd).sub hF).norm
    exact hc.continuousAt.eventually_lt_const (by simpa using half_pos hm)
  have hcenter : ∀ᶠ p in 𝓝 p₀, ‖F p z‖<m/2 := by
    have hc : Continuous (fun p => ‖F p z‖) := (hF.comp (continuous_id.prodMk continuous_const)).norm
    exact hc.continuousAt.eventually_lt_const (by simpa [hz] using half_pos hm)
  filter_upwards [herr,hcenter] with p hp hpc
  apply exists_zero_closedBall_of_boundary_bound (hhol p) hr (half_pos hm) hpc
  intro w hw
  have h1 : m≤‖F p₀ w‖ := hmin hw
  have h2 := norm_le_norm_sub_add (F p₀ w) (F p w)
  have h3 := hp w hw
  linarith

/-- Every zero of a nonzero entire member persists in every neighborhood under small parameter changes. -/
theorem eventually_exists_zero_mem_nhds {P : Type*} [TopologicalSpace P]
    {F : P → ℂ → ℂ} (hF : Continuous (fun pz : P × ℂ => F pz.1 pz.2))
    (hhol : ∀p,Differentiable ℂ (F p)) {p₀ : P} (hne : ∃w,F p₀ w≠0)
    {z : ℂ} (hz : F p₀ z=0) {N : Set ℂ} (hN : N∈𝓝 z) :
    ∀ᶠ p in 𝓝 p₀, ∃w∈N,F p w=0 := by
  have his := analytic_locally_nonzero (fun w => (hhol p₀).analyticAt w) hne z
  rw [nhdsWithin,Filter.eventually_inf_principal] at his
  rcases Metric.mem_nhds_iff.mp (Filter.inter_mem hN his) with ⟨R,hR,hsub⟩
  have hr : 0<R/2 := half_pos hR
  have hb : Metric.closedBall z (R/2)⊆N := by
    intro w hw
    exact (hsub (lt_of_le_of_lt hw (half_lt_self hR))).1
  have hs : ∀w∈Metric.sphere z (R/2),F p₀ w≠0 := by
    intro w hw
    have hd : dist w z=R/2 := hw
    apply (hsub (by change dist w z<R; rw [hd]; exact half_lt_self hR)).2
    intro he
    subst w
    simp at hd
    linarith
  filter_upwards [eventually_exists_zero_closedBall hF hhol hr hz hs] with p hp
  rcases hp with ⟨w,hw,hzero⟩
  exact ⟨w,hb hw,hzero⟩

end
end IsingBulk.Anisotropic
