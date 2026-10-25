import IsingBulk.Joint.FormFactors.LocalAnnulus

namespace IsingBulk.Joint.FormFactors
noncomputable section
open IsingBulk.Anisotropic.FormFactors Set Filter Metric
open scoped Topology

/-- A local uniform scalar bound on the literal inverse dispersion,
proved by compactness of the two circles and actual pole exclusion. -/
theorem local_inverse_dispersion_bound {r : ℝ} {z : Coupling}
    (h : ContourAnnulus z r) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ w in 𝓝 z, ∀ x y : ℂ, ‖x‖=r → ‖y‖=r →
      ‖(dispersion w x y)⁻¹‖ ≤ M := by
  let K : Set (ℂ × ℂ) := sphere (0:ℂ) r ×ˢ sphere (0:ℂ) r
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hp (p : ℂ × ℂ) (hp : p ∈ K) : p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ dispersion z p.1 p.2 ≠ 0 := by
    have hx : ‖p.1‖=r := by simpa using hp.1
    have hy : ‖p.2‖=r := by simpa using hp.2
    exact ⟨norm_ne_zero_iff.mp (hx.trans_ne h.1.ne'),norm_ne_zero_iff.mp (hy.trans_ne h.1.ne'),
      h.2.2 _ _ hx.ge (hx.le.trans h.2.1.le) hy.ge (hy.le.trans h.2.1.le)⟩
  have hc : ContinuousOn (fun p : ℂ × ℂ => (dispersion z p.1 p.2)⁻¹) K := by
    intro p hpk
    have hh := hp p hpk
    have hd := (dispersion_continuousAt hh.1 hh.2.1).inv₀ hh.2.2
    exact (hd.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc
  let L := max M 0+1
  have hL : 0 < L := by dsimp [L]; linarith [le_max_right M 0]
  refine ⟨L,hL,?_⟩
  have he : ∀ᶠ w in 𝓝 z, ∀ p ∈ K, ‖(dispersion w p.1 p.2)⁻¹‖ < L := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hpk
    have hh := hp p hpk
    apply (((dispersion_continuousAt hh.1 hh.2.1).inv₀ hh.2.2).norm).eventually_lt continuousAt_const
    exact (hM p hpk).trans_lt (by dsimp [L]; linarith [le_max_left M 0])
  filter_upwards [he] with w hw
  intro x y hx hy
  exact (hw (x,y) ⟨by simpa using hx,by simpa using hy⟩).le
end
end IsingBulk.Joint.FormFactors
