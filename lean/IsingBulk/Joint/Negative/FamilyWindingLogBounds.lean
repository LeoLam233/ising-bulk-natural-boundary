import IsingBulk.Joint.Negative.FamilyHessianBounds
import IsingBulk.Joint.Negative.FamilyDensityScalar
import IsingBulk.Anisotropic.NegativeDominance.PhysicalWindingOverhead

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_log_norm_bound (f : ℂ × E→ℂ) {Q : Set E} (hQ : IsCompact Q)
    (hf : ∀eta∈Q,AnalyticAt ℂ f (0,eta)) (hfn : ∀eta∈Q,f (0,eta)≠0) :
    ∃r L : ℝ,0<r ∧ 0<L ∧ ∀eta∈Q,∀t : ℂ,‖t‖<r →
      f (t,eta)≠0 ∧ |Real.log ‖f (t,eta)‖|≤L := by
  have hcont : ContinuousOn (fun eta=>Real.log ‖f (0,eta)‖) Q := by
    intro eta heta
    exact (((hf eta heta).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).norm.log
        (norm_ne_zero_iff.mpr (hfn eta heta))).continuousWithinAt
  obtain ⟨C,hC⟩ := hQ.exists_bound_of_continuousOn hcont
  let L := max C 0+1
  have hL : 0<L := by dsimp [L]; linarith [le_max_right C 0]
  let U : Set (ℂ × E) := {q | AnalyticAt ℂ f q ∧ f q≠0 ∧ |Real.log ‖f q‖|<L}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    have hc := hq.1.continuousAt.norm.log (norm_ne_zero_iff.mpr hq.2.1)
    exact hq.1.eventually_analyticAt.and ((hq.1.continuousAt.eventually_ne hq.2.1).and
      (hc.abs.eventually_lt_const hq.2.2))
  obtain ⟨r,hr,htube⟩ := compact_product_tube hQ hU (by
    intro eta heta
    refine ⟨hf eta heta,hfn eta heta,?_⟩
    have hh := hC eta heta
    rw [Real.norm_eq_abs] at hh
    dsimp [L]
    linarith [le_max_left C 0])
  exact ⟨r,L,hr,hL,fun eta heta t ht=>
    ⟨(htube eta heta t ht).2.1,(htube eta heta t ht).2.2.le⟩⟩

theorem compact_family_winding_log_bounds (B rootB : ℂ × E→ℂ) (phi : ℝ)
    {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈Q,B (0,eta)≠0) (hroot : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (hrootn : ∀eta∈Q,rootB (0,eta)≠0) :
    ∃L : ℝ,0<L ∧ ∀ᶠN : ℕ in atTop,∀eta∈Q,
      B (tau N,eta)≠0 ∧ rootB (tau N,eta)≠0 ∧
      hessianFactor (B (tau N,eta)) (Real.cos phi) (Real.sin phi) N≠0 ∧
      |Real.log ‖B (tau N,eta)‖|≤L ∧ |Real.log ‖rootB (tau N,eta)‖|≤L ∧
      |Real.log ‖hessianFactor (B (tau N,eta)) (Real.cos phi) (Real.sin phi) N‖|≤L := by
  obtain ⟨r,Lb,hr,hLb,hb⟩ := compact_family_log_norm_bound B hQ hB hBn
  obtain ⟨s,Lr,hs,hLr,hrb⟩ := compact_family_log_norm_bound rootB hQ hroot hrootn
  obtain ⟨u,Lh,hu,hLh,hh⟩ := compact_family_log_norm_bound
    (fun q : ℂ × E=>centralHessian (familyMember B q.2) phi q.1) hQ
    (fun eta heta=>family_hessian_analyticAt B phi eta (hB eta heta))
    (fun _ _=>by simp only [centralHessian_zero,ne_eq,one_ne_zero,not_false_eq_true])
  have ht : ∀ᶠN : ℕ in atTop,‖(tau N:ℂ)‖<min r s := by
    simpa only [mem_ball,dist_zero_right] using
      tau_complex_tendsto_zero.eventually (ball_mem_nhds (0:ℂ) (lt_min hr hs))
  have hd : ∀ᶠN : ℕ in atTop,‖((Real.pi/(N:ℝ):ℝ):ℂ)‖<u := by
    simpa only [mem_ball,dist_zero_right] using
      winding_angle_complex_tendsto_zero.eventually (ball_mem_nhds (0:ℂ) hu)
  refine ⟨Lb+Lr+Lh,by positivity,?_⟩
  filter_upwards [ht,hd] with N ht hd eta heta
  have hb := hb eta heta _ (ht.trans_le (min_le_left _ _))
  have hrb := hrb eta heta _ (ht.trans_le (min_le_right _ _))
  have hh := hh eta heta _ hd
  rw [centralHessian_at_winding] at hh
  exact ⟨hb.1,hrb.1,hh.1,hb.2.trans (by linarith),hrb.2.trans (by linarith),hh.2.trans (by linarith)⟩

end
end IsingBulk.Joint.Negative
