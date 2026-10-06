import IsingBulk.Tail.CompactComplexHessian
import IsingBulk.Tail.CompactFirstJetPerturbation

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem actual_compact_complex_first_perturbation (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB)) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ N : ℕ, 0<N → ∀ eps τ lam : ℝ,
      0<eps → 0≤τ → τ≤1 → 0≤lam → lam≤1 → eps+lam≤r →
      ∀ θ v : Fin N → ℝ, ‖v‖≤1 →
      (∀ i, θ i∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      let G := currentComplexPhase (N := N) f (Real.exp (-d.c₀*eps)) τ lam (radialParameter d.theta eps)
      ‖fderiv ℝ G θ v-
        ∑ i, ((deriv (compactRightPhase (1+Real.cos d.thetaB)) (θ i)*v i:ℝ):ℂ)‖≤
        (N:ℝ)*C*(eps+lam) := by
  have hS : 0<1+Real.cos d.thetaB := by
    have hh := Real.strictAntiOn_cos ⟨d.thetaB_pos.le,d.thetaB_lt.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ d.thetaB_lt
    simp only [Real.cos_pi] at hh
    linarith
  have hγ : 0<min (δ/2) ((1+Real.cos d.thetaB)/2) := lt_min (half_pos hδ) (half_pos hS)
  have hmargin := right_sector_interval_uniform_margin d.thetaB_pos d.thetaB_lt hδ hδsmall
  have hstrict : ∀ a∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ),
      |1+Real.cos d.thetaB-Real.cos a|<1 := fun a ha => lt_of_le_of_lt (hmargin a ha) (by linarith)
  obtain ⟨r₀,C,hr₀,hC,hperturb⟩ := actual_compact_phase_first_perturbation d f hf.p_smooth hf.m_smooth
    hf.p_periodic hf.m_periodic (fun x => ⟨hf.p_nonneg x,hp1 x⟩) (fun x => ⟨hf.m_nonneg x,hf.m_le_one x⟩) hstrict
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨e,he,_,hmarginS⟩ := radialDampingMargin_linear hsint hcsmall
  refine ⟨min r₀ (e/2),C,lt_min hr₀ (half_pos he),hC,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 hsmall θ v hv hθ
  have hepsE : eps<e := by have hh := hsmall.trans (min_le_right _ _); linarith
  have hsmallR := hsmall.trans (min_le_left _ _)
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  have hr : 0<r := Real.exp_pos _
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hmarg : r⁻¹-r<(sourceS s).im := by
    have hh := radialRadius_parameter_margin heps (hmarginS eps heps hepsE)
    change r⁻¹-r+Real.sin d.theta*eps<_ at hh
    linarith [mul_pos hsint heps]
  let F : Fin N → ℝ → ℂ := fun i u => continuedPhase (sourceW s (deformedPoint f r τ lam (θ+u • v) i))
  have hF (i : Fin N) : ContDiff ℝ ∞ (F i) :=
    (currentPhase_coordinate_contDiff hN f hr hr1 hτ hlam hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg
      hf.p_zero hf.m_zero hmarg i).comp (show ContDiff ℝ ∞ (fun u : ℝ => θ+u • v) by fun_prop)
  have hpoint (i : Fin N) : ‖deriv (F i) 0-
      ((deriv (compactRightPhase (1+Real.cos d.thetaB)) (θ i)*v i:ℝ):ℂ)‖≤C*(eps+lam) := by
    have hh := hperturb N hN eps τ lam θ v i 0 heps.le hτ hτ1 hlam hlam1 hv (by simpa using hθ i) hsmallR
    have heq : (fun u => compactPhaseModel (currentPhaseRayPoint f d.c₀ eps τ lam s θ v i u))=F i := by
      funext u
      exact (compactPhaseModel_source_identity f d.c₀ eps τ lam s (θ+u • v) i).symm
    rw [heq] at hh
    have hb := compactPhaseModel_boundary_first (1+Real.cos d.thetaB) (θ i) (v i) (hstrict _ (hθ i))
    change fderiv ℝ compactPhaseModel
      (((1+Real.cos d.thetaB:ℝ):ℂ),0,((θ i):ℂ)) (phaseRayBaseDirection v i)=_ at hb
    simpa only [zero_smul,add_zero,hb] using hh
  let G := currentComplexPhase (N := N) f r τ lam s
  have hG : ContDiff ℝ ∞ G := currentComplexPhase_contDiff hN f hr hr1 hτ hlam
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero hmarg
  have hsum : deriv (fun u : ℝ => G (θ+u • v)) 0=∑ i, deriv (F i) 0 :=
    deriv_fun_sum (fun i _ => (hF i).differentiable (by simp) 0)
  have hG' : HasFDerivAt G (fderiv ℝ G θ) (θ+(0:ℝ) • v) := by
    simpa using (hG.differentiable (by simp) θ).hasFDerivAt
  have hd : deriv (fun u : ℝ => G (θ+u • v)) 0=fderiv ℝ G θ v := by
    exact (hG'.comp_hasDerivAt (0:ℝ) (affine_angular_ray_hasDerivAt θ v 0)).deriv
  rw [hd] at hsum
  change ‖fderiv ℝ G θ v-_‖≤_
  rw [hsum,← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hh


end
end IsingBulk.Tail
