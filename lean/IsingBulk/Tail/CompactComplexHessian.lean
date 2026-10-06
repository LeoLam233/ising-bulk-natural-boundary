import IsingBulk.Tail.CompactRightActualCurvature
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Full complex second-coordinate perturbation of the actual coupled phase. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem second_derivative_affine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) (x v : E) :
    deriv (deriv (fun t : ℝ => f (x+t • v))) 0=fderiv ℝ (fderiv ℝ f) x v v := by
  have hp : ContDiff ℝ ∞ (fun t : ℝ => x+t • v) := by fun_prop
  have hd : deriv (fun t : ℝ => x+t • v)=(fun _ => v) := by
    funext t
    simpa using (((hasDerivAt_id t).smul_const v).const_add x).deriv
  rw [second_derivative_comp_curve (hf.contDiffAt.of_le (by simp)) (hp.contDiffAt.of_le (by simp)),hd]
  simp [iteratedFDeriv_two_apply]

theorem actual_compact_complex_diagonal_hessian (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB)) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ N : ℕ, 0<N → ∀ eps τ lam : ℝ,
      0<eps → 0≤τ → τ≤1 → 0≤lam → lam≤1 → eps+lam≤r →
      ∀ θ v : Fin N → ℝ, ‖v‖≤1 →
      (∀ i, θ i∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      let G := currentComplexPhase (N := N) f (Real.exp (-d.c₀*eps)) τ lam (radialParameter d.theta eps)
      ‖fderiv ℝ (fderiv ℝ G) θ v v-
        ∑ i, ((deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) (θ i)*(v i)^2:ℝ):ℂ)‖≤
        (N:ℝ)*C*(eps+lam) := by
  have hS : 0<1+Real.cos d.thetaB := by
    have hh := Real.strictAntiOn_cos ⟨d.thetaB_pos.le,d.thetaB_lt.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ d.thetaB_lt
    simp only [Real.cos_pi] at hh
    linarith
  have hγ : 0<min (δ/2) ((1+Real.cos d.thetaB)/2) := lt_min (half_pos hδ) (half_pos hS)
  have hmargin := right_sector_interval_uniform_margin d.thetaB_pos d.thetaB_lt hδ hδsmall
  have hstrict : ∀ a∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ),
      |1+Real.cos d.thetaB-Real.cos a|<1 := fun a ha => lt_of_le_of_lt (hmargin a ha) (by linarith)
  obtain ⟨r₀,C,hr₀,hC,hperturb⟩ := actual_compact_phase_second_perturbation d f hf.p_smooth hf.m_smooth
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
  have hpoint (i : Fin N) : ‖deriv (deriv (F i)) 0-
      ((deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) (θ i)*(v i)^2:ℝ):ℂ)‖≤C*(eps+lam) := by
    have hh := hperturb N hN eps τ lam θ v i 0 heps.le hτ hτ1 hlam hlam1 hv (by simpa using hθ i) hsmallR
    have heq : (fun u => compactPhaseModel (currentPhaseRayPoint f d.c₀ eps τ lam s θ v i u))=F i := by
      funext u
      exact (compactPhaseModel_source_identity f d.c₀ eps τ lam s (θ+u • v) i).symm
    rw [heq] at hh
    have hb := compactPhaseModel_boundary_second (1+Real.cos d.thetaB) (θ i) (v i) (hstrict _ (hθ i))
    change iteratedFDeriv ℝ 2 compactPhaseModel
      (((1+Real.cos d.thetaB:ℝ):ℂ),0,((θ i):ℂ)) (fun _ => phaseRayBaseDirection v i)=_ at hb
    simpa only [zero_smul,add_zero,hb] using hh
  let G := currentComplexPhase (N := N) f r τ lam s
  have hG : ContDiff ℝ ∞ G := currentComplexPhase_contDiff hN f hr hr1 hτ hlam
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero hmarg
  have hsum : deriv (deriv (fun u : ℝ => G (θ+u • v))) 0=∑ i, deriv (deriv (F i)) 0 :=
    second_deriv_finite_sum F hF 0
  rw [second_derivative_affine hG θ v] at hsum
  change ‖fderiv ℝ (fderiv ℝ G) θ v v-_‖≤_
  rw [hsum,← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hh


/-- Polarization retains a dimension-free factor two. The diagonal comparison
is already for the full complex Hessian, not merely its real part. -/
theorem complex_hessian_polarization_bound {N : ℕ}
    (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℂ) (c : Fin N → ℝ)
    (hB : ∀ u v, B u v=B v u) {e : ℝ}
    (hdiag : ∀ v : Fin N → ℝ, ‖v‖≤1 → ‖B v v-∑ i, ((c i*(v i)^2:ℝ):ℂ)‖≤e)
    (u v : Fin N → ℝ) (hu : ‖u‖≤1) (hv : ‖v‖≤1) :
    ‖B u v-∑ i, ((c i*u i*v i:ℝ):ℂ)‖≤2*e := by
  let p : Fin N → ℝ := (1/2:ℝ) • (u+v)
  let m : Fin N → ℝ := (1/2:ℝ) • (u-v)
  have hp : ‖p‖≤1 := by
    dsimp [p]
    rw [norm_smul]
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh := norm_add_le u v
    nlinarith
  have hm : ‖m‖≤1 := by
    dsimp [m]
    rw [norm_smul]
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh := norm_sub_le u v
    nlinarith
  have hpolar : B u v=B p p-B m m := by
    dsimp [p,m]
    simp only [map_smul,map_add,map_sub,smul_apply,
      add_apply,sub_apply,hB v u]
    module
  have hbase : (∑ i, ((c i*(p i)^2:ℝ):ℂ))-(∑ i, ((c i*(m i)^2:ℝ):ℂ))=
      ∑ i, ((c i*u i*v i:ℝ):ℂ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [p,m]
    push_cast
    ring
  have heq : B u v-(∑ i, ((c i*u i*v i:ℝ):ℂ))=
      (B p p-∑ i, ((c i*(p i)^2:ℝ):ℂ))-(B m m-∑ i, ((c i*(m i)^2:ℝ):ℂ)) := by
    rw [hpolar,← hbase]
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith [hdiag p hp,hdiag m hm])


theorem actual_compact_complex_hessian_perturbation (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB)) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ N : ℕ, 0<N → ∀ eps τ lam : ℝ,
      0<eps → 0≤τ → τ≤1 → 0≤lam → lam≤1 → eps+lam≤r →
      ∀ θ u v : Fin N → ℝ, ‖u‖≤1 → ‖v‖≤1 →
      (∀ i, θ i∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      let G := currentComplexPhase (N := N) f (Real.exp (-d.c₀*eps)) τ lam (radialParameter d.theta eps)
      ‖fderiv ℝ (fderiv ℝ G) θ u v-
        ∑ i, ((deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) (θ i)*u i*v i:ℝ):ℂ)‖≤
        (N:ℝ)*C*(eps+lam) := by
  obtain ⟨r₀,C,hr₀,hC,hdiag⟩ := actual_compact_complex_diagonal_hessian d hcsmall f hf hp1 hδ hδsmall
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨e,he,_,hmarginS⟩ := radialDampingMargin_linear hsint hcsmall
  refine ⟨min r₀ (e/2),2*C,lt_min hr₀ (half_pos he),by positivity,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 hsmall θ u v hu hv hθ
  have hepsE : eps<e := by have hh := hsmall.trans (min_le_right _ _); linarith
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  have hr : 0<r := Real.exp_pos _
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hmarg : r⁻¹-r<(sourceS s).im := by
    have hh := radialRadius_parameter_margin heps (hmarginS eps heps hepsE)
    change r⁻¹-r+Real.sin d.theta*eps<_ at hh
    linarith [mul_pos hsint heps]
  let G := currentComplexPhase (N := N) f r τ lam s
  have hG : ContDiff ℝ ∞ G := currentComplexPhase_contDiff hN f hr hr1 hτ hlam
    hf.p_smooth hf.m_smooth hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero hmarg
  have hsym : ∀ u v, fderiv ℝ (fderiv ℝ G) θ u v=fderiv ℝ (fderiv ℝ G) θ v u :=
    hG.contDiffAt.isSymmSndFDerivAt (by simp)
  have hh := complex_hessian_polarization_bound (fderiv ℝ (fderiv ℝ G) θ)
    (fun i => deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) (θ i)) hsym
    (fun w hw => hdiag N hN eps τ lam heps hτ hτ1 hlam hlam1
      (hsmall.trans (min_le_left _ _)) θ w hw hθ) u v hu hv
  convert hh using 1; ring

end
end IsingBulk.Tail
