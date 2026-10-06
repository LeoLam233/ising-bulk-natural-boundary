import IsingBulk.Tail.CompactHessianPerturbation
import IsingBulk.Tail.CompactPhaseBoundaryJet
import IsingBulk.Tail.CompactPhaseRegularity
import IsingBulk.Tail.CompactRightSectorGeometry

/-! Strict curvature of the ACTUAL coupled compact-right phase, with its
finite-dimensional scalar perturbation and all N-dependent summation costs. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem second_deriv_re (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    deriv (deriv (fun u => (F u).re)) t=(deriv (deriv F) t).re := by
  have he : deriv (fun u => (F u).re)=(fun u => (deriv F u).re) := by
    funext u
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hF.differentiable (by simp) u).hasDerivAt).deriv
  rw [he]
  have hd : ContDiff ℝ ∞ (deriv F) := by apply ContDiff.deriv'; simpa using hF
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd.differentiable (by simp) t).hasDerivAt).deriv

theorem second_deriv_finite_sum {N : ℕ} (F : Fin N → ℝ → ℂ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (t : ℝ) :
    deriv (deriv (fun u => ∑ i, F i u)) t=∑ i, deriv (deriv (F i)) t := by
  have he : deriv (fun u => ∑ i, F i u)=(fun u => ∑ i, deriv (F i) u) := by
    funext u
    exact deriv_fun_sum (fun i _ => (hF i).differentiable (by simp) u)
  rw [he]
  apply deriv_fun_sum
  intro i _
  have hd : ContDiff ℝ ∞ (deriv (F i)) := by apply ContDiff.deriv'; simpa using hF i
  exact hd.differentiable (by simp) t

theorem normalized_shape_norm_le {N : ℕ} (v : Fin N → ℝ) (hv : ∑ i, (v i)^2=1) : ‖v‖≤1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro i
  have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => sq_nonneg (v j)) (Finset.mem_univ i)
  rw [hv] at hh
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (v i),abs_nonneg (v i)]

theorem actual_compact_right_direction_curvature (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB)) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ (N : ℕ), 0<N → ∀ (eps τ lam : ℝ)
      (θ v : Fin N → ℝ) (t : ℝ), 0<eps → 0≤τ → τ≤1 → 0≤lam → lam≤1 →
      ‖v‖≤1 → 1≤(∑ i, (v i)^2) →
      (∀ i, (θ+t • v) i ∈ Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      eps+lam≤r →
      deriv (deriv (fun u => currentUnwrappedPhase f (Real.exp (-d.c₀*eps)) τ lam
        (radialParameter d.theta eps) (θ+u • v))) t ≤
        -(1+Real.cos d.thetaB)*min (δ/2) ((1+Real.cos d.thetaB)/2)+(N:ℝ)*C*(eps+lam) := by
  have hS : 0<1+Real.cos d.thetaB := by
    have hh := Real.strictAntiOn_cos ⟨d.thetaB_pos.le,d.thetaB_lt.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ d.thetaB_lt
    simp only [Real.cos_pi] at hh
    linarith
  let γ := min (δ/2) ((1+Real.cos d.thetaB)/2)
  have hγ : 0<γ := lt_min (half_pos hδ) (half_pos hS)
  have hmargin := right_sector_interval_uniform_margin d.thetaB_pos d.thetaB_lt hδ hδsmall
  have hstrict : ∀ a ∈ Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ),
      |1+Real.cos d.thetaB-Real.cos a|<1 := fun a ha => lt_of_le_of_lt (hmargin a ha) (by linarith)
  obtain ⟨r₀,C,hr₀,hC,hperturb⟩ := actual_compact_phase_second_perturbation d f hf.p_smooth hf.m_smooth
    hf.p_periodic hf.m_periodic (fun x => ⟨hf.p_nonneg x,hp1 x⟩) (fun x => ⟨hf.m_nonneg x,hf.m_le_one x⟩) hstrict
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨e,he,_,hmarginS⟩ := radialDampingMargin_linear hsint hcsmall
  refine ⟨min r₀ (e/2),C,lt_min hr₀ (half_pos he),hC,?_⟩
  intro N hN eps τ lam θ v t heps hτ hτ1 hlam hlam1 hnormv hv hθ hsmall
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
  have hpoint (i : Fin N) : (deriv (deriv (F i)) t).re ≤
      deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) ((θ+t • v) i)*(v i)^2+C*(eps+lam) := by
    have hh := hperturb N hN eps τ lam θ v i t heps.le hτ hτ1 hlam hlam1 hnormv (hθ i) hsmallR
    have heq : (fun u => compactPhaseModel (currentPhaseRayPoint f d.c₀ eps τ lam s θ v i u))=F i := by
      funext u
      exact (compactPhaseModel_source_identity f d.c₀ eps τ lam s (θ+u • v) i).symm
    rw [heq] at hh
    have hb := compactPhaseModel_boundary_second (1+Real.cos d.thetaB) ((θ+t • v) i) (v i) (hstrict _ (hθ i))
    change iteratedFDeriv ℝ 2 compactPhaseModel
      (((1+Real.cos d.thetaB:ℝ):ℂ),0,((θ+t • v) i:ℂ)) (fun _ => phaseRayBaseDirection v i)=_ at hb
    rw [hb] at hh
    have hre := (Complex.re_le_norm _).trans hh
    simp only [Complex.sub_re,Complex.ofReal_re] at hre
    linarith
  have hcurve : (fun u => currentUnwrappedPhase f r τ lam s (θ+u • v))=(fun u => (∑ i, F i u).re) := by
    funext u
    rw [currentUnwrappedPhase_eq_re]
    rfl
  rw [hcurve,second_deriv_re _ (ContDiff.sum (fun i _ => hF i)),second_deriv_finite_sum F hF,Complex.re_sum]
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
  have hcurv (i : Fin N) : deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) ((θ+t • v) i)≤
      -(1+Real.cos d.thetaB)*γ := compactRightPhase_uniform_curvature hS hγ _ (hmargin _ (hθ i))
  have hlim := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => mul_le_mul_of_nonneg_right (hcurv i) (sq_nonneg (v i)))
  rw [← Finset.mul_sum] at hlim
  have hlim' : (∑ i, deriv (deriv (compactRightPhase (1+Real.cos d.thetaB))) ((θ+t • v) i)*(v i)^2)≤
      -(1+Real.cos d.thetaB)*γ := hlim.trans (by
    have hh := mul_le_mul_of_nonpos_left hv (show -(1+Real.cos d.thetaB)*γ≤0 by nlinarith)
    simpa only [mul_one] using hh)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  change _≤-(1+Real.cos d.thetaB)*γ+(N:ℝ)*C*(eps+lam)
  nlinarith only [hsum,hlim']


theorem actual_compact_right_shape_curvature (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB)) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ (N : ℕ), 0<N → ∀ (eps τ lam : ℝ)
      (θ v : Fin N → ℝ) (t : ℝ), 0<eps → 0≤τ → τ≤1 → 0≤lam → lam≤1 →
      (∑ i, (v i)^2)=1 →
      (∀ i, (θ+t • v) i ∈ Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      eps+lam≤r →
      deriv (deriv (fun u => currentUnwrappedPhase f (Real.exp (-d.c₀*eps)) τ lam
        (radialParameter d.theta eps) (θ+u • v))) t ≤
        -(1+Real.cos d.thetaB)*min (δ/2) ((1+Real.cos d.thetaB)/2)+(N:ℝ)*C*(eps+lam) := by
  obtain ⟨r,C,hr,hC,hbound⟩ := actual_compact_right_direction_curvature d hcsmall f hf hp1 hδ hδsmall
  refine ⟨r,C,hr,hC,?_⟩
  intro N hN eps τ lam θ v t heps hτ hτ1 hlam hlam1 hv hθ hsmall
  exact hbound N hN eps τ lam θ v t heps hτ hτ1 hlam hlam1
    (normalized_shape_norm_le v hv) (by rw [hv]) hθ hsmall

end
end IsingBulk.Tail
