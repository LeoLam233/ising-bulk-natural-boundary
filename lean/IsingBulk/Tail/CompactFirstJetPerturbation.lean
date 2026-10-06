import IsingBulk.Tail.CompactHessianPerturbation
import IsingBulk.Tail.CompactPhaseBoundaryJet

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

lemma first_derivative_curve_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {p : ℝ → E} {t : ℝ} (q e : E)
    (hf : DifferentiableAt ℝ f (p t)) (hp : DifferentiableAt ℝ p t)
    {B delta U V : ℝ} (hB : 0≤B) (hd : 0≤delta)
    (hbase : ‖fderiv ℝ f q‖≤B)
    (hmotion : ‖iteratedFDeriv ℝ 1 f (p t)-iteratedFDeriv ℝ 1 f q‖≤delta)
    (hvelocity : ‖deriv p t‖≤U) (hdiff : ‖deriv p t-e‖≤V) :
    ‖deriv (fun x => f (p x)) t-fderiv ℝ f q e‖≤delta*U+B*V := by
  have hchain : deriv (fun x => f (p x)) t=(fderiv ℝ f (p t)) (deriv p t) := by
    simpa only [Function.comp_def] using (hf.hasFDerivAt.comp_hasDerivAt t hp.hasDerivAt).deriv
  rw [hchain]
  have h1 := (iteratedFDeriv ℝ 1 f (p t)-iteratedFDeriv ℝ 1 f q).le_opNorm (fun _ : Fin 1 => deriv p t)
  simp only [sub_apply,iteratedFDeriv_one_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin,pow_one] at h1
  have h1b := h1.trans (mul_le_mul hmotion hvelocity (norm_nonneg _) hd)
  have h2 := ((fderiv ℝ f q).le_opNorm (deriv p t-e)).trans
    (mul_le_mul hbase hdiff (norm_nonneg _) hB)
  have he : (fderiv ℝ f (p t)) (deriv p t)-(fderiv ℝ f q) e =
      ((fderiv ℝ f (p t)) (deriv p t)-(fderiv ℝ f q) (deriv p t))+
        (fderiv ℝ f q) (deriv p t-e) := by rw [map_sub]; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add h1b h2)

lemma compactPhaseModel_boundary_first (S theta w : ℝ) (h : |S-Real.cos theta|<1) :
    fderiv ℝ compactPhaseModel ((S:ℂ),0,(theta:ℂ)) ((0:ℂ),0,(w:ℂ)) =
      ((deriv (compactRightPhase S) theta * w : ℝ):ℂ) := by
  let p : ℝ → ℂ × ℂ × ℂ := fun t => ((S:ℂ),0,(t:ℂ))
  have hp : HasDerivAt p ((0:ℂ),0,1) theta :=
    (hasDerivAt_const theta (S:ℂ)).prodMk
      ((hasDerivAt_const theta (0:ℂ)).prodMk Complex.ofRealCLM.hasDerivAt)
  have hf := (compactPhaseModel_analyticAt S theta h).differentiableAt.restrictScalars ℝ
  have hc := (hf.hasFDerivAt.comp_hasDerivAt theta hp).deriv
  have hnear : ∀ᶠ t in 𝓝 theta, |S-Real.cos t|<1 :=
    (show Continuous (fun t : ℝ => |S-Real.cos t|) by fun_prop).continuousAt.eventually (gt_mem_nhds h)
  have he : (compactPhaseModel ∘ p) =ᶠ[𝓝 theta] (fun t => (compactRightPhase S t:ℂ)) := by
    filter_upwards [hnear] with t ht
    exact compactPhaseModel_limiting S t ht
  have hd := (compactRightPhase_hasDerivAt S theta h).ofReal_comp.deriv
  rw [← (compactRightPhase_hasDerivAt S theta h).deriv] at hd
  have hunit : fderiv ℝ compactPhaseModel ((S:ℂ),0,(theta:ℂ)) ((0:ℂ),0,1)=
      ((deriv (compactRightPhase S) theta:ℝ):ℂ) := hc.symm.trans (he.deriv_eq.trans hd)
  have hv : (((0:ℂ),0,(w:ℂ)) : ℂ × ℂ × ℂ)=w • (((0:ℂ),0,1) : ℂ × ℂ × ℂ) := by simp [Complex.real_smul]
  rw [hv,map_smul,hunit]
  simp [Complex.real_smul,mul_comm]

theorem actual_compact_phase_first_perturbation (d : LocalBranchData) (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hpper : Function.Periodic f.p (2*Real.pi)) (hmper : Function.Periodic f.m (2*Real.pi))
    (hpv : ∀ x, 0≤f.p x ∧ f.p x≤1) (hmv : ∀ x, 0≤f.m x ∧ f.m x≤1)
    {a b : ℝ} (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ|<1) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ (N : ℕ), 0<N → ∀ (eps τ lam : ℝ)
      (θ omegaVec : Fin N → ℝ) (i : Fin N) (t : ℝ),
      0≤eps → 0≤τ → τ≤1 → 0≤lam → lam≤1 → ‖omegaVec‖≤1 →
      (θ+t • omegaVec) i ∈ Icc a b → eps+lam≤r →
      ‖deriv (fun u => compactPhaseModel
          (currentPhaseRayPoint f d.c₀ eps τ lam (radialParameter d.theta eps) θ omegaVec i u)) t-
        fderiv ℝ compactPhaseModel
          (((1+Real.cos d.thetaB:ℝ):ℂ),0,((θ+t • omegaVec) i:ℂ))
          (phaseRayBaseDirection omegaVec i)‖≤C*(eps+lam) := by
  obtain ⟨r₀,B,hr₀,hB,hjets⟩ := compactPhaseModel_real_compact_tube hmargin 1
  obtain ⟨A,hA,hvelocity⟩ := currentPhaseRayPoint_velocity_bounds f hp hm hpper hmper
  let D := 5+d.c₀
  let U := 1+A
  let C := B*D*U+B*A
  have hD : 0<D := by dsimp [D]; positivity [d.c₀_pos]
  have hU : 1≤U := by dsimp [U]; linarith
  have hC : 0<C := by dsimp [C,U]; positivity
  refine ⟨r₀/D,C,div_pos hr₀ hD,hC,?_⟩
  intro N hN eps τ lam θ omegaVec i t heps hτ hτ1 hlam hlam1 homega hθ hsmall
  let x := θ+t • omegaVec
  let v := radialRayExponent f d.c₀ eps τ lam θ omegaVec i t
  let p := currentPhaseRayPoint f d.c₀ eps τ lam (radialParameter d.theta eps) θ omegaVec i
  let q : ℂ × ℂ × ℂ := (((1+Real.cos d.thetaB:ℝ):ℂ),0,(x i:ℂ))
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hP0 := occupancy_nonneg (fun l => (hpv (x l)).1)
  have hP1 := occupancy_le (fun l => (hpv (x l)).2)
  have hv : |v|≤d.c₀*eps+2*τ*lam := coupledRadialExponent_lambda_bound d.c₀_pos.le heps hτ hlam
    (hpv (x i)).1 (hpv (x i)).2 (hmv (x i)).1 (hmv (x i)).2
    (div_nonneg hP0 hn.le) ((div_le_one hn).mpr hP1)
  have hs := sourceS_radial_to_boundary d eps heps
  have htl : τ*lam≤lam := mul_le_of_le_one_left hlam hτ1
  have hmax : max ‖sourceS (radialParameter d.theta eps)-((1+Real.cos d.thetaB:ℝ):ℂ)‖ ‖(v:ℂ)‖≤D*(eps+lam) := by
    rw [max_le_iff,Complex.norm_real,Real.norm_eq_abs]
    dsimp [D]
    constructor <;> nlinarith [mul_nonneg d.c₀_pos.le heps,mul_nonneg d.c₀_pos.le hlam]
  have hsmall' : D*(eps+lam)≤r₀ := by
    have hh := (le_div_iff₀ hD).mp hsmall
    nlinarith
  obtain ⟨hanalytic,hjet⟩ := hjets (x i) hθ (sourceS (radialParameter d.theta eps)) (v:ℂ) (hmax.trans hsmall')
  have hzero : max ‖((1+Real.cos d.thetaB:ℝ):ℂ)-((1+Real.cos d.thetaB:ℝ):ℂ)‖ ‖(0:ℂ)‖≤r₀ := by simp; exact hr₀.le
  have hbase : ‖fderiv ℝ compactPhaseModel q‖≤B := by
    simpa only [norm_iteratedFDeriv_one,q] using
      ((hjets (x i) hθ ((1+Real.cos d.thetaB:ℝ):ℂ) 0 hzero).2 1 le_rfl).1
  have hmotion : ‖iteratedFDeriv ℝ 1 compactPhaseModel (p t)-iteratedFDeriv ℝ 1 compactPhaseModel q‖≤B*D*(eps+lam) := by
    have hh := (hjet 1 le_rfl).2.trans (mul_le_mul_of_nonneg_left hmax hB.le)
    simpa only [mul_assoc,p,currentPhaseRayPoint,q,v,x] using hh
  have hanalytic' : AnalyticAt ℂ compactPhaseModel (p t) := by
    simpa only [p,currentPhaseRayPoint,v,x] using hanalytic
  have hf : DifferentiableAt ℝ compactPhaseModel (p t) :=
    hanalytic'.differentiableAt.restrictScalars ℝ
  have hpoint : DifferentiableAt ℝ p t :=
    (currentPhaseRayPoint_smooth f hp hm d.c₀ eps τ lam (radialParameter d.theta eps) θ omegaVec i).differentiable (by simp) t
  obtain ⟨he,hu,hd,ha⟩ := hvelocity N hN d.c₀ eps τ lam (radialParameter d.theta eps) θ omegaVec i t hτ hτ1 hlam hlam1 homega
  have hresult := first_derivative_curve_perturbation q (phaseRayBaseDirection omegaVec i) hf hpoint
    hB.le (show 0≤B*D*(eps+lam) by positivity) hbase hmotion hu hd
  apply hresult.trans
  have hle : lam≤eps+lam := by linarith
  have hh := mul_le_mul_of_nonneg_left hle (show 0≤B*A by positivity)
  dsimp only [C]
  nlinarith only [hh]

end
end IsingBulk.Tail
