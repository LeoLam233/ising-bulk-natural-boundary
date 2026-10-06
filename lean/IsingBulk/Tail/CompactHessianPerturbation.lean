import IsingBulk.Tail.CompactPhaseCurve

/-! Actual coupled compact-right phase second-jet perturbation. Constants
precede particle number; all occupancy derivatives are retained. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology ContDiff
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actual_compact_phase_second_perturbation (d : LocalBranchData) (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hpper : Function.Periodic f.p (2*Real.pi)) (hmper : Function.Periodic f.m (2*Real.pi))
    (hpv : ∀ x, 0≤f.p x ∧ f.p x≤1) (hmv : ∀ x, 0≤f.m x ∧ f.m x≤1)
    {a b : ℝ} (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ|<1) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ (N : ℕ), 0<N → ∀ (eps τ lam : ℝ)
      (θ omegaVec : Fin N → ℝ) (i : Fin N) (t : ℝ),
      0≤eps → 0≤τ → τ≤1 → 0≤lam → lam≤1 → ‖omegaVec‖≤1 →
      (θ+t • omegaVec) i ∈ Icc a b → eps+lam≤r →
      ‖deriv (deriv (fun u => compactPhaseModel
          (currentPhaseRayPoint f d.c₀ eps τ lam (radialParameter d.theta eps) θ omegaVec i u))) t-
        iteratedFDeriv ℝ 2 compactPhaseModel
          (((1+Real.cos d.thetaB:ℝ):ℂ),0,((θ+t • omegaVec) i:ℂ))
          (fun _ => phaseRayBaseDirection omegaVec i)‖≤C*(eps+lam) := by
  obtain ⟨r₀,B,hr₀,hB,hjets⟩ := compactPhaseModel_real_compact_tube hmargin 2
  obtain ⟨A,hA,hvelocity⟩ := currentPhaseRayPoint_velocity_bounds f hp hm hpper hmper
  let D := 5+d.c₀
  let U := 1+A
  let C := B*D*U^2+2*B*U*A+B*A
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
  have hbase := (hjets (x i) hθ ((1+Real.cos d.thetaB:ℝ):ℂ) 0 hzero).2 2 le_rfl
  have hfirst : ‖fderiv ℝ compactPhaseModel (p t)‖≤B := by
    simpa only [norm_iteratedFDeriv_one,p,currentPhaseRayPoint,v,x] using (hjet 1 (by norm_num)).1
  have hmotion : ‖iteratedFDeriv ℝ 2 compactPhaseModel (p t)-iteratedFDeriv ℝ 2 compactPhaseModel q‖≤B*D*(eps+lam) := by
    have hh := (hjet 2 le_rfl).2.trans (mul_le_mul_of_nonneg_left hmax hB.le)
    simpa only [mul_assoc,p,currentPhaseRayPoint,q,v,x] using hh
  have hanalytic' : AnalyticAt ℂ compactPhaseModel (p t) := by
    simpa only [p,currentPhaseRayPoint,v,x] using hanalytic
  have hf : ContDiffAt ℝ 2 compactPhaseModel (p t) :=
    (hanalytic'.contDiffAt : ContDiffAt ℂ 2 compactPhaseModel (p t)).restrict_scalars ℝ
  have hpoint : ContDiffAt ℝ 2 p t :=
    ((currentPhaseRayPoint_smooth f hp hm d.c₀ eps τ lam (radialParameter d.theta eps) θ omegaVec i).of_le (by simp)).contDiffAt
  obtain ⟨he,hu,hd,ha⟩ := hvelocity N hN d.c₀ eps τ lam (radialParameter d.theta eps) θ omegaVec i t hτ hτ1 hlam hlam1 homega
  have hresult := second_derivative_curve_perturbation q (phaseRayBaseDirection omegaVec i) hf hpoint
    hB.le (show 0≤B*D*(eps+lam) by positivity) hU (show 0≤A*lam by positivity) (show 0≤A*lam by positivity)
    hfirst hbase.1 hmotion hu he hd ha
  apply hresult.trans
  have hle : lam≤eps+lam := by linarith
  have h₂ := mul_le_mul_of_nonneg_left hle (show 0≤2*B*U*A by dsimp [U]; positivity)
  have h₃ := mul_le_mul_of_nonneg_left hle (show 0≤B*A by positivity)
  dsimp only [C]
  nlinarith only [h₂,h₃]

end
end IsingBulk.Tail
