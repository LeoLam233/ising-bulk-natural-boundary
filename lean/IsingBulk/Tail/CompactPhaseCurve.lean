import IsingBulk.Tail.CompactRetractionCurve
import IsingBulk.Tail.CompactRealPhaseJets

/-! Exact real derivatives of the actual scalar-model input along a coupled
angular ray. No angular holomorphic extension is introduced. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped ContDiff
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem radialRayExponent_smooth {N : ℕ} (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (c₀ eps τ lam : ℝ) (θ omegaVec : Fin N → ℝ) (i : Fin N) :
    ContDiff ℝ ∞ (radialRayExponent f c₀ eps τ lam θ omegaVec i) := by
  unfold radialRayExponent coupledRadialExponent occupancy
  fun_prop

def currentPhaseRayPoint {N : ℕ} (f : SelectorFunctions) (c₀ eps τ lam : ℝ)
    (s : ℂ) (θ omegaVec : Fin N → ℝ) (i : Fin N) (t : ℝ) : ℂ × ℂ × ℂ :=
  (sourceS s,(radialRayExponent f c₀ eps τ lam θ omegaVec i t:ℂ),((θ+t • omegaVec) i:ℂ))

def phaseRayBaseDirection {N : ℕ} (omegaVec : Fin N → ℝ) (i : Fin N) : ℂ × ℂ × ℂ :=
  (0,0,(omegaVec i:ℂ))

theorem currentPhaseRayPoint_smooth {N : ℕ} (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (c₀ eps τ lam : ℝ) (s : ℂ) (θ omegaVec : Fin N → ℝ) (i : Fin N) :
    ContDiff ℝ ∞ (currentPhaseRayPoint f c₀ eps τ lam s θ omegaVec i) := by
  have hv := radialRayExponent_smooth f hp hm c₀ eps τ lam θ omegaVec i
  have hvC : ContDiff ℝ ∞ (fun t => (radialRayExponent f c₀ eps τ lam θ omegaVec i t:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hv
  have haC : ContDiff ℝ ∞ (fun t : ℝ => ((θ+t • omegaVec) i:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ∞ (fun t : ℝ => (θ+t • omegaVec) i) by fun_prop)
  exact contDiff_const.prodMk (hvC.prodMk haC)

theorem currentPhaseRayPoint_deriv {N : ℕ} (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (c₀ eps τ lam : ℝ) (s : ℂ) (θ omegaVec : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    deriv (currentPhaseRayPoint f c₀ eps τ lam s θ omegaVec i) t=
      (0,((deriv (radialRayExponent f c₀ eps τ lam θ omegaVec i) t:ℝ):ℂ),(omegaVec i:ℂ)) := by
  have hv := (radialRayExponent_smooth f hp hm c₀ eps τ lam θ omegaVec i).differentiable (by simp) t
  have hv' := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hv.hasDerivAt
  have ha : HasDerivAt (fun u : ℝ => ((θ+u • omegaVec) i:ℂ)) (omegaVec i:ℂ) t := by
    have hh : HasDerivAt (fun u : ℝ => (θ+u • omegaVec) i) (omegaVec i) t := by
      simpa using ((hasDerivAt_id t).mul_const (omegaVec i)).const_add (θ i)
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hh
  exact ((hasDerivAt_const t (sourceS s)).prodMk (hv'.prodMk ha)).deriv

theorem currentPhaseRayPoint_second_deriv {N : ℕ} (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (c₀ eps τ lam : ℝ) (s : ℂ) (θ omegaVec : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    deriv (deriv (currentPhaseRayPoint f c₀ eps τ lam s θ omegaVec i)) t=
      (0,((deriv (deriv (radialRayExponent f c₀ eps τ lam θ omegaVec i)) t:ℝ):ℂ),0) := by
  have he := funext (currentPhaseRayPoint_deriv f hp hm c₀ eps τ lam s θ omegaVec i)
  rw [he]
  have hv : ContDiff ℝ 1 (deriv (radialRayExponent f c₀ eps τ lam θ omegaVec i)) := by
    apply ContDiff.deriv'
    exact (radialRayExponent_smooth f hp hm c₀ eps τ lam θ omegaVec i).of_le (by simp)
  have hv' := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hv.differentiable (by norm_num) t).hasDerivAt
  exact ((hasDerivAt_const t (0:ℂ)).prodMk (hv'.prodMk (hasDerivAt_const t (omegaVec i:ℂ)))).deriv

theorem currentPhaseRayPoint_velocity_bounds (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hpper : Function.Periodic f.p (2*Real.pi)) (hmper : Function.Periodic f.m (2*Real.pi)) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ), 0<N → ∀ (c₀ eps τ lam : ℝ) (s : ℂ)
      (θ omegaVec : Fin N → ℝ) (i : Fin N) (t : ℝ), 0≤τ → τ≤1 → 0≤lam → lam≤1 → ‖omegaVec‖≤1 →
      ‖phaseRayBaseDirection omegaVec i‖≤1 ∧
      ‖deriv (currentPhaseRayPoint f c₀ eps τ lam s θ omegaVec i) t‖≤1+C ∧
      ‖deriv (currentPhaseRayPoint f c₀ eps τ lam s θ omegaVec i) t-phaseRayBaseDirection omegaVec i‖≤C*lam ∧
      ‖deriv (deriv (currentPhaseRayPoint f c₀ eps τ lam s θ omegaVec i)) t‖≤C*lam := by
  obtain ⟨C,hC,hbound⟩ := retraction_ray_derivative_bounds f hp hm hpper hmper
  refine ⟨C,hC,?_⟩
  intro N hN c₀ eps τ lam s θ omegaVec i t hτ hτ1 hlam hlam1 homega
  obtain ⟨hv,ha⟩ := hbound N hN c₀ eps τ lam θ omegaVec i t hτ hlam homega
  have hcLam : C*τ*lam≤C*lam := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hC.le hτ1) hlam
  have hc1 : C*lam≤C := mul_le_of_le_one_right hC.le hlam1
  have homegai : |omegaVec i|≤1 := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm omegaVec i).trans homega
  rw [currentPhaseRayPoint_deriv f hp hm,currentPhaseRayPoint_second_deriv f hp hm]
  dsimp [phaseRayBaseDirection]
  simp only [sub_zero,sub_self,norm_zero,Complex.norm_real,Real.norm_eq_abs]
  refine ⟨?_,?_,?_,?_⟩
  · exact max_le (by norm_num) (max_le (by norm_num) homegai)
  · exact max_le (by positivity) (max_le (by linarith [hv.trans hcLam]) (by linarith))
  · exact max_le (by positivity) (max_le (hv.trans hcLam) (by positivity))
  · exact max_le (by positivity) (max_le (ha.trans hcLam) (by positivity))

end
end IsingBulk.Tail
