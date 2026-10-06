import IsingBulk.Tail.MixedActiveTransportColumn

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Exact chain rule for the fixed-background analytic active model. All
spectator dependence on the complex parameter remains in F. -/
theorem mixed_active_scalar_transport {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q : Fin N) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hp : ∀ i,DifferentiableAt ℝ f.p (θ i)) (hm : ∀ i,DifferentiableAt ℝ f.m (θ i))
    (hplateau : ∀ i∈insert q J,deriv f.p (θ i)=0 ∧ deriv f.m (θ i)=0)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0) (hΩ : (s,θ)∈mixedSeparatedDomain J j q f r τ lam)
    (F : MixedActiveSpace N → ℂ) (hF : DifferentiableAt ℂ F 0) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam)
      (fun t x => F (mixedSourceDisplacement J q f r τ lam s θ t x)) s θ =
    fderiv ℂ F 0 (mixedActiveParameterDirection N)+
      mixedActiveBranchResidual J j q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
        (deformedPoint f r τ lam θ) 0 * fderiv ℂ F 0 (mixedActiveBranchDirection j)+
      mixedActiveCompactResidual J j q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
        (deformedPoint f r τ lam θ) 0 * fderiv ℂ F 0 (mixedActiveCompactDirection N) := by
  let y := deformedPoint f r τ lam θ
  let φ := fun i => mixedSourcePhase s (y i)
  let L := fderiv ℂ F 0
  have ht := mixedSourceDisplacement_parameter J q f r τ lam s θ s θ hΩ.1
    (by simpa only [mixedFreeze_self] using fun i (_ : i∈J) => hΩ.2.1 i)
  have hs : deriv (fun t => F (mixedSourceDisplacement J q f r τ lam s θ t θ)) s =
      L (mixedDisplacementParameterColumn J (fun i => mixedSourceTau s (y i))) := by
    simpa only [mixedFreeze_self,Function.comp_def,L,y] using
      (hF.hasFDerivAt.comp_hasDerivAt_of_eq s ht (mixedSourceDisplacement_zero J q f r τ lam s θ).symm).deriv
  have hx (k : Fin N) : coordDeriv (fun x => F (mixedSourceDisplacement J q f r τ lam s θ s x)) θ k =
      L (mixedDisplacementAngularColumn J q k (fun i => mixedSourceSlope s (y i))) := by
    have hd := mixedSourceDisplacement_angular J q f hr τ lam s θ s θ k
      (by simpa only [mixedFreeze_self] using hp)
      (by simpa only [mixedFreeze_self] using hm)
      (by simpa only [mixedFreeze_self] using hplateau)
      (by simpa only [mixedFreeze_self] using fun i (_ : i∈J) => hΩ.2.1 i)
    unfold coordDeriv
    simpa only [mixedFreeze_self,Function.update_eq_self,Function.comp_def,L,y,
      ContinuousLinearMap.coe_restrictScalars'] using
      ((hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (θ k) hd
        (by simp only [Function.update_eq_self,mixedSourceDisplacement_zero])).deriv
  unfold mixedCoordinateTransport
  rw [hs]
  simp_rw [hx,← smul_eq_mul,← map_smul]
  rw [← map_sum,← map_sub]
  rw [mixed_actual_transport_column hN J j q hj hq f hr τ lam s θ hbranch hΩ]
  simp only [map_add,map_smul,smul_eq_mul,L]

end
end IsingBulk.Tail
