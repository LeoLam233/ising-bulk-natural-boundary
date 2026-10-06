import IsingBulk.Tail.MixedActiveScalarTransport

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem mixed_active_residuals_frozen_model {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (hj : j∈J) (hq : q∉J) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ)
    (hp : ∀ i∈insert q J,f.p (x i)=f.p (background i))
    (hm : ∀ i∈insert q J,f.m (x i)=f.m (background i)) :
    let θ := mixedFreeze (insert q J) background x
    let u := mixedSourceDisplacement J q f r τ lam s background t x
    let φ := fun i => mixedContourPhase f r τ lam s background i
    let ψ := fun i => mixedContourPhase f r τ lam t θ i
    let y := deformedPoint f r τ lam background
    let z := deformedPoint f r τ lam θ
    mixedActiveBranchResidual J j q s φ y u=mixedActiveBranchResidual J j q t ψ z 0 ∧
      mixedActiveCompactResidual J j q s φ y u=mixedActiveCompactResidual J j q t ψ z 0 := by
  have he := mixedActiveResidualData_recenter J j q hj hq s t
    (fun i => mixedContourPhase f r τ lam s background i)
    (fun i => mixedContourPhase f r τ lam t (mixedFreeze (insert q J) background x) i)
    (deformedPoint f r τ lam background) (deformedPoint f r τ lam (mixedFreeze (insert q J) background x))
    (mixedSourceDisplacement J q f r τ lam s background t x)
    (by simp [mixedSourceDisplacement]) (fun i hi => by simp [mixedSourceDisplacement,hi])
    (fun i hi => mixed_frozen_compact_coordinate J q i f r τ lam s background t x hi hp hm)
  dsimp only
  unfold mixedActiveBranchResidual mixedActiveCompactResidual
  rw [he]
  exact ⟨rfl,rfl⟩

/-- The active scalar transport formula holds near the background, with F
and every coefficient model fixed before any further differentiation. -/
theorem mixed_frozen_scalar_transport {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q : Fin N) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ)
    (hpval : ∀ i∈insert q J,f.p (x i)=f.p (background i))
    (hmval : ∀ i∈insert q J,f.m (x i)=f.m (background i))
    (hp : ∀ i,DifferentiableAt ℝ f.p (mixedFreeze (insert q J) background x i))
    (hm : ∀ i,DifferentiableAt ℝ f.m (mixedFreeze (insert q J) background x i))
    (hplateau : ∀ i∈insert q J,deriv f.p (mixedFreeze (insert q J) background x i)=0 ∧
      deriv f.m (mixedFreeze (insert q J) background x i)=0)
    (hbranch : ∀ i∈J,Real.sin (mixedFreeze (insert q J) background x i)<0)
    (hΩ : (t,mixedFreeze (insert q J) background x)∈mixedSeparatedDomain J j q f r τ lam)
    (F : MixedActiveSpace N → ℂ)
    (hF : DifferentiableAt ℂ F (mixedSourceDisplacement J q f r τ lam s background t x)) :
    let u := mixedSourceDisplacement J q f r τ lam s background t x
    let φ := fun i => mixedSourcePhase s (deformedPoint f r τ lam background i)
    let y := deformedPoint f r τ lam background
    mixedCoordinateTransport (fun z a => mixedContourVelocity J j q f r τ lam z
      (mixedFreeze (insert q J) background a))
      (fun z a => F (mixedSourceDisplacement J q f r τ lam s background z a)) t x =
    fderiv ℂ F u (mixedActiveParameterDirection N)+
      mixedActiveBranchResidual J j q s φ y u * fderiv ℂ F u (mixedActiveBranchDirection j)+
      mixedActiveCompactResidual J j q s φ y u * fderiv ℂ F u (mixedActiveCompactDirection N) := by
  let θ := mixedFreeze (insert q J) background x
  let u := mixedSourceDisplacement J q f r τ lam s background t x
  let L := fderiv ℂ F u
  have ht := mixedSourceDisplacement_parameter J q f r τ lam s background t x hΩ.1
    (fun i _ => hΩ.2.1 i)
  have hs : deriv (fun z => F (mixedSourceDisplacement J q f r τ lam s background z x)) t =
      L (mixedDisplacementParameterColumn J (fun i => mixedSourceTau t (deformedPoint f r τ lam θ i))) := by
    simpa only [Function.comp_def,L,u,θ] using (hF.hasFDerivAt.comp_hasDerivAt t ht).deriv
  have hx (k : Fin N) : coordDeriv (fun a => F (mixedSourceDisplacement J q f r τ lam s background t a)) x k =
      L (mixedDisplacementAngularColumn J q k (fun i => mixedSourceSlope t (deformedPoint f r τ lam θ i))) := by
    have hd := mixedSourceDisplacement_angular J q f hr τ lam s background t x k hp hm hplateau
      (fun i _ => hΩ.2.1 i)
    unfold coordDeriv
    simpa only [Function.comp_def,L,u,θ,ContinuousLinearMap.coe_restrictScalars'] using
      ((hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (x k) hd
        (by simp only [Function.update_eq_self])).deriv
  obtain ⟨hR,hQ⟩ := mixed_active_residuals_frozen_model J j q hj hq f r τ lam s background t x hpval hmval
  dsimp only
  unfold mixedCoordinateTransport
  rw [hs]
  simp_rw [hx,← smul_eq_mul,← map_smul]
  rw [← map_sum,← map_sub,mixed_actual_transport_column hN J j q hj hq f hr τ lam t θ hbranch hΩ]
  simp only [map_add,map_smul,smul_eq_mul,L]
  dsimp only [mixedContourPhase] at hR hQ
  rw [hR,hQ]

end
end IsingBulk.Tail
