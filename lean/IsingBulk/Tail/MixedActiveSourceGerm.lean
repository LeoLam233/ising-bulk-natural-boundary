import IsingBulk.Tail.MixedGaussianAmplitudeJets
import IsingBulk.Tail.MixedActiveRestriction
import IsingBulk.Tail.MixedActiveVelocity
import IsingBulk.Tail.MixedSeparatedDomain

/-! Fixed-background active analytic models of the literal source density. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem mixedActivePairProduct_source {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedActivePairProduct J q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ) 0=
      canceledPairProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)) (deformedPoint f r τ lam θ) := by
  unfold mixedActivePairProduct
  simp_rw [mixedActiveCompletePair_source J q f hr τ lam s θ hbranch hW]
  simp only [canceledPairProduct,orderedIndexPairs,Finset.prod_filter,Finset.prod_product]

theorem mixedActiveRegularAmplitude_source {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedActiveRegularAmplitude J q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ) 0=
      ((coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))⁻¹+
        (coordinateProduct (deformedPoint f r τ lam θ))⁻¹)*
        canceledPairProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)) (deformedPoint f r τ lam θ)*
        ∏ i,mixedSourceOneBody J f r τ lam s θ i := by
  rw [mixedActiveRegularAmplitude,mixedActiveSmoothAmplitude_source J q f hr τ lam s θ hbranch hW,
    mixedActivePairProduct_source J q f hr τ lam s θ hbranch hW]
  ring

/-- The normalization, full coupled determinant and simple kernels are
literal. The regular amplitude is the one whose Gaussian jets were proved. -/
theorem mixed_pulledDensity_active_amplitude {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    pulledDensity f r τ lam s θ=
      (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
        (angularJacobian f τ lam θ).det*mixedHybridVolume J f r τ lam s θ*
        mixedActiveRegularAmplitude J q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
          (deformedPoint f r τ lam θ) 0/
        ((1-coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))*
          (1-coordinateProduct (deformedPoint f r τ lam θ))) := by
  rw [mixed_pulledDensity_factorization J f hr τ lam s θ hbranch (fun i _ => hW i),
    mixedActiveRegularAmplitude_source J q f hr τ lam s θ hbranch hW]
  unfold mixedSourceAmplitude
  dsimp only
  ring

theorem mixedActiveCompact_formula {N : ℕ} (F : ℂ → ℂ → ℂ) (s : ℂ)
    (y : Fin N → ℂ) (q i : Fin N) (u : MixedActiveSpace N) :
    mixedActiveCompact F s y q i u=F (s+u.1)
      (y i*Complex.exp (Complex.I*(if i=q then u.2.2 else 0))) := by
  unfold mixedActiveCompact
  rw [rotatingCompactCoefficient_formula]
  by_cases hi : i=q <;> simp [mixedActiveCompactCoordinate,hi]

theorem mixedActiveBranch_recenter {N : ℕ} (F : ℂ → ℂ → ℂ) (s t : ℂ)
    (φ ψ : Fin N → ℂ) (i : Fin N) (u : MixedActiveSpace N)
    (ht : t=s+u.1) (hφ : ψ i=φ i+u.2.1 i) :
    mixedActiveBranch F s φ i u=mixedActiveBranch F t ψ i 0 := by
  simp only [mixedActiveBranch,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,add_zero]
  rw [← ht,← hφ]

theorem mixedActiveCompact_recenter {N : ℕ} (F : ℂ → ℂ → ℂ) (s t : ℂ)
    (y z : Fin N → ℂ) (q i : Fin N) (u : MixedActiveSpace N)
    (ht : t=s+u.1) (hy : z i=y i*Complex.exp (Complex.I*(if i=q then u.2.2 else 0))) :
    mixedActiveCompact F s y q i u=mixedActiveCompact F t z q i 0 := by
  rw [mixedActiveCompact_formula,mixedActiveCompact_formula]
  simp only [Prod.fst_zero,Prod.snd_zero,ite_self,add_zero,mul_zero,Complex.exp_zero,mul_one]
  rw [← ht,← hy]

theorem mixedActiveCompletePair_recenter {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s t : ℂ) (φ ψ y z : Fin N → ℂ) (u : MixedActiveSpace N)
    (ht : t=s+u.1) (hφ : ∀ i∈J,ψ i=φ i+u.2.1 i)
    (hy : ∀ i∉J,z i=y i*Complex.exp (Complex.I*(if i=q then u.2.2 else 0))) (i j : Fin N) :
    mixedActiveCompletePair J q s φ y i j u=mixedActiveCompletePair J q t ψ z i j 0 := by
  unfold mixedActiveCompletePair
  split_ifs with hi hj hj
  · simp only [mixedActiveBranchPair,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,add_zero]
    rw [← ht,← hφ i hi,← hφ j hj]
  · rw [activeBranchCompactPair_formula,activeBranchCompactPair_formula]
    simp only [Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,ite_self,add_zero,mul_zero,Complex.exp_zero,mul_one]
    rw [← ht,← hφ i hi,← hy j hj]
  · rw [activeBranchCompactPair_formula,activeBranchCompactPair_formula]
    simp only [Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,ite_self,add_zero,mul_zero,Complex.exp_zero,mul_one]
    rw [← ht,← hφ j hj,← hy i hi]
  · rw [activeCompactPair_formula,activeCompactPair_formula]
    simp only [Prod.fst_zero,Prod.snd_zero,ite_self,add_zero,mul_zero,Complex.exp_zero,mul_one]
    rw [← ht,← hy i hi,← hy j hj]

theorem mixedActiveRegularAmplitude_recenter {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s t : ℂ) (φ ψ y z : Fin N → ℂ) (u : MixedActiveSpace N)
    (ht : t=s+u.1) (hφ : ∀ i∈J,ψ i=φ i+u.2.1 i)
    (hy : ∀ i∉J,z i=y i*Complex.exp (Complex.I*(if i=q then u.2.2 else 0))) :
    mixedActiveRegularAmplitude J q s φ y u=mixedActiveRegularAmplitude J q t ψ z 0 := by
  have hv (a : Fin 3) (i : Fin N) : mixedActiveAmplitudeVertex J q s φ y a i u=
      mixedActiveAmplitudeVertex J q t ψ z a i 0 := by
    unfold mixedActiveAmplitudeVertex
    by_cases hi : i∈J
    · simp only [hi,ite_true]
      exact mixedActiveBranch_recenter _ s t φ ψ i u ht (hφ i hi)
    · simp only [hi,ite_false]
      exact mixedActiveCompact_recenter _ s t y z q i u ht (hy i hi)
  unfold mixedActiveRegularAmplitude mixedActiveSmoothAmplitude mixedActivePairProduct
  simp_rw [hv,mixedActiveCompletePair_recenter J q s t φ ψ y z u ht hφ hy]

def mixedSourceDisplacement {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ)
    (t : ℂ) (x : Fin N → ℝ) : MixedActiveSpace N :=
  (t-s,((fun i => if i∈J then mixedContourPhase f r τ lam t (mixedFreeze (insert q J) background x) i-
      mixedContourPhase f r τ lam s background i else 0),
    (mixedFreeze (insert q J) background x q:ℂ)-(background q:ℂ)))

theorem mixed_frozen_compact_coordinate {N : ℕ} (J : Finset (Fin N)) (q i : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ)
    (t : ℂ) (x : Fin N → ℝ) (hi : i∉J)
    (hp : ∀ k∈insert q J,f.p (x k)=f.p (background k))
    (hm : ∀ k∈insert q J,f.m (x k)=f.m (background k)) :
    deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i=
      deformedPoint f r τ lam background i*Complex.exp (Complex.I*
        (if i=q then (mixedSourceDisplacement J q f r τ lam s background t x).2.2 else 0)) := by
  rw [mixedFreeze_contour_identity (insert q J) background x f r τ lam hp hm i]
  by_cases hiq : i=q
  · subst i
    simp [mixedSourceDisplacement]
  · simp [mixedFreeze,hi,hiq]

/-- A fixed-background analytic amplitude models the actual contour on
active slices. The source determinant is retained and is locally constant
only by the explicit p/m plateau data. -/
theorem mixed_pulledDensity_frozen_model {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ)
    (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ)
    (hp : ∀ k∈insert q J,f.p (x k)=f.p (background k))
    (hm : ∀ k∈insert q J,f.m (x k)=f.m (background k))
    (hp' : ∀ k∈insert q J,deriv f.p (x k)=deriv f.p (background k))
    (hm' : ∀ k∈insert q J,deriv f.m (x k)=deriv f.m (background k))
    (hbranch : ∀ i∈J,Real.sin (mixedFreeze (insert q J) background x i)<0)
    (hW : ∀ i,0<(sourceW t (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i)).im) :
    pulledDensity f r τ lam t (mixedFreeze (insert q J) background x)=
      (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
        (angularJacobian f τ lam background).det*
        mixedHybridVolume J f r τ lam t (mixedFreeze (insert q J) background x)*
        mixedActiveRegularAmplitude J q s (fun i => mixedContourPhase f r τ lam s background i)
          (deformedPoint f r τ lam background) (mixedSourceDisplacement J q f r τ lam s background t x)/
        ((1-coordinateProduct (fun i => globalRoot t (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i)))*
          (1-coordinateProduct (deformedPoint f r τ lam (mixedFreeze (insert q J) background x)))) := by
  have he := mixedActiveRegularAmplitude_recenter J q s t
    (fun i => mixedContourPhase f r τ lam s background i)
    (fun i => mixedContourPhase f r τ lam t (mixedFreeze (insert q J) background x) i)
    (deformedPoint f r τ lam background)
    (deformedPoint f r τ lam (mixedFreeze (insert q J) background x))
    (mixedSourceDisplacement J q f r τ lam s background t x)
    (by simp [mixedSourceDisplacement])
    (fun i hi => by simp [mixedSourceDisplacement,hi])
    (fun i hi => mixed_frozen_compact_coordinate J q i f r τ lam s background t x hi hp hm)
  rw [he,mixed_pulledDensity_active_amplitude J q f hr τ lam t _ hbranch hW,
    mixedFreeze_jacobian_identity (insert q J) background x f τ lam hp hm hp' hm']
  rfl

def mixedFrozenDensityModel {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ)
    (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
    (angularJacobian f τ lam background).det*
    mixedHybridVolume J f r τ lam t (mixedFreeze (insert q J) background x)*
    mixedActiveRegularAmplitude J q s (fun i => mixedContourPhase f r τ lam s background i)
      (deformedPoint f r τ lam background) (mixedSourceDisplacement J q f r τ lam s background t x)/
    ((1-coordinateProduct (fun i => globalRoot t (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i)))*
      (1-coordinateProduct (deformedPoint f r τ lam (mixedFreeze (insert q J) background x))))

/-- A joint source germ with frozen spectators. The analytic amplitude's
background is fixed throughout subsequent differentiation. -/
theorem mixed_pulledDensity_active_germ {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ)
    (background : Fin N → ℝ) (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,background)∈mixedSeparatedDomain J j q f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (background i)<0)
    (hp : ∀ i∈insert q J,f.p =ᶠ[𝓝 (background i)] (fun _ => f.p (background i)))
    (hm : ∀ i∈insert q J,f.m =ᶠ[𝓝 (background i)] (fun _ => f.m (background i))) :
    (fun p : ℂ × (Fin N → ℝ) => pulledDensity f r τ lam p.1 (mixedFreeze (insert q J) background p.2)) =ᶠ[𝓝 (s,background)]
      (fun p => mixedFrozenDensityModel J q f r τ lam s background p.1 p.2) := by
  let H := fun p : ℂ × (Fin N → ℝ) => (p.1,mixedFreeze (insert q J) background p.2)
  have hH : Continuous H := continuous_fst.prodMk ((mixedFreeze_continuous _ _).comp continuous_snd)
  have hΩnear : ∀ᶠ p in 𝓝 (s,background),H p∈mixedSeparatedDomain J j q f r τ lam := by
    apply hH.continuousAt.eventually
    apply (mixedSeparatedDomain_isOpen J j q f hr τ lam hp_smooth hm_smooth).mem_nhds
    simpa only [H,mixedFreeze_self] using hΩ
  have hbnear : ∀ᶠ x in 𝓝 background,∀ i∈J,Real.sin (mixedFreeze (insert q J) background x i)<0 := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    have hc : Continuous (fun x => Real.sin (mixedFreeze (insert q J) background x i)) :=
      Real.continuous_sin.comp ((continuous_apply i).comp (mixedFreeze_continuous _ _))
    exact (hc.continuousAt (x := background)).eventually_lt continuousAt_const
      (by simpa only [mixedFreeze_self] using hbranch i hi)
  have hsnd : Tendsto (fun p : ℂ × (Fin N → ℝ) => p.2) (𝓝 (s,background)) (𝓝 background) :=
    continuous_snd.continuousAt.tendsto
  have hpnear := hsnd.eventually (mixed_plateau_data_eventually (insert q J) background f.p hp)
  have hmnear := hsnd.eventually (mixed_plateau_data_eventually (insert q J) background f.m hm)
  have hbnear' := hsnd.eventually hbnear
  filter_upwards [hΩnear,hpnear,hmnear,hbnear'] with p hpΩ hpp hpm hpb
  exact mixed_pulledDensity_frozen_model J q f hr τ lam s background p.1 p.2
    (fun i hi => (hpp i hi).1) (fun i hi => (hpm i hi).1)
    (fun i hi => (hpp i hi).2) (fun i hi => (hpm i hi).2) hpb hpΩ.2.1

@[simp] theorem mixedSourceDisplacement_zero {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ) :
    mixedSourceDisplacement J q f r τ lam s background s background=0 := by
  ext i <;> simp [mixedSourceDisplacement]

theorem mixedActiveResidualData_recenter {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (hj : j∈J) (hq : q∉J) (s t : ℂ) (φ ψ y z : Fin N → ℂ) (u : MixedActiveSpace N)
    (ht : t=s+u.1) (hφ : ∀ i∈J,ψ i=φ i+u.2.1 i)
    (hy : ∀ i∉J,z i=y i*Complex.exp (Complex.I*(if i=q then u.2.2 else 0))) :
    mixedActiveResidualData J j q s φ y u=mixedActiveResidualData J j q t ψ z 0 := by
  unfold mixedActiveResidualData
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact mixedActiveBranch_recenter mixedInverseSlope s t φ ψ j u ht (hφ j hj)
  · exact mixedActiveCompact_recenter mixedRootSlope s t y z q q u ht (hy q hq)
  · change (∑ i∈J,mixedActiveBranch regularA s φ i u)/(N:ℂ)=
      (∑ i∈J,mixedActiveBranch regularA t ψ i 0)/(N:ℂ)
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact mixedActiveBranch_recenter _ s t φ ψ i u ht (hφ i hi)
  · change (∑ i∈Finset.univ.filter (fun i => i∉J),mixedActiveCompact mixedRootTau s y q i u)/(N:ℂ)=
      (∑ i∈Finset.univ.filter (fun i => i∉J),mixedActiveCompact mixedRootTau t z q i 0)/(N:ℂ)
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact mixedActiveCompact_recenter _ s t y z q i u ht (hy i (Finset.mem_filter.mp hi).2)

theorem mixedActiveAngularVelocity_recenter {N : ℕ} (J : Finset (Fin N)) (j q i : Fin N)
    (hj : j∈J) (hq : q∉J) (s t : ℂ) (φ ψ y z : Fin N → ℂ) (u : MixedActiveSpace N)
    (ht : t=s+u.1) (hφ : ∀ i∈J,ψ i=φ i+u.2.1 i)
    (hy : ∀ i∉J,z i=y i*Complex.exp (Complex.I*(if i=q then u.2.2 else 0))) :
    mixedActiveAngularVelocity J j q s φ y i u=mixedActiveAngularVelocity J j q t ψ z i 0 := by
  unfold mixedActiveAngularVelocity
  rw [mixedActiveResidualData_recenter J j q hj hq s t φ ψ y z u ht hφ hy,
    mixedActiveBranch_recenter mixedInverseSlope s t φ ψ j u ht (hφ j hj)]
  by_cases hi : i∈J
  · simp only [hi,ite_true]
    rw [mixedActiveBranch_recenter regularA s t φ ψ i u ht (hφ i hi)]
  · simp only [hi,ite_false]

/-- Pointwise matching of the complete source angular field to one fixed
analytic active model. Source arguments remain coupled in every coordinate. -/
theorem mixed_velocity_frozen_model {N : ℕ} (hN : 0<N) (J : Finset (Fin N)) (j q i : Fin N)
    (hj : j∈J) (hq : q∉J) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ)
    (hp : ∀ k∈insert q J,f.p (x k)=f.p (background k))
    (hm : ∀ k∈insert q J,f.m (x k)=f.m (background k))
    (hbranch : ∀ k∈J,Real.sin (mixedFreeze (insert q J) background x k)<0)
    (hΩ : (t,mixedFreeze (insert q J) background x)∈mixedSeparatedDomain J j q f r τ lam) :
    mixedContourVelocity J j q f r τ lam t (mixedFreeze (insert q J) background x) i=
      mixedActiveAngularVelocity J j q s (fun k => mixedContourPhase f r τ lam s background k)
        (deformedPoint f r τ lam background) i (mixedSourceDisplacement J q f r τ lam s background t x) := by
  have he := mixedActiveAngularVelocity_recenter J j q i hj hq s t
    (fun k => mixedContourPhase f r τ lam s background k)
    (fun k => mixedContourPhase f r τ lam t (mixedFreeze (insert q J) background x) k)
    (deformedPoint f r τ lam background)
    (deformedPoint f r τ lam (mixedFreeze (insert q J) background x))
    (mixedSourceDisplacement J q f r τ lam s background t x)
    (by simp [mixedSourceDisplacement])
    (fun k hk => by simp [mixedSourceDisplacement,hk])
    (fun k hk => mixed_frozen_compact_coordinate J q k f r τ lam s background t x hk hp hm)
  rw [he]
  symm
  apply mixedActiveAngularVelocity_zero_source hN J j q i f hr τ lam t _ hj hbranch hΩ.2.1
  · unfold mixedSourceSlope
    exact div_ne_zero (mul_ne_zero Complex.I_ne_zero (hΩ.2.2.1 j hj))
      (mul_ne_zero (by norm_num) (mixedSourcePhase_sin_ne (hΩ.2.1 j)))
  · exact hΩ.2.2.2.1

end
end IsingBulk.Tail
