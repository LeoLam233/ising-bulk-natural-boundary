import IsingBulk.HT.Lie.OnsiteModel
import IsingBulk.HT.Contour.OnsiteLieIntegration

/-! The analytic onsite model agrees with the literal coupled source on
active slices. Spectator occupancy is retained and is locally constant only
along the genuine branch plateau coordinates. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets IsingBulk.HT.Contour Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem onsiteActiveRegularAmplitude_recenter {N : ℕ}
    (J : Finset (Fin N)) (q : Fin N) (s t : ℂ) (φ ψ y z : Fin N → ℂ)
    (u : MixedActiveSpace N) (ht : t=s+u.1)
    (hφ : ∀ i∈J,ψ i=φ i+u.2.1 i)
    (hy : ∀ i∉J,z i=y i*Complex.exp (Complex.I*(if i=q then u.2.2 else 0))) :
    onsiteActiveRegularAmplitude J q s φ y u=onsiteActiveRegularAmplitude J q t ψ z 0 := by
  have hv (a : Fin 3) (i : Fin N) : mixedActiveAmplitudeVertex J q s φ y a i u=
      mixedActiveAmplitudeVertex J q t ψ z a i 0 := by
    unfold mixedActiveAmplitudeVertex
    by_cases hi : i∈J
    · simp only [hi,ite_true]
      exact mixedActiveBranch_recenter _ s t φ ψ i u ht (hφ i hi)
    · simp only [hi,ite_false]
      exact mixedActiveCompact_recenter _ s t y z q i u ht (hy i hi)
  unfold onsiteActiveRegularAmplitude onsiteActiveSmoothAmplitude mixedActivePairProduct
  simp_rw [hv,mixedActiveCompletePair_recenter J q s t φ ψ y z u ht hφ hy]

theorem onsite_source_frozen_model {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ)
    (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ)
    (hp : ∀ i∈J,f.p (x i)=f.p (background i))
    (hm : ∀ i∈J,f.m (x i)=f.m (background i))
    (hp' : ∀ i∈J,deriv f.p (x i)=deriv f.p (background i))
    (hm' : ∀ i∈J,deriv f.m (x i)=deriv f.m (background i))
    (hbranch : ∀ i∈J,Real.sin (mixedFreeze J background x i)<0)
    (hW : ∀ i,0<(sourceW t (deformedPoint f r τ lam (mixedFreeze J background x) i)).im) :
    onsitePulledDensity f r τ lam t (mixedFreeze J background x)=
      onsiteRegularModel J f r τ lam s
        (fun i => mixedContourPhase f r τ lam s background i)
        (fun u => mixedDensityNormalization f τ lam background*
          onsiteActiveRegularAmplitude J q s
            (fun i => mixedContourPhase f r τ lam s background i)
            (deformedPoint f r τ lam background) u) t (mixedFreeze J background x) := by
  let θ := mixedFreeze J background x
  let φ := fun i => mixedContourPhase f r τ lam s background i
  let u := onsiteDisplacement J f r τ lam s φ t θ
  have he := onsiteActiveRegularAmplitude_recenter J q s t φ
    (fun i => mixedContourPhase f r τ lam t θ i)
    (deformedPoint f r τ lam background) (deformedPoint f r τ lam θ) u
    (by dsimp [u,onsiteDisplacement,onsiteModelMap]; ring)
    (by intro i hi; dsimp [u,onsiteDisplacement,onsiteModelMap,mixedHybridMap]; simp [hi])
    (by
      intro i hi
      rw [mixedFreeze_contour_identity J background x f r τ lam hp hm i]
      simp [u,onsiteDisplacement,onsiteModelMap,mixedFreeze,hi,θ])
  rw [onsiteRegularModel,he]
  rw [onsiteActiveRegularAmplitude_source J q f hr τ lam t θ hbranch hW]
  rw [mixedFreeze_jacobian_identity J background x f τ lam hp hm hp' hm']
  unfold mixedDensityNormalization mixedContourPhase
  dsimp only [θ]
  ring

/-- A joint active source germ, with the actual normalization fixed only
by the exact plateau identity. -/
theorem onsite_source_active_germ {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ)
    (background : Fin N → ℝ) (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,background)∈onsiteLieDomain J f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (background i)<0)
    (hp : ∀ i∈J,f.p =ᶠ[𝓝 (background i)] fun _ => f.p (background i))
    (hm : ∀ i∈J,f.m =ᶠ[𝓝 (background i)] fun _ => f.m (background i)) :
    (fun p : ℂ × (Fin N → ℝ) => onsitePulledDensity f r τ lam p.1 (mixedFreeze J background p.2))
      =ᶠ[𝓝 (s,background)]
    (fun p => onsiteRegularModel J f r τ lam s
      (fun i => mixedContourPhase f r τ lam s background i)
      (fun u => mixedDensityNormalization f τ lam background*
        onsiteActiveRegularAmplitude J q s
          (fun i => mixedContourPhase f r τ lam s background i)
          (deformedPoint f r τ lam background) u) p.1 (mixedFreeze J background p.2)) := by
  let H := fun p : ℂ × (Fin N → ℝ) => (p.1,mixedFreeze J background p.2)
  have hH : Continuous H := continuous_fst.prodMk ((mixedFreeze_continuous J background).comp continuous_snd)
  have hΩnear : ∀ᶠ p in 𝓝 (s,background),H p∈onsiteLieDomain J f r τ lam := by
    apply hH.continuousAt.eventually
    apply (onsiteLieDomain_isOpen J f hr τ lam hp_smooth hm_smooth).mem_nhds
    simpa only [H,mixedFreeze_self] using hΩ
  have hbnear : ∀ᶠ x in 𝓝 background,∀ i∈J,Real.sin (mixedFreeze J background x i)<0 := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    have hc : Continuous (fun x => Real.sin (mixedFreeze J background x i)) :=
      Real.continuous_sin.comp ((continuous_apply i).comp (mixedFreeze_continuous _ _))
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hbranch i hi)
  have hsnd : Tendsto (fun p : ℂ × (Fin N → ℝ) => p.2) (𝓝 (s,background)) (𝓝 background) :=
    continuous_snd.continuousAt.tendsto
  filter_upwards [hΩnear,hsnd.eventually hbnear,
    hsnd.eventually (mixed_plateau_data_eventually J background f.p hp),
    hsnd.eventually (mixed_plateau_data_eventually J background f.m hm)] with p hpΩ hpb hpp hpm
  exact onsite_source_frozen_model J q f hr τ lam s background p.1 p.2
    (fun i hi => (hpp i hi).1) (fun i hi => (hpm i hi).1)
    (fun i hi => (hpp i hi).2) (fun i hi => (hpm i hi).2) hpb hpΩ.2.1

end
end IsingBulk.HT.Lie
