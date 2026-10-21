import IsingBulk.HT.Contour.OnsiteVolumeIntegral
import IsingBulk.HT.Contour.OnsiteSectorPartition

/-! Integration of a supported actual onsite Lie descendant against the
proved full branch-volume L1 bound. Concrete Gaussian endpoints are supplied
separately, so this analytic wrapper does not assert any source estimate. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Lie Set Filter MeasureTheory
open scoped Topology BigOperators

theorem onsite_lie_integral_of_volume_bound {n : ℕ}
    (J : Finset (Fin (n+1))) (f : SelectorFunctions) (r τ lam : ℝ)
    (w : (Fin (n+1) → ℝ) → ℂ) {U : Set ℂ}
    (hID : SectorLieIntegralIdentity U (onsiteBranchField J f r τ lam)
      (fun s θ => w θ*onsitePulledDensity f r τ lam s θ))
    {s : ℂ} (hs : s∈U) (k : ℕ) {P M : ℝ} (hP : 0≤P)
    (hvolume : IntegrableOn (fun θ => ‖mixedHybridVolume J f r τ lam s θ‖)
      (angleBox (n+1) ∩ tsupport w))
    (hL1 : (∫ θ in angleBox (n+1),(tsupport w).indicator
      (fun θ => ‖mixedHybridVolume J f r τ lam s θ‖) θ)≤M)
    (hpoint : ∀ θ∈angleBox (n+1) ∩ tsupport w,
      ‖((lieStep (onsiteBranchField J f r τ lam))^[k]
        (fun z x => w x*onsitePulledDensity f r τ lam z x)) s θ‖≤
          P*‖mixedHybridVolume J f r τ lam s θ‖) :
    ‖iteratedDeriv k (fun z => ∫ θ in angleBox (n+1),w θ*onsitePulledDensity f r τ lam z θ) s‖≤P*M := by
  let v := (tsupport w).indicator (fun θ => ‖mixedHybridVolume J f r τ lam s θ‖)
  have hv : IntegrableOn v (angleBox (n+1)) := by
    apply (integrable_indicator_iff (isClosed_tsupport w).measurableSet).2
    unfold IntegrableOn
    rw [Measure.restrict_restrict (isClosed_tsupport w).measurableSet,Set.inter_comm]
    exact hvolume
  rw [hID.iteratedDeriv_eq k hs]
  apply (norm_integral_le_of_norm_le (hv.const_mul P) ?_).trans
    ((integral_const_mul P v).trans_le (mul_le_mul_of_nonneg_left hL1 hP))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  by_cases hw : θ∈tsupport w
  · simpa only [v,Set.indicator_of_mem hw] using hpoint θ ⟨hθ,hw⟩
  · rw [iterate_lieStep_zero_off_weight _ _ w k s θ hw]
    simp only [norm_zero,v,Set.indicator_of_notMem hw,mul_zero,le_refl]

/-- The actual named-current scalar is outside every parameter derivative.
This identity remains valid at tau=0; nonzero tau is used only to identify
its support with the real cutoff support. -/
theorem onsiteNamedSectorIntegral_const (N : ℕ) (f : SelectorFunctions)
    (r τ lam b inner : ℝ) (hi : 0< inner) (q : Fin N)
    (sigma : Fin N → Fin 3) (s : ℂ) :
    onsiteNamedSectorIntegral N f r τ lam b inner hi q sigma s=
      (-2*Complex.I*(τ:ℂ))*∫ θ in angleBox N,
        (namedSelectorDerivative f q θ*sectorAssignmentWeight b inner hi sigma θ:ℝ)*
          onsitePulledDensity f r τ lam s θ := by
  unfold onsiteNamedSectorIntegral onsiteNamedSectorWeight
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  ring

theorem onsiteNamedSectorIntegral_deriv_const (N : ℕ) (f : SelectorFunctions)
    (r τ lam b inner : ℝ) (hi : 0< inner) (q : Fin N)
    (sigma : Fin N → Fin 3) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (onsiteNamedSectorIntegral N f r τ lam b inner hi q sigma) s=
      (-2*Complex.I*(τ:ℂ))*iteratedDeriv k (fun z => ∫ θ in angleBox N,
        (namedSelectorDerivative f q θ*sectorAssignmentWeight b inner hi sigma θ:ℝ)*
          onsitePulledDensity f r τ lam z θ) s := by
  have he := funext (onsiteNamedSectorIntegral_const N f r τ lam b inner hi q sigma)
  rw [he,iteratedDeriv_const_mul_field]

end
end IsingBulk.HT.Contour
