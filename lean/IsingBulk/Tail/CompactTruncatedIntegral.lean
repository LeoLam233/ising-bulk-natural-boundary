import IsingBulk.Tail.CompactGuardedWeights
import IsingBulk.Tail.CompactParameterLieIntegral
import IsingBulk.Tail.SmoothParameterWeightedIntegral
import IsingBulk.Tail.CompactSelectedWindow

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set Filter MeasureTheory Function
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000

def compactGuardedWeight {N : ℕ} (P : Finset (Fin N × Fin N)) (M : ℕ)
    (h : ℝ) (i j : Fin N) (w : (Fin N → ℝ) → ℂ) (θ : Fin N → ℝ) : ℂ :=
  w θ*(compactGuardedPairWeight P M h i j θ:ℂ)

theorem compactGuardedWeight_smooth {N : ℕ} (P : Finset (Fin N × Fin N)) (M : ℕ)
    {h : ℝ} (hh : 0 < h) {i j : Fin N} (hij : (i,j) ∈ P)
    (w : (Fin N → ℝ) → ℂ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (compactGuardedWeight P M h i j w) :=
  hw.mul (Complex.ofRealCLM.contDiff.comp (compactGuardedPairWeight_smooth P M hh hij))

theorem compactGuardedWeight_support {N : ℕ} (P : Finset (Fin N × Fin N)) (M : ℕ)
    {h : ℝ} (hh : 0 < h) (i j : Fin N) (w : (Fin N → ℝ) → ℂ) :
    tsupport (compactGuardedWeight P M h i j w) ⊆ tsupport w ∩ {θ | h/2 ≤ |θ i-θ j|} := by
  intro θ hθ
  exact ⟨tsupport_mul_subset_left hθ,compactGuardedPairWeight_support P M hh i j
    (tsupport_comp_subset (g := Complex.ofReal) (by simp) _ (tsupport_mul_subset_right hθ))⟩

theorem compact_weighted_density_derivatives_tendsto {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K)
    (w : ℕ → (Fin N → ℝ) → ℂ) (wlim : (Fin N → ℝ) → ℂ)
    (hw : ∀ k, AEStronglyMeasurable (w k) (volume.restrict K))
    (hwlim : AEStronglyMeasurable wlim (volume.restrict K))
    (hsupp : ∀ k, support (w k) ⊆ K) (hsupplim : support wlim ⊆ K)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ k, ∀ᵐ θ ∂volume.restrict K, ‖w k θ‖ ≤ B)
    (hblim : ∀ᵐ θ ∂volume.restrict K, ‖wlim θ‖ ≤ B)
    (hlim : ∀ᵐ θ ∂volume.restrict K, Tendsto (fun k => w k θ) atTop (𝓝 (wlim θ)))
    (j : ℕ) {s : ℂ} (hs : s ∈ dampingDomain r) :
    Tendsto (fun k => iteratedDeriv j (fun t => ∫ θ, w k θ*pulledDensity f r τ lam t θ) s)
      atTop (𝓝 (iteratedDeriv j (fun t => ∫ θ, wlim θ*pulledDensity f r τ lam t θ) s)) := by
  have he (v : (Fin N → ℝ) → ℂ) (hv : support v ⊆ K) :
      (fun t => ∫ θ, v θ*pulledDensity f r τ lam t θ)=
        (fun t => ∫ θ in K, v θ*pulledDensity f r τ lam t θ) := by
    funext t
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro θ hθ
    rw [notMem_support.mp (fun hn => hθ (hv hn)),zero_mul]
  simp_rw [he _ (hsupp _),he wlim hsupplim]
  exact smooth_parameter_bounded_weight_derivatives_tendsto hK (compactSourceDomain_isOpen N r)
    (dampingDomain_isOpen r) (pulledDensity f r τ lam)
    (compactSource_density_smooth hN f hf hr hr1 hτ hlam) (fun _ h => ⟨h.1,mem_univ _⟩)
    w wlim hw hwlim hB hb hblim hlim j hs

/-- The selected cutoff is removed in every actual parameter derivative,
at fixed positive damping. No flux or derivative identity is assumed. -/
theorem compact_guarded_integral_derivatives_tendsto {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (P : Finset (Fin (n+1) × Fin (n+1))) (M : ℕ) {i j : Fin (n+1)}
    (hij : (i,j) ∈ P) (hne : i ≠ j) (w : AngularSpace n → ℂ)
    (hw : ContDiff ℝ ∞ w) (hK : HasCompactSupport w) (k : ℕ)
    {s : ℂ} (hs : s ∈ dampingDomain r) :
    Tendsto (fun l => iteratedDeriv k (fun t => ∫ θ,
      compactGuardedWeight P M (allBranchTruncationScale l) i j w θ*pulledDensity f r τ lam t θ) s)
      atTop (𝓝 (iteratedDeriv k (fun t => ∫ θ,
        (w θ*(compactPairWeight P M i j θ:ℂ))*pulledDensity f r τ lam t θ) s)) := by
  let K := tsupport w
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hw.continuous.continuousOn
  have hb (θ : AngularSpace n) (hθ : θ ∈ K) : ‖w θ‖ ≤ max 0 C :=
    (hC θ hθ).trans (le_max_right _ _)
  have hg (l : ℕ) (θ : AngularSpace n) : ‖compactGuardedWeight P M (allBranchTruncationScale l) i j w θ‖ ≤ ‖w θ‖ := by
    have hrange := compactGuardedPairWeight_range P M (allBranchTruncationScale l) hij θ
    rw [compactGuardedWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrange.1]
    exact mul_le_of_le_one_right (norm_nonneg _) hrange.2
  have hl (θ : AngularSpace n) : ‖w θ*(compactPairWeight P M i j θ:ℂ)‖ ≤ ‖w θ‖ := by
    have hrange := compactPairWeight_range P M hij θ
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrange.1]
    exact mul_le_of_le_one_right (norm_nonneg _) hrange.2
  apply compact_weighted_density_derivatives_tendsto (Nat.succ_pos n) f hf hr hr1 hτ hlam hK
    (fun l => compactGuardedWeight P M (allBranchTruncationScale l) i j w)
    (fun θ => w θ*(compactPairWeight P M i j θ:ℂ))
    (fun l => (compactGuardedWeight_smooth P M (allBranchTruncationScale_pos l) hij w hw).continuous.aestronglyMeasurable)
    (hw.continuous.measurable.mul (Complex.measurable_ofReal.comp (compactPairWeight_measurable P M i j))).aestronglyMeasurable
    _ _ (le_max_left 0 C) _ _ _ k hs
  · intro l θ hθ
    exact subset_tsupport w (mul_ne_zero_iff.mp hθ).1
  · intro θ hθ
    exact subset_tsupport w (mul_ne_zero_iff.mp hθ).1
  · intro l
    filter_upwards [ae_restrict_mem hK.measurableSet] with θ hθ
    exact (hg l θ).trans (hb θ hθ)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with θ hθ
    exact (hl θ).trans (hb θ hθ)
  · filter_upwards [ae_restrict_of_ae (allBranchExterior_ae_selected_distinct i j hne)] with θ hθ
    apply tendsto_const_nhds.congr'
    filter_upwards [compactGuardedPairWeight_eventually P M i j θ hθ] with l hl
    simp only [compactGuardedWeight,hl]

theorem actual_compact_guarded_lie_integral (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0 ≤ D) (hβ : 0 < β) :
    ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, (n+1:ℕ) ≤ D*Real.sqrt H →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      ∀ P : Finset (Fin (n+1) × Fin (n+1)), ∀ M : ℕ, ∀ i j : Fin (n+1),
      (i,j) ∈ P → i ≠ j → ∀ h : ℝ, 0 < h → ∀ w : AngularSpace n → ℂ,
      ContDiff ℝ ∞ w → HasCompactSupport w →
      (∀ θ ∈ tsupport w, ∀ l, θ l ∈ Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      ∀ k : ℕ,
      let r := Real.exp (-d.c₀*Real.exp (-H))
      let s := radialParameter d.theta (Real.exp (-H))
      let A := fun t θ => compactGuardedWeight P M h i j w θ*pulledDensity f r τ lam t θ
      iteratedDeriv k (fun t => ∫ θ, A t θ) s=
        ∫ θ, ((lieStep (currentSelectedPairField f r τ lam i j))^[k] A) s θ := by
  obtain ⟨c,hc,hwindow⟩ := actual_compact_selected_window d hcsmall f hf hp1 hδ hδsmall hD hβ
  filter_upwards [hwindow] with H hwindowH
  intro n hND τ lam hτ hτ1 hlam hlamB P M i j hij hne h hh w hw hK hcube k
  let r := Real.exp (-d.c₀*Real.exp (-H))
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos,Real.exp_pos (-H)])
  let W := compactGuardedWeight P M h i j w
  have hW := compactGuardedWeight_smooth P M hh hij w hw
  have hWs := compactGuardedWeight_support P M hh i j w
  have hWK : IsCompact (tsupport W) := hK.of_isClosed_subset isClosed_closure (fun θ hθ => (hWs hθ).1)
  apply compact_parameter_lie_integral
    (compactSelectedDomain_isOpen (Nat.succ_pos n) f hf hr hr1 hτ hlam i j)
    _ _ (currentSelectedPairField_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam i j)
    ((ParameterSmoothOn.angular _ W hW).mul (fun p hp =>
      compactSource_density_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam p hp.1)) hWK
  · intro t θ hθ
    exact subset_tsupport W (mul_ne_zero_iff.mp hθ).1
  · intro θ hθ
    have hs := hWs hθ
    apply (hwindowH (n+1) (Nat.succ_pos n) hND τ lam hτ hτ1 hlam hlamB i j hne θ (hcube θ hs.1)).2
    exact sub_ne_zero.mp (abs_pos.mp ((half_pos hh).trans_le hs.2))

end
end IsingBulk.Tail
