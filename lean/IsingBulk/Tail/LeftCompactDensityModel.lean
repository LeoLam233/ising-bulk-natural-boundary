import IsingBulk.Tail.LeftSectorReciprocalJets
import IsingBulk.Tail.MixedActiveSourceGerm
import IsingBulk.Tail.MixedSourceNormalization
import IsingBulk.Tail.MicrocoreParameterSlice
import IsingBulk.Tail.MixedKernelRadialBudget

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem leftFrozenZ_empty_parameter {N : ℕ} (q : Fin N) (s t : ℂ) (y : Fin N → ℂ) :
    leftFrozenZ ∅ q s y (t-s,0)=coordinateProduct (fun i => selectedContinuedRoot t (y i)) := by
  unfold leftFrozenZ coordinateProduct
  apply Finset.prod_congr rfl
  intro i _
  simp [leftFrozenRootFamily,rotatingCompactRoot_formula]

theorem compact_pulledDensity_parameter_germ {N : ℕ} (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hs : s≠0) (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    (fun t => pulledDensity f r τ lam t θ) =ᶠ[𝓝 s]
      (fun t => (mixedDensityNormalization f τ lam θ*
        (1-coordinateProduct (deformedPoint f r τ lam θ))⁻¹)*
        (mixedActiveRegularAmplitude ∅ q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
          (deformedPoint f r τ lam θ) (t-s,0)*
          (1-leftFrozenZ ∅ q s (deformedPoint f r τ lam θ) (t-s,0))⁻¹)) := by
  have hn : ∀ᶠ t in 𝓝 s,∀ i,0<(sourceW t (deformedPoint f r τ lam θ i)).im := by
    apply Filter.eventually_all.mpr
    intro i
    have hcW : ContinuousAt (fun t : ℂ => sourceW t (deformedPoint f r τ lam θ i)) s :=
      (continuousAt_id.add (continuousAt_id.inv₀ hs)).sub continuousAt_const
    have hc : ContinuousAt (fun t : ℂ => (sourceW t (deformedPoint f r τ lam θ i)).im) s :=
      Complex.continuous_im.continuousAt.comp hcW
    exact continuousAt_const.eventually_lt hc (hW i)
  filter_upwards [hn] with t ht
  have ha := mixedActiveRegularAmplitude_recenter (∅ : Finset (Fin N)) q s t
    (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
    (fun i => mixedSourcePhase t (deformedPoint f r τ lam θ i))
    (deformedPoint f r τ lam θ) (deformedPoint f r τ lam θ) (t-s,0)
    (by simp) (by simp) (by simp)
  rw [ha,leftFrozenZ_empty_parameter]
  simp_rw [show ∀ i,selectedContinuedRoot t (deformedPoint f r τ lam θ i)=
    globalRoot t (deformedPoint f r τ lam θ i) from fun i => continuedRoot_eq_interiorRoot (ht i)]
  rw [mixed_pulledDensity_active_amplitude ∅ q f hr τ lam t θ (by simp) ht]
  simp only [mixedHybridVolume,Finset.prod_empty,mul_one,mixedDensityNormalization,
    div_eq_mul_inv,mul_inv_rev]
  ring

/-- On all-compact sectors the regular amplitude and separated Z factor
may be differentiated directly. The Y kernel is constant in the parameter. -/
theorem compact_pulledDensity_parameter_jet_bound {N : ℕ} (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hs : s≠0) (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (order k : ℕ) (hk : k≤order) {A B : ℝ}
    (hA : JetBound (mixedActiveRegularAmplitude ∅ q s
      (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i)) (deformedPoint f r τ lam θ)) 0 order A)
    (hB : JetBound (fun u : ℂ × ℂ => (1-leftFrozenZ ∅ q s (deformedPoint f r τ lam θ) u)⁻¹) 0 order B) :
    ‖iteratedDeriv k (fun t => pulledDensity f r τ lam t θ) s‖≤
      ‖mixedDensityNormalization f τ lam θ‖*
        ‖(1-coordinateProduct (deformedPoint f r τ lam θ))⁻¹‖*(2^order*A*B) := by
  have hAs := jetBound_parameter_slice _ (0:ℂ) 0 order A hA
  have hBs := jetBound_parameter_slice _ (0:ℂ) (0:ℂ) order B hB
  have hb := (hAs.mul hBs).bound k hk
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hb
  rw [(compact_pulledDensity_parameter_germ q f hr τ lam s θ hs hW).iteratedDeriv_eq k]
  rw [iteratedDeriv_const_mul_field]
  have hshift : (fun t => mixedActiveRegularAmplitude ∅ q s
      (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i)) (deformedPoint f r τ lam θ) (t-s,0)*
      (1-leftFrozenZ ∅ q s (deformedPoint f r τ lam θ) (t-s,0))⁻¹)=
      (fun t => (fun u : ℂ => mixedActiveRegularAmplitude ∅ q s
        (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i)) (deformedPoint f r τ lam θ) (u,0)*
        (1-leftFrozenZ ∅ q s (deformedPoint f r τ lam θ) (u,0))⁻¹) (t-s)) := rfl
  rw [hshift,iteratedDeriv_comp_sub_const k
    (fun u : ℂ => mixedActiveRegularAmplitude ∅ q s
      (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i)) (deformedPoint f r τ lam θ) (u,0)*
      (1-leftFrozenZ ∅ q s (deformedPoint f r τ lam θ) (u,0))⁻¹) s]
  simp only [sub_self,norm_mul]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem leftFrozenZ_empty_reciprocal_analytic {N : ℕ} (hN : 0<N) (q : Fin N)
    (s : ℂ) (y : Fin N → ℂ) (hs : s≠0) (hy : ∀ i,y i≠0)
    (hW : ∀ i,0<(sourceW s (y i)).im) :
    AnalyticAt ℂ (fun u : ℂ × ℂ => (1-leftFrozenZ ∅ q s y u)⁻¹) 0 := by
  have hR (i : Fin N) : AnalyticAt ℂ (leftFrozenRootFamily ∅ q s y i) 0 := by
    rw [leftFrozenRootFamily_compact ∅ q s y i (by simp)]
    exact rotatingCompactRoot_analyticAt ⟨hs,hy i,Or.inl (Or.inl (hW i))⟩ _
  have hz : 1-leftFrozenZ ∅ q s y 0≠0 := by
    have he : leftFrozenZ ∅ q s y 0=coordinateProduct (fun i => globalRoot s (y i)) := by
      simp only [leftFrozenZ,leftFrozenRootFamily_zero,coordinateProduct]
      apply Finset.prod_congr rfl
      intro i _
      exact continuedRoot_eq_interiorRoot (hW i)
    rw [he]
    exact one_sub_coordinateProduct_ne_zero hN (fun i => interiorRoot_norm_lt_one (hW i))
  exact (analyticAt_const.sub (Finset.analyticAt_fun_prod _ (fun i _ => hR i))).inv hz

theorem compact_density_gaussian_budget {N order : ℕ} (hN : 1≤N)
    {L H C B κ Y A : ℝ} (hL : 0≤L) (hH : 0≤H) (hC : 0≤C) (_hB : 0≤B) (hY : 0≤Y)
    (hA : A≤L^N*(H^N*Y*(2^order*(C^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2))*(B*(N:ℝ)^order)))) :
    A≤(L*H*C*max 1 (2^order*B))^N*(N:ℝ)^(4*order)*Real.exp (-κ*(N:ℝ)^2)*Y := by
  have hK := mixed_constant_le_exponential ((2:ℝ)^order*B) hN
  calc
    _ ≤ _ := hA
    _ = (L*H*C)^N*(2^order*B)*(N:ℝ)^(4*order)*Real.exp (-κ*(N:ℝ)^2)*Y := by
      simp only [mul_pow,show 4*order=3*order+order by omega,pow_add]
      ring
    _ ≤ (L*H*C)^N*(max 1 (2^order*B))^N*(N:ℝ)^(4*order)*Real.exp (-κ*(N:ℝ)^2)*Y := by gcongr
    _ = _ := by simp only [mul_pow]

theorem compact_weighted_density_gaussian_bound {N : ℕ} (hN : 1≤N) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hs : s≠0) (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (order k : ℕ) (hk : k≤order) {C B H L κ : ℝ} (w : ℂ)
    (hC : 0≤C) (hB : 0≤B) (hH : 0≤H) (hL : 0≤L)
    (hA : JetBound (mixedActiveRegularAmplitude ∅ q s
      (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i)) (deformedPoint f r τ lam θ)) 0 order
      (C^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2)))
    (hR : JetBound (fun u : ℂ × ℂ => (1-leftFrozenZ ∅ q s (deformedPoint f r τ lam θ) u)⁻¹) 0 order
      (B*(N:ℝ)^order))
    (hNorm : ‖mixedDensityNormalization f τ lam θ‖≤H^N) (hw : ‖w‖≤L^N) :
    ‖w*iteratedDeriv k (fun t => pulledDensity f r τ lam t θ) s‖≤
      (L*H*C*max 1 (2^order*B))^N*(N:ℝ)^(4*order)*Real.exp (-κ*(N:ℝ)^2)*
        ‖(1-coordinateProduct (deformedPoint f r τ lam θ))⁻¹‖ := by
  apply compact_density_gaussian_budget hN hL hH hC hB (norm_nonneg _)
  rw [norm_mul]
  have hb := compact_pulledDensity_parameter_jet_bound q f hr τ lam s θ hs hW order k hk hA hR
  calc
    _ ≤ L^N*(‖mixedDensityNormalization f τ lam θ‖*
        ‖(1-coordinateProduct (deformedPoint f r τ lam θ))⁻¹‖*
        (2^order*(C^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2))*(B*(N:ℝ)^order))) :=
      mul_le_mul hw hb (norm_nonneg _) (pow_nonneg hL N)
    _ ≤ _ := by gcongr

end
end IsingBulk.Tail
