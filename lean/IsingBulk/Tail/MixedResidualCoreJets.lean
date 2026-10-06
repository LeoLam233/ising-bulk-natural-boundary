import IsingBulk.Tail.MixedActualActiveJets
import IsingBulk.Tail.MixedBranchIdentification

namespace IsingBulk.Tail
noncomputable section
open Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1500000

/-- Local use of the library composition estimate; no dimension-dependent
compactness or derivative certificate is introduced. -/
theorem analytic_vector_composition_geometric_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (g : F → ℂ) (f : E → F) (x : E) (k : ℕ)
    (hg : AnalyticAt ℂ g (f x)) (hf : AnalyticAt ℂ f x)
    (C D : ℝ) (hC : ∀ i≤k,‖iteratedFDeriv ℂ i g (f x)‖≤C)
    (hD : ∀ i,1≤ i → i≤k → ‖iteratedFDeriv ℂ i f x‖≤D^i) :
    ‖iteratedFDeriv ℂ k (g ∘ f) x‖≤k.factorial*C*D^k := by
  let V := {z | AnalyticAt ℂ g z}
  have hV : IsOpen V := isOpen_analyticAt ℂ g
  have hfx : f x∈V := hg
  obtain ⟨U,hU,hopen,hx⟩ := _root_.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and (hf.continuousAt.preimage_mem_nhds (hV.mem_nhds hfx)))
  have hgu : ContDiffOn ℂ ω g V := fun z hz => hz.contDiffAt.contDiffWithinAt
  have hfu : ContDiffOn ℂ ω f U := fun y hy => (hU y hy).1.contDiffAt.contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_comp_le hgu hfu (n := k) (by simp)
    hV.uniqueDiffOn hopen.uniqueDiffOn (fun y hy => (hU y hy).2) hx
    (C := C) (D := D) (by simpa only [iteratedFDerivWithin_of_isOpen _ hV hfx] using hC)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ hopen hx] using hD)
  simpa only [iteratedFDerivWithin_of_isOpen _ hopen hx] using hb

theorem mixed_residual_core_pullback_uniform_jets (B : ℝ) (order : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E],
      ∀ (F : E → MixedResidualData) (x : E),AnalyticAt ℂ F x →
      (∀ k≤order,‖iteratedFDeriv ℂ k F x‖≤B) → (3/4:ℝ)≤‖1-(F x).2.1*(F x).1‖ →
      ∀ k≤order,‖iteratedFDeriv ℂ k (mixedResidualCore ∘ F) x‖≤C ∧
        ‖iteratedFDeriv ℂ k (mixedCompactCore ∘ F) x‖≤C := by
  obtain ⟨D,hD,hDb⟩ := mixed_residual_finite_jets B order
  let M := max 1 B
  have hM : 1≤M := le_max_left _ _
  have hM0 : 0<M := zero_lt_one.trans_le hM
  refine ⟨order.factorial*D*M^order,by positivity,?_⟩
  intro E _ _ F x hF hFj hgap k hk
  have hnorm : ‖F x‖≤B := by simpa using hFj 0 (Nat.zero_le _)
  have hv : F x∈mixedResidualCompact B := ⟨by simpa [Metric.mem_closedBall,dist_eq_norm] using hnorm,hgap⟩
  have hd : 1-(F x).2.1*(F x).1≠0 := norm_ne_zero_iff.mp (by
    have hh : (0:ℝ)<‖1-(F x).2.1*(F x).1‖ := lt_of_lt_of_le (by norm_num) hgap
    exact hh.ne')
  have hj : ∀ i,1≤ i → i≤k → ‖iteratedFDeriv ℂ i F x‖≤M^i := by
    intro i hi hik
    exact (hFj i (hik.trans hk)).trans ((le_max_right 1 B).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hM hi))
  have hbound : (k.factorial:ℝ)*D*M^k≤order.factorial*D*M^order := by
    gcongr
  constructor
  · exact (analytic_vector_composition_geometric_jets mixedResidualCore F x k
      (mixedResidualCore_analyticAt hd) hF D M (fun i hi => (hDb _ hv i (hi.trans hk)).1) hj).trans hbound
  · exact (analytic_vector_composition_geometric_jets mixedCompactCore F x k
      (mixedCompactCore_analyticAt hd) hF D M (fun i hi => (hDb _ hv i (hi.trans hk)).2) hj).trans hbound


theorem mixed_active_data_source_gap {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hsin : Real.sin (θ j)<0)
    (hW : 0<(IsingBulk.First.sourceW s (deformedPoint f r τ lam θ q)).im)
    (hsep : ‖mixedSourceSlope s (deformedPoint f r τ lam θ q)/
      mixedSourceSlope s (deformedPoint f r τ lam θ j)‖≤1/4) :
    let y := deformedPoint f r τ lam θ
    let φ := fun i => mixedSourcePhase s (y i)
    let v := mixedActiveResidualData J j q s φ y 0
    (3/4:ℝ)≤‖1-v.2.1*v.1‖ := by
  dsimp only
  have hβ := mixed_actual_inverseSlope f hr τ lam s θ j hsin
  have hb := mixedRootSlope_eq_source hW
  have he : (mixedActiveResidualData J j q s
      (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ) 0).2.1*
      (mixedActiveResidualData J j q s
      (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ) 0).1 =
      mixedSourceSlope s (deformedPoint f r τ lam θ q)/mixedSourceSlope s (deformedPoint f r τ lam θ j) := by
    simp only [mixedActiveResidualData,mixedActiveBranch,mixedActiveCompact,map_zero,
      rotatingCompactCoefficient_formula]
    change mixedRootSlope (s+0) (_*Complex.exp (Complex.I*0))*
      mixedInverseSlope (s+0) (mixedSourcePhase s (deformedPoint f r τ lam θ j)+0)=_
    simp only [add_zero,mul_zero,Complex.exp_zero,mul_one]
    rw [hb]
    change _*mixedInverseSlope s (mixedContourPhase f r τ lam s θ j)=_
    rw [hβ,div_eq_mul_inv]
  rw [he]
  have hh := norm_sub_norm_le (1:ℂ)
    (mixedSourceSlope s (deformedPoint f r τ lam θ q)/mixedSourceSlope s (deformedPoint f r τ lam θ j))
  simp only [norm_one] at hh
  linarith


theorem actual_residual_dimension_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) (x : E) (hF : AnalyticAt ℂ F x) (N k : ℕ) {C : ℝ}
    (hjet : ‖iteratedFDeriv ℂ k F x‖≤C) :
    ‖iteratedFDeriv ℂ k (fun u => (N:ℂ)*F u) x‖≤(N:ℝ)*C := by
  change ‖iteratedFDeriv ℂ k (fun u => (N:ℂ) • F u) x‖≤_
  rw [iteratedFDeriv_const_smul_apply' hF.contDiffAt,norm_smul,Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hjet (Nat.cast_nonneg N)

end
end IsingBulk.Tail
