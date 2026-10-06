import IsingBulk.Tail.ActualCompactGuardedValues
import IsingBulk.Tail.CompactSourceKernelIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Quantitative bound for every actual parameter derivative of a rationally
weighted compact source integral. The guard has been removed by its proved
derivative limit; its radius does not occur in this estimate. -/
theorem actual_compact_pair_integral_bound (d₀ : LocalBranchData)
    (hcsmall : d₀.c₀ < Real.sin d₀.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {δ τ D β : ℝ} (hδ : 0 < δ)
    (hδsmall : δ < 2*(1-Real.cos d₀.thetaB)) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hD : 0 ≤ D) (hβ : 0 < β) (J : ℕ) :
    ∃ K G Q : ℝ, 0 < K ∧ 1 ≤ G ∧ 0 < Q ∧ ∀ᶠ H : ℝ in atTop,
      ∀ n : ℕ, (n+1:ℕ) ≤ D*Real.sqrt H →
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      ∀ P : Finset (Fin (n+1) × Fin (n+1)), ∀ M : ℕ, 0 < M → J ≤ M →
      ∀ i j : Fin (n+1), (i,j) ∈ P → i ≠ j →
      let R := rightSectorRadius d₀.thetaB δ
      let S := Icc (fun _ : Fin (n+1) => -R) (fun _ => R)
      let r := Real.exp (-d₀.c₀*Real.exp (-H))
      let s := radialParameter d₀.theta (Real.exp (-H))
      ∀ w : AngularSpace n → ℂ, ContDiff ℝ ∞ w → tsupport w ⊆ S →
      ∀ Cnear Cfar ρ : ℝ, 0 ≤ Cnear → 0 ≤ Cfar → 0 < ρ → ρ ≤ 1 → ∀ m : ℕ,
      (∀ θ ∈ S, 0 < compactAllowedDiameter P θ → compactAllowedDiameter P θ ≤ 1 →
        RealScaledJetBound (fun p : ℂ × AngularSpace n => w p.2*compactRegularDensity f r τ lam p.1 p.2)
          (s,θ) J (compactAllowedDiameter P θ) Cnear (2*(J:ℤ)+(m+1:ℕ))) →
      (∀ θ ∈ S, RealScaledJetBound
        (fun p : ℂ × AngularSpace n => w p.2*compactRegularDensity f r τ lam p.1 p.2) (s,θ) J 1 Cfar 0) →
      ‖iteratedDeriv J (fun z => ∫ θ, (w θ*(compactPairWeight P M i j θ:ℂ))*pulledDensity f r τ lam z θ) s‖ ≤
        (4*compactGuardedLieCost (n+1) M J K G (max 1 (2*R)))*
          (Cnear*ρ^m+Cfar*ρ^(-(2*M+1:ℕ):ℤ))*(Q^(n+1)*(n+1:ℕ)^4*(H+1)^2) := by
  obtain ⟨K,G,hK,hG,hvalues⟩ := actual_compact_guarded_regular_values d₀ hcsmall f hf hp1 hδ hδsmall hD hβ J
  obtain ⟨a,Q,ha,hQ,hkernel⟩ := actual_compact_right_source_kernel_budget d₀ hcsmall f hf hp1
    hτ hτ1 hδ hδsmall hD hβ
  obtain ⟨c,hc,hwindow⟩ := actual_compact_selected_window d₀ hcsmall f hf hp1 hδ hδsmall hD hβ
  have hid := actual_compact_guarded_lie_integral d₀ hcsmall f hf hp1 hδ hδsmall hD hβ
  have ht : Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall (fun H => Real.exp_pos (-H))⟩
  refine ⟨K,G,Q,hK,hG,hQ,?_⟩
  filter_upwards [hvalues,hkernel,hwindow,hid,ht.eventually (radial_source_eventually_damping d₀ hcsmall)]
    with H hvH hkH hwH hiH hdom
  intro n hND lam hlam hlamB P M hM hJM i j hij hne R S r s w hw hsupp
    Cnear Cfar ρ hCn hCf hρ hρ1 m hnear hfar
  have hr : 0 < r := hdom.1
  have hr1 : r < 1 := hdom.2.1
  have hs : s ∈ dampingDomain r := hdom.2.2
  have hwK : HasCompactSupport w := isCompact_Icc.of_isClosed_subset isClosed_closure hsupp
  let T := max 1 (2*R)
  let cost := compactGuardedLieCost (n+1) M J K G T
  have hcost : 0 ≤ cost := compactGuardedLieCost_nonneg _ _ _ hK.le (by linarith) (by exact (zero_le_one.trans (le_max_left _ _)))
  let L := compactRadialPhaseKernel (N := n+1) d₀ f τ lam H a
  have hker := hkH (n+1) (Nat.succ_pos n) hND lam hlam hlamB
  have hA : ParameterSmoothOn (compactSourceDomain (n+1) r)
      (fun z x => w x*compactRegularDensity f r τ lam z x) :=
    (ParameterSmoothOn.angular _ w hw).mul (compactRegularDensity_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam)
  have hbound (h : ℝ) (hh : 0 < h) :
      ‖iteratedDeriv J (fun z => ∫ θ, compactGuardedWeight P M h i j w θ*pulledDensity f r τ lam z θ) s‖ ≤
        (4*cost)*(Cnear*ρ^m+Cfar*ρ^(-(2*M+1:ℕ):ℤ))*(Q^(n+1)*(n+1:ℕ)^4*(H+1)^2) := by
    let A := fun z x => compactGuardedWeight P M h i j w x*pulledDensity f r τ lam z x
    let V := currentSelectedPairField f r τ lam i j
    let F := fun θ => ((lieStep V)^[J] A) s θ
    have he := hiH n hND τ lam hτ hτ1 hlam hlamB P M i j hij hne h hh w hw hwK
      (fun θ hθ l => ⟨(hsupp hθ).1 l,(hsupp hθ).2 l⟩) J
    change iteratedDeriv J (fun z => ∫ θ, A z θ) s=∫ θ, F θ at he
    rw [he]
    have hFs : tsupport F ⊆ S := iterate_lieStep_support_subset V A isOpen_univ isClosed_Icc
      (fun _ _ θ hθ => hsupp (subset_tsupport w (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hθ).1).1))
      J s (mem_univ s)
    have heS : (∫ θ, F θ)=∫ θ in S, F θ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro θ hθ
      exact image_eq_zero_of_notMem_tsupport (fun hn => hθ (hFs hn))
    rw [heS]
    have hb := compact_allowed_near_far_integral (m := m) (q := 2*M) P L F hρ
      (show 0 ≤ 4*cost*Cnear by positivity) (show 0 ≤ 4*cost*Cfar by positivity)
      (fun θ => compactRadialPhaseKernel_nonneg d₀ f τ lam H a θ) hker.1 hker.2.1
    have hb' : ‖∫ θ in S, F θ‖ ≤
        ((4*cost*Cnear)*ρ^m+(4*cost*Cfar)*ρ^(-(2*M+1:ℕ):ℤ))*(Q^(n+1)*(n+1:ℕ)^4*(H+1)^2) := by
      apply hb
      filter_upwards [ae_restrict_mem (show MeasurableSet S from measurableSet_Icc),
        ae_restrict_of_ae (allBranchExterior_ae_selected_distinct i j hne)] with θ hθ hgap
      have hcube : ∀ l, θ l ∈ Icc (-R) R := fun l => ⟨hθ.1 l,hθ.2 l⟩
      have hd : 0 < compactAllowedDiameter P θ :=
        (abs_pos.mpr (sub_ne_zero.mpr hgap)).trans_le (compactAllowedDiameter_pair_le P θ hij)
      have hgapT : |θ i-θ j| ≤ T := (abs_le.mpr ⟨by linarith [(hθ.1 i),(hθ.2 j)],
        by linarith [(hθ.2 i),(hθ.1 j)]⟩ : |θ i-θ j| ≤ 2*R).trans (le_max_right _ _)
      have hv := hvH n hND τ lam hτ hτ1 hlam hlamB P M hM hJM i j hij hne h hh θ hcube hgap
        T (le_max_left _ _) hgapT _ hA Cnear Cfar (2*(J:ℤ)+(m+1:ℕ)) (hnear θ hθ hd) (hfar θ hθ)
      have hp := (hwH (n+1) (Nat.succ_pos n) hND τ lam hτ hτ1 hlam hlamB i j hne θ hcube).2 hgap
      have hfEq := compact_guarded_pulled_factorization f hf hr hr1 hτ hlam hh P M hij w hw J hp
      have hLθ : 0 ≤ L θ := compactRadialPhaseKernel_nonneg d₀ f τ lam H a θ
      have hnorm : ‖F θ‖=‖mixedSimpleKernel f r τ lam s θ‖*
          ‖((lieStep V)^[J] (fun z x => (compactGuardedPairWeight P M h i j x:ℂ)*
            (w x*compactRegularDensity f r τ lam z x))) s θ‖ := by
        change ‖((lieStep V)^[J] A) s θ‖=_
        rw [hfEq,norm_mul]
      refine ⟨hd,?_,?_⟩
      · intro hn
        have hvn := hv.1 (hn.trans hρ1)
        have hexp : (2*(J:ℤ)+(m+1:ℕ))-2*(J:ℤ)=(m+1:ℕ) := by ring
        rw [hexp,zpow_natCast] at hvn
        rw [hnorm]
        exact (mul_le_mul (hker.2.2 θ) hvn (norm_nonneg _) (by positivity)).trans_eq (by dsimp [cost,L]; ring)
      · intro _
        rw [hnorm]
        exact (mul_le_mul (hker.2.2 θ) hv.2 (norm_nonneg _) (by positivity)).trans_eq (by dsimp [cost,L]; ring)
    exact hb'.trans_eq (by ring)
  have hlim := compact_guarded_integral_derivatives_tendsto f hf hr hr1 hτ hlam P M hij hne w hw hwK J hs
  exact le_of_tendsto hlim.norm (Eventually.of_forall (fun l => hbound _ (allBranchTruncationScale_pos l)))

end
end IsingBulk.Tail
