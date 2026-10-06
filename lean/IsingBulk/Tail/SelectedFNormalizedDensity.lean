import IsingBulk.Tail.SelectedFActualDensity
import IsingBulk.Tail.SelectorJacobianBounds

/-! Exact factorial-normalized selected integrand majorant. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem constructed_selected_weight_norm_le {N : ℕ} (b η α : ℝ) (θ : Fin N → ℝ) :
    ‖((1-angularSelector (constructedSelector b η α) θ:ℝ):ℂ)‖ ≤ 1 := by
  have h0 : 0 ≤ angularSelector (constructedSelector b η α) θ := by
    unfold angularSelector selectorWeight constructedSelector periodicUpperA
    exact Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (thresholdStep_range _ _ _).2)
  have h1 : angularSelector (constructedSelector b η α) θ ≤ 1 := by
    unfold angularSelector selectorWeight constructedSelector periodicUpperA
    exact Finset.prod_le_one₀ (fun i _ => sub_nonneg.mpr (thresholdStep_range _ _ _).2)
      (fun i _ => sub_le_self _ (thresholdStep_range _ _ _).1)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  linarith

theorem selected_actual_normalized_discount (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ C D K a : ℝ,
        0 < c ∧ 0 < eps₀ ∧ 0 < C ∧ 0 < D ∧ 0 < K ∧ 0 < a ∧
        ∀ (N : ℕ) (eps L : ℝ) (θ : Fin N → ℝ) (s : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → 0 < L → θ ∈ angleBox N →
          ‖s-radialParameter d.theta eps‖ ≤ c/(N:ℝ) →
          ‖((1-angularSelector (constructedSelector d.thetaB η α) θ:ℝ):ℂ)*
            continuedPulledDensity (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 s θ‖ ≤
            ((N.factorial:ℝ)⁻¹*K*D^N*Real.exp ((Real.log L)^2/(4*a)))*
              ((∏ i, discountedSelectedWeight d.thetaB η C eps L (θ i))*
                ‖First.pairProduct (deformedPoint (constructedSelector d.thetaB η α)
                  (Real.exp (-d.c₀*eps)) τ 1 θ)‖) := by
  obtain ⟨ηA,τ₀,hηA,hτ₀,hmain⟩ := selected_actual_reduced_discount d hcsmall
  refine ⟨min ηA (Real.sin d.thetaB/4),τ₀,lt_min hηA (by positivity [d.a_pos]),hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨c,e,C,D,K,a,hc,he,hC,hD,hK,ha,hred⟩ := hmain η α τ hη
    (hηlt.trans_le (min_le_left _ _)) hα hαsmall hτ hτlt
  obtain ⟨J,hJ,hjac⟩ := constructed_selector_jacobian_bound d.thetaB η α τ d.a_pos hη hηsmall hα hτ.le
  let E := Real.exp (d.c₀+2*τ)
  let D' := (2*Real.pi)⁻¹*J*E*D
  refine ⟨c,min e 1,C,D',K,a,hc,lt_min he (by norm_num),hC,by dsimp [D',E]; positivity,hK,ha,?_⟩
  intro N eps L θ s hN heps hepslt hL hθ hsd
  have heps1 := hepslt.le.trans (min_le_right e 1)
  have hweights : ∀ x, 0 ≤ discountedSelectedWeight d.thetaB η C eps L x := by
    intro x
    unfold discountedSelectedWeight
    split_ifs <;> positivity
  by_cases hsupp : θ ∈ tsupport (fun θ : Fin N → ℝ => 1-angularSelector (constructedSelector d.thetaB η α) θ)
  · have hb := hred N eps L θ s hN heps (hepslt.trans_le (min_le_left _ _)) hL hθ hsupp hsd
    have hj := hjac N (by omega) 1 (by norm_num) (by norm_num) θ
    have hy := selected_y_norm_envelope (by omega : 0<N) (constructedSelector d.thetaB η α)
      d.c₀_pos.le hτ.le heps.le heps1
      (fun x => (thresholdStep_range _ _ _).1) (fun x => (thresholdStep_range _ _ _).2)
      (fun x => Real.smoothTransition.nonneg _) (fun x => Real.smoothTransition.le_one _) θ
    have hyp : ∏ i, ‖deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 θ i‖ ≤ E^N := by
      calc
        _ ≤ ∏ _i : Fin N, E := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => (hy i).1)
        _ = _ := by simp
    have hw := constructed_selected_weight_norm_le d.thetaB η α θ
    rw [norm_mul,continuedPulledDensity_norm]
    calc
      _ ≤ 1*(((N.factorial:ℝ)⁻¹*(2*Real.pi)⁻¹^N)*J^N*E^N*
        (K*D^N*Real.exp ((Real.log L)^2/(4*a))*
          ((∏ i, discountedSelectedWeight d.thetaB η C eps L (θ i))*
            ‖First.pairProduct (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 θ)‖))) := by
        gcongr
      _ = _ := by dsimp [D']; simp only [mul_pow]; ring
  · have hz : 1-angularSelector (constructedSelector d.thetaB η α) θ=0 :=
      image_eq_zero_of_notMem_tsupport (f := fun θ : Fin N → ℝ => 1-angularSelector (constructedSelector d.thetaB η α) θ) hsupp
    rw [hz,Complex.ofReal_zero,zero_mul,norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (Finset.prod_nonneg (fun i _ => hweights (θ i))) (norm_nonneg _))

end
end IsingBulk.Tail
