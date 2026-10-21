import IsingBulk.HT.Tail.SignedExteriorNegativeKernel
import IsingBulk.HT.Tail.SignedExteriorOnePhaseIntegral

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail IsingBulk.HT.Lie Set MeasureTheory
open scoped BigOperators

theorem signed_allBranchExterior_original_Y_floor (ξ : ℝ) {n : ℕ} (d : LocalBranchData) {ε : ℝ} (hε : 0 < ε)
    (u : AngularSpace n)
    (hp : MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) :
    ‖1-Complex.exp (Complex.I*(ξ:ℂ))*regularYProduct (radialParameter d.theta ε) (fun i => originalPhase d ε (u i))‖⁻¹ ≤
      2*(phaseDenominator (Real.exp (-(d.c₀*ε))) ((∑ i, u i)-(n+1:ℝ)*d.thetaB+ξ))⁻¹ := by
  let v := -d.c₀*ε
  have hv : v < 0 := by dsimp [v]; nlinarith [d.c₀_pos]
  have hY : ‖Complex.exp (allBranchExteriorYExponent v d.thetaB u)‖ ≤ Real.exp v := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [allBranchExteriorYExponent,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero]
    push_cast
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hh := signed_exp_kernel_floor (allBranchExteriorYExponent v d.thetaB u) ξ
    (show 0 < -v by linarith) (by simpa using hY)
  have hi : (allBranchExteriorYExponent v d.thetaB u).im=(∑ i, u i)-(n+1:ℝ)*d.thetaB := by
    simp [allBranchExteriorYExponent]
  rw [hi] at hh
  rw [← original_chartMap_eq,allBranchExterior_regularY_exponent (-d.c₀*ε) d.thetaB _ u hp.g_pos]
  simpa [v,shiftedPhaseKernel] using hh

/-- A pointwise bound for the true kernel, before the negative-coordinate split. -/
theorem signed_allBranchExterior_kernel_density_Y_bound (ξ : ℝ) {n : ℕ} (d : LocalBranchData) {ε : ℝ}
    (hε : 0 < ε) (u : AngularSpace n)
    (hp : MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) :
    signedExteriorKernelDensity (Complex.exp (Complex.I*(ξ:ℂ))) d ε u ≤
      2*(phaseDenominator (Real.exp (-(d.c₀*ε))) ((∑ i, u i)-(n+1:ℝ)*d.thetaB+ξ))⁻¹*
        ((∏ i, ‖deriv (originalPhase d ε) (u i)‖)/
          ‖1-Complex.exp (Complex.I*(ξ:ℂ))*regularZProduct (radialParameter d.theta ε) (fun i => originalPhase d ε (u i))‖) := by
  have hh := mul_le_mul_of_nonneg_right (signed_allBranchExterior_original_Y_floor ξ d hε u hp)
    (show 0 ≤ (∏ i, ‖deriv (originalPhase d ε) (u i)‖)/
      ‖1-Complex.exp (Complex.I*(ξ:ℂ))*regularZProduct (radialParameter d.theta ε) (fun i => originalPhase d ε (u i))‖ from
      div_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _))
  apply le_trans (le_of_eq ?_) hh
  unfold signedExteriorKernelDensity signedRegularKernel
  rw [norm_mul]
  ring

theorem signed_allBranchExterior_negative_density_bounds {d : LocalBranchData} (B : BranchEstimates d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ξ : ℝ, ∀ n : ℕ, ∀ ε a : ℝ,
      0 < ε → ε ≤ B.ε₀ → 0 < a → ∀ u : AngularSpace n,
      (∀ i, |u i| ≤ B.r) →
      MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u →
      ∀ p v : Fin (n+1), a ≤ |u p| → u v ≤ 0 →
      (p ≠ v → signedExteriorKernelDensity (Complex.exp (Complex.I*(ξ:ℂ))) d ε u ≤
        (2*(B.magnitudeUpper/Real.sqrt a)*C)*shiftedExteriorLogPhaseKernel ξ d ε (d.c₀*ε) p v u) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ |u v| → signedExteriorKernelDensity (Complex.exp (Complex.I*(ξ:ℂ))) d ε u ≤
        (2*(B.magnitudeUpper/Real.sqrt a)/(c*Real.sqrt δ))*shiftedExteriorOnePhaseKernel ξ d ε (d.c₀*ε) p u) := by
  obtain ⟨c,C,hc,hC,hneg⟩ := signed_exterior_negative_Z_bound B
  refine ⟨c,C,hc,hC,?_⟩
  intro ξ n ε a hε hεr ha u hu hp p v hpa hv
  let L := fun i => ‖deriv (originalPhase d ε) (u i)‖
  let Z := ‖1-Complex.exp (Complex.I*(ξ:ℂ))*regularZProduct (radialParameter d.theta ε) (fun i => originalPhase d ε (u i))‖
  let Y := (phaseDenominator (Real.exp (-(d.c₀*ε))) ((∑ i, u i)-(n+1:ℝ)*d.thetaB+ξ))⁻¹
  let A := B.magnitudeUpper/Real.sqrt a
  have hA : 0 ≤ A := div_nonneg B.magnitudeUpper_pos.le (Real.sqrt_nonneg a)
  have hY : 0 ≤ Y := inv_nonneg.mpr (norm_nonneg _)
  have hpL : L p ≤ A := allBranchExterior_anchor_measure_bound B hε hεr ha (hu p) hpa
  have hz := hneg (Complex.exp (Complex.I*(ξ:ℂ)))
    (by simp [Complex.norm_exp,Complex.mul_re]) (n+1) ε hε hεr u hu v hv
  dsimp only at hz
  have hprod : (∏ i, L i)=L p*(∏ i ∈ Finset.univ.erase p, L i) :=
    (Finset.mul_prod_erase Finset.univ L (Finset.mem_univ p)).symm
  have hstart : signedExteriorKernelDensity (Complex.exp (Complex.I*(ξ:ℂ))) d ε u ≤ 2*Y*((∏ i, L i)/Z) :=
    signed_allBranchExterior_kernel_density_Y_bound ξ d hε u hp
  constructor
  · intro hpv
    have hrest : (∏ i ∈ Finset.univ.erase p, L i)=L v*(∏ i ∈ (Finset.univ.erase p).erase v, L i) :=
      (Finset.mul_prod_erase (Finset.univ.erase p) L
        (Finset.mem_erase.mpr ⟨hpv.symm,Finset.mem_univ v⟩)).symm
    have hb : L p*(L v/Z) ≤ A*(C/(|u v|+ε)) :=
      mul_le_mul hpL hz.2 (div_nonneg (norm_nonneg _) (norm_nonneg _)) hA
    have hb' := mul_le_mul_of_nonneg_right hb
      (Finset.prod_nonneg (s := (Finset.univ.erase p).erase v) (f := L) (fun _ _ => norm_nonneg _))
    calc
      _ ≤ 2*Y*((∏ i, L i)/Z) := hstart
      _ = 2*Y*((L p*(L v/Z))*(∏ i ∈ (Finset.univ.erase p).erase v, L i)) := by rw [hprod,hrest]; ring
      _ ≤ 2*Y*((A*(C/(|u v|+ε)))*(∏ i ∈ (Finset.univ.erase p).erase v, L i)) :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = _ := by unfold shiftedExteriorLogPhaseKernel; dsimp [Y,A,L]; push_cast; ring
  · intro δ hδ hδv
    have hz' : c*Real.sqrt δ ≤ Z :=
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (show δ ≤ |u v|+ε by linarith)) hc.le).trans hz.1
    have hb : L p/Z ≤ A/(c*Real.sqrt δ) :=
      div_le_div₀ hA hpL (mul_pos hc (Real.sqrt_pos.mpr hδ)) hz'
    have hb' := mul_le_mul_of_nonneg_right hb
      (Finset.prod_nonneg (s := Finset.univ.erase p) (f := L) (fun _ _ => norm_nonneg _))
    calc
      _ ≤ 2*Y*((∏ i, L i)/Z) := hstart
      _ = 2*Y*((L p/Z)*(∏ i ∈ Finset.univ.erase p, L i)) := by rw [hprod]; ring
      _ ≤ 2*Y*((A/(c*Real.sqrt δ))*(∏ i ∈ Finset.univ.erase p, L i)) :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = _ := by unfold shiftedExteriorOnePhaseKernel; dsimp [Y,A,L]; push_cast; ring

end
end IsingBulk.HT.Tail
