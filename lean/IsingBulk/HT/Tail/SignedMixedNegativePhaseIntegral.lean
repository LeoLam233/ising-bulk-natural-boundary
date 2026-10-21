import IsingBulk.HT.Contour.SignedLeftKernelIntegral
import IsingBulk.Tail.MixedNegativePhaseIntegral

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie IsingBulk.HT.Contour Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem shifted_angular_one_phase_weighted_integral (ξ : ℝ) {N : ℕ} (p q : Fin N) (hpq : p≠q)
    (L : Fin N → ℝ → ℝ) (C : Fin N → ℝ) (hL0 : ∀ i t,0≤L i t)
    {a : ℝ} (ha : 0<a) (ha1 : a≤1)
    (hL : ∀ i,ContinuousOn (L i) (Icc 0 (2*Real.pi)))
    (hLint : ∀ i,(∫ t in Icc 0 (2*Real.pi),L i t)≤C i) :
    let f := fun θ : Fin N → ℝ => shiftedPhaseKernel a ξ (∑ i,θ i)*
      ∏ i∈Finset.univ.erase p,L i (θ i)
    IntegrableOn f (angleBox N) ∧ (∫ θ in angleBox N,f θ)≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*(∏ i∈Finset.univ.erase p,C i) := by
  have hk := shifted_angular_one_phase_product_integral ξ p L C hL0 ha ha1 hL hLint
  have hh := injective_coordinate_weighted_coarea_on (S := angleBox N) measurableSet_Icc
    (onePhaseSumMap p 0) (fun _ => onePhaseSumDerivative p)
    (fun θ _ => (onePhaseSum_hasFDerivAt p 0 θ).hasFDerivWithinAt)
    (onePhaseSum_injective p 0).injOn (angularOnePhaseMap_image p)
    (fun _ => 1) (shiftedOnePhaseSpectatorKernel ξ p a L) continuousOn_const
    (shiftedAngularOnePhaseKernel_continuousOn ξ p ha L hL)
    (shiftedOnePhaseSpectatorKernel_nonneg ξ p a L hL0) hk.1 (C := 1) zero_le_one
    (fun _ _ => zero_le_one) (fun _ _ => by rw [onePhaseSum_det p q hpq]; norm_num)
  simp only [one_mul,shiftedOnePhaseSum_kernel_eq,mul_zero,sub_zero] at hh
  exact ⟨hh.1,hh.2.trans hk.2⟩

def signedMixedNegativePhaseMajorant (ξ : ℝ) {N : ℕ} (b B eps a : ℝ) (j q : Fin N) (θ : Fin N → ℝ) : ℝ :=
  shiftedPhaseKernel a ξ (∑ i,θ i)*(|θ j+b-2*Real.pi|+eps)⁻¹*
    ∏ i∈(Finset.univ.erase q).erase j,mixedSpectatorMajorant b B eps (θ i)

/-- The negative-coordinate attenuation pays one logarithm and the true
sum phase pays the other. Spectators retain their uniform scalar L1 cost. -/
theorem signed_mixed_negative_phase_integral (ξ : ℝ) {N : ℕ} (j q : Fin N) (hjq : j≠q)
    {b B eps a : ℝ} (hb : 0≤b) (hb2 : b≤2*Real.pi) (hB : 0≤B)
    (he : 0<eps) (ha : 0<a) (ha1 : a≤1) :
    IntegrableOn (signedMixedNegativePhaseMajorant ξ b B eps a j q) (angleBox N) ∧
      (∫ θ in angleBox N,signedMixedNegativePhaseMajorant ξ b B eps a j q θ)≤
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
          (2*Real.log ((2*Real.pi+eps)/eps))*(2*Real.pi+4*B*Real.sqrt (2*Real.pi))^(N-2) := by
  classical
  let P := 2*Real.pi+4*B*Real.sqrt (2*Real.pi)
  let D := 2*Real.log ((2*Real.pi+eps)/eps)
  let L := fun i : Fin N => if i=j then (fun t : ℝ => (|t+b-2*Real.pi|+eps)⁻¹)
    else mixedSpectatorMajorant b B eps
  let C := fun i : Fin N => if i=j then D else P
  have hL0 (i : Fin N) (t : ℝ) : 0≤L i t := by
    dsimp [L]
    split_ifs
    · exact inv_nonneg.mpr (by positivity)
    · exact zero_le_one.trans (mixedSpectatorMajorant_one_le b hB t)
  have hLc (i : Fin N) : ContinuousOn (L i) (Icc 0 (2*Real.pi)) := by
    dsimp [L]
    split_ifs
    · exact ((reciprocal_abs_continuous he).comp ((continuous_id.add continuous_const).sub continuous_const)).continuousOn
    · exact (mixedSpectatorMajorant_continuous b B he).continuousOn
  have hLint (i : Fin N) : (∫ t in Icc 0 (2*Real.pi),L i t)≤C i := by
    dsimp [L,C]
    split_ifs
    · exact shifted_reciprocal_angular_integral hb hb2 he
    · exact (mixedSpectatorMajorant_integral hb hb2 hB he).2
  have hj : j∈Finset.univ.erase q := Finset.mem_erase.mpr ⟨hjq,Finset.mem_univ _⟩
  have hprod (θ : Fin N → ℝ) : (∏ i∈Finset.univ.erase q,L i (θ i))=
      (|θ j+b-2*Real.pi|+eps)⁻¹*
        ∏ i∈(Finset.univ.erase q).erase j,mixedSpectatorMajorant b B eps (θ i) := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase q) (fun i => L i (θ i)) hj]
    dsimp only [L]
    simp only [ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp [(Finset.mem_erase.mp hi).1]
  have hCprod : (∏ i∈Finset.univ.erase q,C i)=D*P^(N-2) := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase q) C hj]
    dsimp only [C]
    simp only [ite_true]
    congr 1
    have hh : (∏ i∈(Finset.univ.erase q).erase j,if i=j then D else P)=
        ∏ _i∈(Finset.univ.erase q).erase j,P := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [(Finset.mem_erase.mp hi).1]
    rw [hh,Finset.prod_const,Finset.card_erase_of_mem hj,
      Finset.card_erase_of_mem (Finset.mem_univ q),Finset.card_univ,Fintype.card_fin]
    congr 1
  have hh := shifted_angular_one_phase_weighted_integral ξ q j hjq.symm L C hL0 ha ha1 hLc hLint
  unfold signedMixedNegativePhaseMajorant
  simpa only [hprod,hCprod,D,P,mul_assoc] using hh

end
end IsingBulk.HT.Tail
