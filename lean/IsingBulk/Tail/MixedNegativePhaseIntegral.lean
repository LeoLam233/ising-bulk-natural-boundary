import IsingBulk.Tail.AngularOnePhaseIntegral
import IsingBulk.Tail.MixedSpectatorMajorant
import IsingBulk.Tail.ReciprocalDistanceIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set MeasureTheory
open scoped BigOperators

theorem shifted_reciprocal_angular_integral {b eps : ℝ} (hb : 0≤b) (hb2 : b≤2*Real.pi)
    (he : 0<eps) :
    (∫ t in Icc 0 (2*Real.pi),(|t+b-2*Real.pi|+eps)⁻¹)≤
      2*Real.log ((2*Real.pi+eps)/eps) := by
  have hc := reciprocal_abs_continuous he
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by positivity : 0≤2*Real.pi)]
  have heq : (fun t : ℝ => (|t+b-2*Real.pi|+eps)⁻¹)=
      (fun t : ℝ => (|t-(2*Real.pi-b)|+eps)⁻¹) := by funext t; congr 3; ring
  rw [heq,intervalIntegral.integral_comp_sub_right (fun u : ℝ => (|u|+eps)⁻¹) (2*Real.pi-b)]
  calc
    _ ≤ ∫ u in -(2*Real.pi)..2*Real.pi,(|u|+eps)⁻¹ :=
      intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall (fun _ => inv_nonneg.mpr (by positivity)))
        (hc.intervalIntegrable _ _)
    _ = _ := reciprocal_abs_symmetric_integral (by positivity) he

def mixedNegativePhaseMajorant {N : ℕ} (b B eps a : ℝ) (j q : Fin N) (θ : Fin N → ℝ) : ℝ :=
  (phaseDenominator (Real.exp (-a)) (∑ i,θ i))⁻¹*(|θ j+b-2*Real.pi|+eps)⁻¹*
    ∏ i∈(Finset.univ.erase q).erase j,mixedSpectatorMajorant b B eps (θ i)

/-- The negative-coordinate attenuation pays one logarithm and the true
sum phase pays the other. Spectators retain their uniform scalar L1 cost. -/
theorem mixed_negative_phase_integral {N : ℕ} (j q : Fin N) (hjq : j≠q)
    {b B eps a : ℝ} (hb : 0≤b) (hb2 : b≤2*Real.pi) (hB : 0≤B)
    (he : 0<eps) (ha : 0<a) (ha1 : a≤1) :
    IntegrableOn (mixedNegativePhaseMajorant b B eps a j q) (angleBox N) ∧
      (∫ θ in angleBox N,mixedNegativePhaseMajorant b B eps a j q θ)≤
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
  have hh := angular_one_phase_weighted_integral q j hjq.symm L C hL0 ha ha1 hLc hLint
  unfold mixedNegativePhaseMajorant
  simpa only [hprod,hCprod,D,P,mul_assoc] using hh

end
end IsingBulk.Tail
