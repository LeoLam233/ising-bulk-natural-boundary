import IsingBulk.Tail.CompactCollisionSummability

namespace IsingBulk.Tail
noncomputable section
open Filter
set_option maxHeartbeats 1800000

def compactSourceMajorant (J : ℕ) (K G T Q Cnear Cfar κ B : ℝ) (N : ℕ) : ℝ :=
  (4*compactGuardedLieCost N (J+1) J K G T)*
    ((2^(3*J)*Cnear^(2*N^2+2*N)*(N:ℝ)^(8*J))*(Real.exp (-B*N))^(N*(N-1)-(2*J+1))+
      (Cfar^N*(N:ℝ)^(6*J)*Real.exp (-κ*(N:ℝ)^2))*(Real.exp (-B*N))^(-(2*(J+1)+1:ℕ):ℤ))*
    (Q^N*(N:ℝ)^6)

theorem compactSourceMajorant_nonneg (J N : ℕ) {K G T Q Cnear Cfar κ B : ℝ}
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hT : 0 ≤ T) (hQ : 0 ≤ Q) (hCn : 0 ≤ Cnear) (hCf : 0 ≤ Cfar) :
    0 ≤ compactSourceMajorant J K G T Q Cnear Cfar κ B N := by
  have hc := compactGuardedLieCost_nonneg N (J+1) J hK hG hT
  unfold compactSourceMajorant
  positivity

/-- Exponential collision splitting gives a summable majorant for the actual
full-compact integral cost. Its scale is fixed before particle number and H. -/
theorem compactSourceMajorant_summable (J : ℕ) (K G T Q Cnear Cfar : ℝ)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hT : 0 ≤ T) (hQ : 0 ≤ Q) (hCn : 0 ≤ Cnear) (hCf : 0 ≤ Cfar)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B → Summable (compactSourceMajorant J K G T Q Cnear Cfar κ B) := by
  let base := fun N : ℕ => (4*compactGuardedLieCost N (J+1) J K G T)*(Q^N*(N:ℝ)^6)
  have hb : NatExponentialEnvelope 1 base :=
    ((NatExponentialEnvelope.const 1 4).mul (compactGuardedLieCost_envelope (J+1) J K G T)).mul
      ((NatExponentialEnvelope.const_pow Q (fun N => N) (fun _ _ => by simp)).mul (NatExponentialEnvelope.id.pow 6))
  let near := fun N => base N*(2^(3*J)*Cnear^(2*N^2+2*N)*(N:ℝ)^(8*J))
  let far := fun N => base N*(Cfar^N*(N:ℝ)^(6*J))
  have hn : NatExponentialEnvelope 2 near := (hb.mono_degree (by omega)).mul (compact_collision_numerator_envelope J Cnear)
  have hf : NatExponentialEnvelope 1 far := hb.mul
    ((NatExponentialEnvelope.const_pow Cfar (fun N => N) (fun _ _ => by simp)).mul (NatExponentialEnvelope.id.pow (6*J)))
  obtain ⟨B₀,hB₀,hnf⟩ := compact_near_far_summable hn hf (2*J+1) (2*(J+1)+1) hκ
  refine ⟨B₀,hB₀,?_⟩
  intro B hB
  apply Summable.of_nonneg_of_le (fun N => compactSourceMajorant_nonneg J N hK hG hT hQ hCn hCf) _ (hnf B hB)
  intro N
  have hr : 0 < Real.exp (-B*(N:ℝ)) := Real.exp_pos _
  have hr1 : Real.exp (-B*(N:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg N (α := ℝ)])
  have hexp : (N-1)*(N-2)-(2*J+1) ≤ N*(N-1)-(2*J+1) :=
    Nat.sub_le_sub_right (by nlinarith [Nat.sub_le N 1,Nat.sub_le N 2]) _
  have hp := pow_le_pow_of_le_one hr.le hr1 hexp
  have hbase : 0 ≤ base N := by
    have hc := compactGuardedLieCost_nonneg N (J+1) J hK hG hT
    dsimp [base]
    positivity
  have he : compactSourceMajorant J K G T Q Cnear Cfar κ B N=
      base N*((2^(3*J)*Cnear^(2*N^2+2*N)*(N:ℝ)^(8*J))*
        (Real.exp (-B*N))^(N*(N-1)-(2*J+1))+
        (Cfar^N*(N:ℝ)^(6*J))*(Real.exp (-B*N))^(-(2*(J+1)+1:ℕ):ℤ)*Real.exp (-κ*(N:ℝ)^2)) := by
    dsimp [compactSourceMajorant,base]
    ring
  rw [he]
  have hnpos : 0 ≤ 2^(3*J)*Cnear^(2*N^2+2*N)*(N:ℝ)^(8*J) := by positivity
  have hh := mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hp hnpos)
    ((Cfar^N*(N:ℝ)^(6*J))*Real.exp (-B*N)^(-(2*(J+1)+1:ℕ):ℤ)*Real.exp (-κ*(N:ℝ)^2))) hbase
  dsimp only [near,far]
  convert hh using 1 <;> ring

end
end IsingBulk.Tail
