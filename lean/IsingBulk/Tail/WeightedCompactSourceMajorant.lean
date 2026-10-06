import IsingBulk.Tail.CompactSourceMajorant

namespace IsingBulk.Tail
noncomputable section
open Filter

/-- Finite sector-count costs are retained in the summability statement. -/
theorem compactSourceMajorant_weighted_summable (J : ℕ) (K G T Q Cnear Cfar : ℝ)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hT : 0 ≤ T) (hQ : 0 ≤ Q) (hCn : 0 ≤ Cnear) (hCf : 0 ≤ Cfar)
    {κ : ℝ} (hκ : 0 < κ) {w : ℕ → ℝ} (hw : NatExponentialEnvelope 1 w) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      Summable (fun N => w N*compactSourceMajorant J K G T Q Cnear Cfar κ B N) := by
  obtain ⟨C,hC,hw⟩ := hw
  obtain ⟨B₀,hB₀,hmain⟩ := compactSourceMajorant_summable J K G T (Real.exp C*Q) Cnear Cfar
    hK hG hT (by positivity) hCn hCf hκ
  refine ⟨B₀,hB₀,?_⟩
  intro B hB
  apply (hmain B hB).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hS := compactSourceMajorant_nonneg J N hK hG hT hQ hCn hCf (κ := κ) (B := B)
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hS]
  calc
    _ ≤ Real.exp (C*N)*compactSourceMajorant J K G T Q Cnear Cfar κ B N :=
      mul_le_mul_of_nonneg_right (by simpa only [pow_one] using hw N hN) hS
    _ = _ := by
      have he : (Real.exp C)^N=Real.exp (C*N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      unfold compactSourceMajorant
      rw [mul_pow,he]
      ring

def compactSectorMultiplicity (N : ℕ) : ℝ := (12:ℝ)^N*(N:ℝ)^2+1

theorem compactSectorMultiplicity_one_le (N : ℕ) : 1 ≤ compactSectorMultiplicity N := by
  unfold compactSectorMultiplicity
  have hh : 0 ≤ (12:ℝ)^N*(N:ℝ)^2 := by positivity
  linarith

theorem compactSectorMultiplicity_envelope : NatExponentialEnvelope 1 compactSectorMultiplicity :=
  ((NatExponentialEnvelope.const_pow 12 (fun N => N) (fun _ _ => by simp)).mul
    (NatExponentialEnvelope.id.pow 2)).add (NatExponentialEnvelope.const 1 1)

end
end IsingBulk.Tail
