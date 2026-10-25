import IsingBulk.Joint.RegularEdges.CompactFullJets
import IsingBulk.Anisotropic.RegularEdges.IntegratedJets

/-! # Actual complete mixed differentiated tails on compact families -/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology BigOperators

theorem compact_full_integrated_mixed_jets {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ r C M : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧
      ∀ j : ℕ, ∃ D : ℝ, 0<D ∧ ∀ v∈K, ∀ x∈ball ((0:ℂ),v) δ, 0<x.1.im →
      ∀ k : ℕ,
      ‖∫ q : Fin (2*j+3+k) → ℝ,
        iteratedFDeriv ℂ j (fun p => independentFullIntegrand b p (centeredFullAngles (2*j+3+k) q))
          x ∂Measure.pi (fun _ => edgeAngleMeasure)‖≤
        D*particleEdgeMajorant r C M (2*j+3+k+1)*((2*j+3+k+1:ℕ):ℝ)^j := by
  obtain ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,hall⟩ := compact_full_integrand_mixed_jets hb hK hB hS
  refine ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,?_⟩
  intro j
  obtain ⟨D,hD,hbound⟩ := hall j
  refine ⟨D*retainedIntegralBound j,mul_pos hD (retainedIntegralBound_pos j),?_⟩
  intro v hv x hx hi k
  let : Nonempty (Fin (2*j+3)) := ⟨⟨0,by omega⟩⟩
  let W := D*particleEdgeMajorant r C M (2*j+3+k+1)*((2*j+3+k+1:ℕ):ℝ)^j
  have hp := retainedPower_lift_integrable j k
  have hg : Integrable (fun q : Fin (2*j+3+k) → ℝ =>
      W*(1+‖fun i : Fin (2*j+3) => q (Fin.castAdd k i)‖^(-(2*(j+1):ℝ))))
      (Measure.pi fun _ => edgeAngleMeasure) := ((integrable_const 1).add hp).const_mul W
  have hh : ‖∫ q : Fin (2*j+3+k) → ℝ,
      iteratedFDeriv ℂ j (fun p => independentFullIntegrand b p (centeredFullAngles (2*j+3+k) q))
        x ∂Measure.pi (fun _ => edgeAngleMeasure)‖≤
      ∫ q : Fin (2*j+3+k) → ℝ,
        W*(1+‖fun i : Fin (2*j+3) => q (Fin.castAdd k i)‖^(-(2*(j+1):ℝ)))
          ∂Measure.pi (fun _ => edgeAngleMeasure) := by
    apply norm_integral_le_of_norm_le hg
    filter_upwards [edgeAngleMeasure_pi_ae_mem (2*j+3+k),retainedCoordinates_ae_ne_zero j k]
      with q hq hq0
    have hn := centeredFullAngles_retained_norm (2*j+3) k q hq
    have hne : (fun i : Fin (2*j+3) =>
        centeredFullAngles (2*j+3+k) q ((Fin.castAdd k i).castSucc))≠0 := by
      intro he
      have hh := congrArg norm he
      rw [hn,norm_zero] at hh
      exact hq0 (norm_eq_zero.mp hh)
    have hb' := hbound v hv x hx hi (2*j+3+k+1) (2*j+3)
      (centeredFullAngles (2*j+3+k) q) (fun i => (Fin.castAdd k i).castSucc)
      (fun i => wrapAngle_mem _) hne
    simpa only [hn,W] using hb'
  rw [integral_const_mul, integral_add (integrable_const 1) hp,
    retainedPower_integral_lift] at hh
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hh
  convert hh using 1
  dsimp [W,retainedIntegralBound]
  ring


/-- All particle indices above the retained-dimension threshold are present.
The same independent polydisk works for every mixed derivative order. -/
theorem compact_full_tail_summable_mixed_jets {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ j : ℕ, ∃ G : ℕ→ℝ,
      Summable G ∧ (∀ k, 0≤G k) ∧
      ∀ v∈K, ∀ x∈ball ((0:ℂ),v) δ, 0<x.1.im → ∀ k : ℕ,
      ‖∫ q : Fin (2*j+3+k) → ℝ,
        iteratedFDeriv ℂ j (fun p => independentFullIntegrand b p (centeredFullAngles (2*j+3+k) q))
          x ∂Measure.pi (fun _ => edgeAngleMeasure)‖≤G k := by
  obtain ⟨δ,r,C,M,hδ,hr,hr1,hC,hM,hall⟩ := compact_full_integrated_mixed_jets hb hK hB hS
  refine ⟨δ,hδ,?_⟩
  intro j
  obtain ⟨D,hD,hbound⟩ := hall j
  let G : ℕ→ℝ := fun k => D*particleEdgeMajorant r C M (2*j+3+k+1)*((2*j+3+k+1:ℕ):ℝ)^j
  have hsum : Summable G := by
    have hh := (particleEdgeMajorant_polynomial_summable hr hr1 hC hM j).comp_injective
      (i := fun k : ℕ => 2*j+3+k+1) (by intro a b h; dsimp at h; omega)
    simpa only [G,Function.comp_def,mul_assoc,mul_comm,mul_left_comm] using hh.mul_left D
  exact ⟨G,hsum,fun k => mul_nonneg (mul_nonneg hD.le
    (particleEdgeMajorant_nonneg hr.le hC.le hM.le _)) (pow_nonneg (Nat.cast_nonneg _) _),hbound⟩

end
end IsingBulk.Joint.RegularEdges
