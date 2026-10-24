import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedAngles

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open MeasureTheory Set Filter IsingBulk.Anisotropic.RegularEdges
open scoped ENNReal Topology

theorem negativeShiftedFullIntegrand_integrated_jets {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    ∃ δ r C M D : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<D ∧
      ∀ ε : ℝ, 0<ε → ε<δ → ∀ k : ℕ,
      ‖∫ q : Fin (2*j+3+k) → ℝ,
        iteratedDeriv j (fun u => negativeShiftedFullIntegrand b B S (2*j+3+k) u q)
          (Complex.I*(ε:ℂ)) ∂Measure.pi (fun _ => edgeAngleMeasure)‖≤
        D*particleEdgeMajorant r C M (2*j+3+k+1)*((2*j+3+k+1:ℕ):ℝ)^j := by
  obtain ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,hD,hbound⟩ :=
    negativeShiftedFullIntegrand_uniform_jets hb hB hc hS hS0 j
  refine ⟨δ,r,C,M,D*retainedIntegralBound j,hδ,hr,hr1,hC,hM,
    mul_pos hD (retainedIntegralBound_pos j),?_⟩
  intro ε hε hεδ k
  let : Nonempty (Fin (2*j+3)) := ⟨⟨0,by omega⟩⟩
  let W := D*particleEdgeMajorant r C M (2*j+3+k+1)*((2*j+3+k+1:ℕ):ℝ)^j
  have hp := retainedPower_lift_integrable j k
  have hg : Integrable (fun q : Fin (2*j+3+k) → ℝ =>
      W*(1+‖fun i : Fin (2*j+3) => q (Fin.castAdd k i)‖^(-(2*(j+1):ℝ))))
      (Measure.pi fun _ => edgeAngleMeasure) := ((integrable_const 1).add hp).const_mul W
  have hh : ‖∫ q : Fin (2*j+3+k) → ℝ,
      iteratedDeriv j (fun u => negativeShiftedFullIntegrand b B S (2*j+3+k) u q)
        (Complex.I*(ε:ℂ)) ∂Measure.pi (fun _ => edgeAngleMeasure)‖≤
      ∫ q : Fin (2*j+3+k) → ℝ,
        W*(1+‖fun i : Fin (2*j+3) => q (Fin.castAdd k i)‖^(-(2*(j+1):ℝ)))
          ∂Measure.pi (fun _ => edgeAngleMeasure) := by
    apply norm_integral_le_of_norm_le hg
    filter_upwards [edgeAngleMeasure_pi_ae_mem (2*j+3+k),retainedCoordinates_ae_ne_zero j k]
      with q hq hq0
    exact hbound ε hε hεδ (2*j+3) k q hq hq0
  rw [integral_const_mul, integral_add (integrable_const 1) hp,
    retainedPower_integral_lift] at hh
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hh
  convert hh using 1
  dsimp [W,retainedIntegralBound]
  ring


end
end IsingBulk.Anisotropic.NegativeDominance
