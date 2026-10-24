import IsingBulk.Anisotropic.RegularEdges.FullIntegrandBound
import IsingBulk.Anisotropic.RegularEdges.AngularWrapping

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges
open IsingBulk.HT.Contour

 def centeredFullAngles (n : ℕ) (q : Fin n → ℝ) : Fin (n+1) → ℝ :=
  fun i => wrapAngle (physicalDependentAngles n q i)

 theorem norm_wrapAngle_of_mem {q : ℝ} (hq : q∈Icc (-Real.pi) Real.pi) :
    ‖wrapAngle q‖=‖q‖ := by
  rcases eq_or_lt_of_le hq.1 with he|he
  · rw [←he]
    simp [wrapAngle]
  · rw [wrapAngle, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨he,hq.2⟩]

 theorem centeredFullAngles_retained_norm (m k : ℕ) (q : Fin (m+k) → ℝ)
    (hq : ∀ i, q i∈Icc (-Real.pi) Real.pi) :
    ‖fun i : Fin m => centeredFullAngles (m+k) q ((Fin.castAdd k i).castSucc)‖ =
      ‖fun i : Fin m => q (Fin.castAdd k i)‖ := by
  simp only [centeredFullAngles,physicalDependentAngles,Fin.snoc_castSucc]
  rw [Pi.norm_def, Pi.norm_def]
  congr 1
  apply Finset.sup_congr rfl
  intro i _
  exact NNReal.eq (norm_wrapAngle_of_mem (hq (Fin.castAdd k i)))

 theorem edgeAngleMeasure_ae_mem : ∀ᵐ q ∂edgeAngleMeasure, q∈Icc (-Real.pi) Real.pi := by
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

 theorem edgeAngleMeasure_pi_ae_mem (n : ℕ) :
    ∀ᵐ q : Fin n → ℝ ∂Measure.pi (fun _ => edgeAngleMeasure),
      ∀ i, q i∈Icc (-Real.pi) Real.pi := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : Fin n => edgeAngleMeasure) i).quasiMeasurePreserving.ae
    edgeAngleMeasure_ae_mem

 theorem retainedCoordinates_ae_ne_zero (j k : ℕ) :
    ∀ᵐ q : Fin (2*j+3+k) → ℝ ∂Measure.pi (fun _ => edgeAngleMeasure),
      (fun i : Fin (2*j+3) => q (Fin.castAdd k i))≠0 := by
  filter_upwards [Measure.ae_eval_ne (fun _ : Fin (2*j+3+k) => edgeAngleMeasure)
    (Fin.castAdd k ⟨0,by omega⟩) 0] with q hq
  intro he
  exact hq (congrFun he ⟨0,by omega⟩)

 def retainedIntegralBound (j : ℕ) : ℝ :=
  1+∫ q : Fin (2*j+3) → ℝ, ‖q‖^(-(2*(j+1):ℝ))
    ∂Measure.pi (fun _ => edgeAngleMeasure)

 theorem retainedIntegralBound_pos (j : ℕ) : 0<retainedIntegralBound j := by
  have h : 0≤∫ q : Fin (2*j+3) → ℝ, ‖q‖^(-(2*(j+1):ℝ))
      ∂Measure.pi (fun _ => edgeAngleMeasure) :=
    integral_nonneg (fun q => Real.rpow_nonneg (norm_nonneg q) _)
  dsimp [retainedIntegralBound]
  linarith

/-- Uniform all-index integral bound for the actual differentiated full integrand.
The normalized unused angular volume is exactly one. -/
theorem edgeFullIntegrand_integrated_jets {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : AnalyticAt ℂ B 0)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    ∃ δ r C M D : ℝ, 0<δ ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<D ∧
      ∀ ε : ℝ, 0<ε → ε<δ → ∀ k : ℕ,
      ‖∫ q : Fin (2*j+3+k) → ℝ,
        iteratedDeriv j (fun u => edgeFullIntegrand b B S u (centeredFullAngles (2*j+3+k) q))
          (Complex.I*(ε:ℂ)) ∂Measure.pi (fun _ => edgeAngleMeasure)‖≤
        D*particleEdgeMajorant r C M (2*j+3+k+1)*((2*j+3+k+1:ℕ):ℝ)^j := by
  obtain ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,hD,hbound⟩ :=
    edgeFullIntegrand_uniform_jets hb hB hc hS hS0 j
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
      iteratedDeriv j (fun u => edgeFullIntegrand b B S u (centeredFullAngles (2*j+3+k) q))
        (Complex.I*(ε:ℂ)) ∂Measure.pi (fun _ => edgeAngleMeasure)‖≤
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
    have hb' := hbound ε hε hεδ (2*j+3+k+1) (2*j+3)
      (centeredFullAngles (2*j+3+k) q) (fun i => (Fin.castAdd k i).castSucc)
      (fun i => wrapAngle_mem _) hne
    simpa only [hn,W] using hb'
  rw [integral_const_mul, integral_add (integrable_const 1) hp,
    retainedPower_integral_lift] at hh
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hh
  convert hh using 1
  dsimp [W,retainedIntegralBound]
  ring

end IsingBulk.Anisotropic.RegularEdges
