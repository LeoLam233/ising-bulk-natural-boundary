import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! Actual finite-product integration for an arbitrary pairing of coordinates.
Matching enumeration and the source Pfaffian expansion remain separate. -/
namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory
open scoped BigOperators

variable {ι κ E : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace E]

theorem finite_uncurry_measurePreserving (μ : Measure E) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ E).symm
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ)))
      (Measure.pi (fun _ : ι × κ => μ)) := by
  refine ⟨(MeasurableEquiv.curry ι κ E).symm.measurable, ?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have hp : (MeasurableEquiv.curry ι κ E).symm ⁻¹' (Set.pi Set.univ s) =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i,j))) := by
    ext x
    simp [Set.mem_pi, MeasurableEquiv.coe_curry_symm, Function.uncurry]
  rw [hp, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : ι × κ => μ (s p))).symm

theorem paired_block_integral (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : (Fin 2 → E) → ℝ) :
    (∫ x : Fin n × Fin 2 → E, ∏ i : Fin n, f (fun j => x (i,j))
      ∂Measure.pi (fun _ => μ)) =
      (∫ v : Fin 2 → E, f v ∂Measure.pi (fun _ => μ))^n := by
  rw [← (finite_uncurry_measurePreserving (ι := Fin n) (κ := Fin 2) μ).integral_comp']
  simpa [MeasurableEquiv.coe_curry_symm, Function.uncurry] using
    (integral_fintype_prod_eq_pow (ι := Fin n) (μ := Measure.pi (fun _ : Fin 2 => μ)) f)

/-- Any pairing is just a measure-preserving reindexing, not a probabilistic
independence assumption about an already integrated expression. -/
theorem arbitrary_pairing_integral (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (e : (Fin n × Fin 2) ≃ Fin (2*n)) (f : (Fin 2 → E) → ℝ) :
    (∫ x : Fin (2*n) → E, ∏ i : Fin n, f (fun j => x (e (i,j)))
      ∂Measure.pi (fun _ => μ)) =
      (∫ v : Fin 2 → E, f v ∂Measure.pi (fun _ => μ))^n := by
  rw [← (measurePreserving_piCongrLeft (fun _ : Fin (2*n) => μ) e).integral_comp']
  simpa [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply] using
    paired_block_integral n μ f

/-- The pair integral is the genuine two-angle iterated integral. -/
theorem pair_integral_eq_iterated (μ : Measure E) [SigmaFinite μ]
    (f : E → E → ℝ) (hf : Integrable (Function.uncurry f) (μ.prod μ)) :
    (∫ v : Fin 2 → E, f (v 0) (v 1) ∂Measure.pi (fun _ => μ)) =
      ∫ x, ∫ y, f x y ∂μ ∂μ := by
  rw [← (measurePreserving_piFinTwo (fun _ : Fin 2 => μ)).symm.integral_comp']
  simpa [MeasurableEquiv.piFinTwo_symm_apply, Function.uncurry] using integral_prod (Function.uncurry f) hf

theorem arbitrary_pairing_integrable (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (e : (Fin n × Fin 2) ≃ Fin (2*n)) (f : (Fin 2 → E) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin 2 => μ))) :
    Integrable (fun x : Fin (2*n) → E => ∏ i : Fin n, f (fun j => x (e (i,j))))
      (Measure.pi (fun _ => μ)) := by
  rw [← (measurePreserving_piCongrLeft (fun _ : Fin (2*n) => μ) e).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rw [← (finite_uncurry_measurePreserving (ι := Fin n) (κ := Fin 2) μ).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simpa [Function.comp_def, MeasurableEquiv.coe_curry_symm, Function.uncurry] using
    (Integrable.fintype_prod (ι := Fin n) (fun _ => hf))

theorem arbitrary_pairing_integral_iterated (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (e : (Fin n × Fin 2) ≃ Fin (2*n)) (f : E → E → ℝ)
    (hf : Integrable (Function.uncurry f) (μ.prod μ)) :
    (∫ x : Fin (2*n) → E, ∏ i : Fin n, f (x (e (i,0))) (x (e (i,1)))
      ∂Measure.pi (fun _ => μ)) = (∫ x, ∫ y, f x y ∂μ ∂μ)^n := by
  rw [arbitrary_pairing_integral n μ e (fun v => f (v 0) (v 1)),
    pair_integral_eq_iterated μ f hf]

end
end IsingBulk.Tail
