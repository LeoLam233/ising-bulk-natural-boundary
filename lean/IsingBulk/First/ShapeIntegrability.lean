import IsingBulk.First.ShapePolar

/-! Absolute integrability of the actual constrained period after mean integration. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Metric Module

/-- Integrability version of the exact radial density conversion. -/
theorem integrable_shapeRadialDensity (n d : ℕ) (f : ℝ → ℂ) :
    Integrable (fun r : Ioi (0 : ℝ) => (r.1 ^ d) • f r.1)
      (Measure.volumeIoiPow (n-1)) ↔
      IntegrableOn (fun r : ℝ => (r ^ (n-1+d)) • f r) (Ioi 0) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul']
  · rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
    apply integrable_congr
    apply Filter.Eventually.of_forall
    intro r
    simp only [Function.comp_apply]
    rw [ENNReal.toReal_ofReal (pow_nonneg r.2.le _), smul_smul, ← pow_add]
  · fun_prop
  · exact Filter.Eventually.of_forall fun r => ENNReal.ofReal_lt_top

/-- Weighted polar integrability, keeping the squared Vandermonde angular factor. -/
theorem integrable_shapeVandermonde_polar {n : ℕ} (hn : 1 ≤ n) (f : ℝ → ℂ)
    (hr : IntegrableOn (fun r : ℝ => (r ^ (n-1+(n+1)*n)) • f r) (Ioi 0)) :
    Integrable (fun x : ShapeSpace n => shapeVandermondeSq x • f ‖x‖) := by
  let : Nontrivial (ShapeSpace n) := ⟨⟨distinctShape n, 0, distinctShape_ne_zero hn⟩⟩
  let F : ShapeSpace n → ℂ := fun x => shapeVandermondeSq x • f ‖x‖
  let G : sphere (0 : ShapeSpace n) 1 × Ioi (0 : ℝ) → ℂ :=
    fun z => F ((homeomorphUnitSphereProd (ShapeSpace n)).symm z).1
  have hg (z : sphere (0 : ShapeSpace n) 1 × Ioi (0 : ℝ)) :
      G z = shapeVandermondeSq z.1.1 • ((z.2.1 ^ ((n+1)*n)) • f z.2.1) := by
    have hnorm : ‖(z.2.1 • z.1.1 : ShapeSpace n)‖ = z.2.1 := by
      calc
        ‖(z.2.1 • z.1.1 : ShapeSpace n)‖ = ‖z.2.1‖ * ‖z.1.1‖ := norm_smul _ _
        _ = z.2.1 := by
          rw [Real.norm_eq_abs, abs_of_pos z.2.2,
            mem_sphere_zero_iff_norm.mp z.1.2, mul_one]
    change shapeVandermondeSq (z.2.1 • z.1.1) • f ‖(z.2.1 • z.1.1 : ShapeSpace n)‖ = _
    rw [hnorm, shapeVandermondeSq_homogeneous, mul_smul, smul_comm]
  have hrad := (integrable_shapeRadialDensity n ((n+1)*n) f).mpr hr
  have hprod : Integrable G ((volume : Measure (ShapeSpace n)).toSphere.prod
      (Measure.volumeIoiPow (n-1))) := by
    exact ((shapeSphere_integrable n).smul_prod hrad).congr
      (Filter.Eventually.of_forall fun z => (hg z).symm)
  have hp := (volume : Measure (ShapeSpace n)).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (Homeomorph.measurableEmbedding _) (g := G)
  rw [finrank_shapeSpace] at hp
  have hi := hp.mpr hprod
  simp only [Function.comp_def, G, Homeomorph.symm_apply_apply] at hi
  have hi' : IntegrableOn F ({(0 : ShapeSpace n)}ᶜ) :=
    (integrableOn_iff_comap_subtypeVal (f := F) (measurableSet_singleton _).compl).mpr hi
  simpa only [IntegrableOn, restrict_compl_singleton] using hi' 

theorem shapePeriodIntrinsic_boundary_integrable {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) {Q d δ : ℝ}
    (hQ : 0 < Q) (hd : 0 < d) (hδ : 0 ≤ δ) :
    Integrable (fun x : ShapeSpace n => (shapeVandermondeSq x : ℂ) /
      ((Q : ℂ) + ((δ : ℂ) - Complex.I * d) * (‖x‖ : ℂ)^2)^(k+1)) := by
  have hr := (shapeRadialKernel_boundary_integrable k hQ hd hδ).integrableOn (s := Ioi 0)
  change IntegrableOn (fun r : ℝ => (r : ℂ)^(2*k) /
    ((Q : ℂ) + ((δ : ℂ) - Complex.I*d) * (r : ℂ)^2)^(k+1)) (Ioi 0) at hr
  have hi := integrable_shapeVandermonde_polar hn
    (fun r => (((Q : ℂ) + ((δ : ℂ) - Complex.I*d) * (r : ℂ)^2)^(k+1))⁻¹)
  apply hi
  simpa only [hdegree, Complex.real_smul,
    Complex.ofReal_pow, div_eq_mul_inv] using hr

theorem shapePeriod_boundary_integrable {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) {Q d δ : ℝ}
    (hQ : 0 < Q) (hd : 0 < d) (hδ : 0 ≤ δ) :
    Integrable (fun t : Fin n → ℝ =>
      let x := shapeCoordinateEquiv n (WithLp.toLp 2 t)
      (shapeVandermondeSq x : ℂ) /
        ((Q : ℂ) + ((δ : ℂ) - Complex.I * d) * (‖x‖ : ℂ)^2)^(k+1)) := by
  have hi := shapePeriodIntrinsic_boundary_integrable hn hdegree hQ hd hδ
  have hc := (shapeCoordinateEquiv_measurePreserving n).integrable_comp_of_integrable hi
  have hz : ENNReal.ofReal (Real.sqrt (n+1 : ℝ)) ≠ 0 := by positivity
  have ht : ENNReal.ofReal (Real.sqrt (n+1 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hv := (integrable_smul_measure hz ht).mp hc
  exact (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_of_integrable hv

end
end IsingBulk.First
