import IsingBulk.First.ShapeSource

/-! Fixed-ball shape majorants for derivative orders below the first singular order.
No estimate on the physical numerator or differentiated density is assumed here. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Metric

/-- Below the singular derivative index, the constrained zero-damping shape
majorant is locally integrable, including the zero shape. -/
theorem shape_lower_order_integrableOn {n k j : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (hj : j < k) (R : ℝ) :
    IntegrableOn (fun x : ShapeSpace n =>
      shapeVandermondeSq x / ‖x‖^(2*(j+1))) (ball 0 R) := by
  have he : 2*(j+1) ≤ 2*k := by omega
  let e : ℕ := 2*k-2*(j+1)
  let f : ℝ → ℂ := (Iio R).indicator (fun r => ((r^(2*(j+1)))⁻¹ : ℝ))
  have hc : Continuous (fun r : ℝ => ((r^e : ℝ) : ℂ)) := by fun_prop
  have hpoly : IntegrableOn (fun r : ℝ => ((r^e : ℝ) : ℂ)) (Iio R ∩ Ioi 0) := by
    have h := hc.integrableOn_Ioc (μ := volume) (a := 0) (b := R)
    apply h.mono_set
    intro r hr
    exact ⟨hr.2, hr.1.le⟩
  have hind : IntegrableOn ((Iio R).indicator (fun r : ℝ => ((r^e : ℝ) : ℂ))) (Ioi 0) :=
    (integrableOn_indicator_iff measurableSet_Iio).mpr hpoly
  have hr : IntegrableOn (fun r : ℝ => (r^(n-1+(n+1)*n)) • f r) (Ioi 0) := by
    apply hind.congr_fun _ measurableSet_Ioi
    intro r hr
    by_cases hb : r < R
    · have hb' : r ∈ Iio R := Set.mem_Iio.mpr hb
      simp only [f, Set.indicator_of_mem hb', hdegree, Complex.real_smul]
      exact_mod_cast pow_sub₀ r (Set.mem_Ioi.mp hr).ne' he
    · simp [f, hb]
  have hi := integrable_shapeVandermonde_polar hn f hr
  have hreal := hi.re
  have hind' : Integrable ((ball (0 : ShapeSpace n) R).indicator
      (fun x => shapeVandermondeSq x / ‖x‖^(2*(j+1)))) := by
    apply hreal.congr
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : ‖x‖ < R
    · have hxb : x ∈ ball (0 : ShapeSpace n) R := mem_ball_zero_iff.mpr hx
      have hxr : ‖x‖ ∈ Iio R := Set.mem_Iio.mpr hx
      simp only [f, Set.indicator_of_mem hxb, Set.indicator_of_mem hxr,
        Complex.real_smul, ← Complex.ofReal_mul, div_eq_mul_inv]
      rfl
    · have hxb : x ∉ ball (0 : ShapeSpace n) R := fun h => hx (mem_ball_zero_iff.mp h)
      have hxr : ‖x‖ ∉ Iio R := fun h => hx (Set.mem_Iio.mp h)
      simp only [f, Set.indicator_of_notMem hxb, Set.indicator_of_notMem hxr,
        smul_zero, map_zero]
  exact (integrable_indicator_iff measurableSet_ball).mp hind'

end
end IsingBulk.First
