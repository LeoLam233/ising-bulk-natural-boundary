import IsingBulk.First.ShapeRadialValue

/-! Analytic transfer of a positive-real radial evaluation to the source boundary.
The positive-real identity remains an explicit intermediate premise until the
separate scalar evaluation theorem is applied. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem shapeRadialIntegral_eq_value_of_positive (k : ℕ) {Q : ℝ} (hQ : 0 < Q)
    (hpositive : ∀ c : ℝ, 0 < c → shapeRadialIntegral k Q c = shapeRadialValue k Q c) :
    Set.EqOn (shapeRadialIntegral k Q) (shapeRadialValue k Q) {c : ℂ | 0 < c.re} :=
  analytic_rightHalfPlane_eq (shapeRadialIntegral_analyticOnNhd k hQ)
    (shapeRadialValue_analyticOnNhd k Q) hpositive

/-- Boundary continuation follows from the actual radial DCT and continuity of
principal powers at the lower imaginary coefficient, which lies on the slit plane. -/
theorem shapeRadialIntegral_boundary_eq_of_positive (k : ℕ) {Q d : ℝ}
    (hQ : 0 < Q) (hd : 0 < d)
    (hpositive : ∀ c : ℝ, 0 < c → shapeRadialIntegral k Q c = shapeRadialValue k Q c) :
    shapeRadialIntegral k Q (-Complex.I*d) = shapeRadialValue k Q (-Complex.I*d) := by
  have hi := (shapeRadialIntegral_boundary_tendsto k hQ hd).mono_left
    (nhdsWithin_mono 0 (Set.Ioi_subset_Ici_self (a := (0 : ℝ))))
  have hc : ContinuousAt (fun δ : ℝ => (δ : ℂ)-Complex.I*d) 0 :=
    Complex.continuous_ofReal.continuousAt.sub continuousAt_const
  have hv : Tendsto (fun δ : ℝ => shapeRadialValue k Q ((δ : ℂ)-Complex.I*d))
      (𝓝[Ioi 0] 0) (𝓝 (shapeRadialValue k Q (-Complex.I*d))) := by
    have hc' : Tendsto (fun δ : ℝ => (δ : ℂ)-Complex.I*d) (𝓝 0) (𝓝 (-Complex.I*d)) := by
      simpa using hc.tendsto
    have h := (shapeRadialValue_boundary_continuous k Q hd).tendsto.comp hc' 
    simpa only [Function.comp_def, Complex.ofReal_zero, zero_sub, neg_mul] using
      h.mono_left nhdsWithin_le_nhds
  have he : (fun δ : ℝ => shapeRadialIntegral k Q ((δ : ℂ)-Complex.I*d)) =ᶠ[𝓝[Ioi 0] 0]
      (fun δ : ℝ => shapeRadialValue k Q ((δ : ℂ)-Complex.I*d)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply shapeRadialIntegral_eq_value_of_positive k hQ hpositive
    simpa using hδ
  exact tendsto_nhds_unique hi (hv.congr' he.symm)

end
end IsingBulk.First
