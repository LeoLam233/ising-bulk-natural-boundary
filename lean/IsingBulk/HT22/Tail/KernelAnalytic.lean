import IsingBulk.HT22.Tail.ScalarTransport

/-! # Joint regularity of the literal odd rational kernel

At positive epsilon the actual interior physical roots separate all pair
denominators. The removable limiting double-branch factor is dealt with
separately by PairFactorization, not assumed here.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators Topology Matrix.Norms.Elementwise

/-- Pointwise joint analyticity of the ordinary rational block from the
actual analytic inverse and the interior phase, at every partial collision. -/
theorem regularOrdinaryKernel_analyticAt {N : ℕ} (t : ℂ) (v : Fin N → ℂ)
    (hU : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,v i))
    (hroot : ∀ i, ‖Complex.exp (-Complex.I*regularPhase t (v i))‖<1) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => regularOrdinaryKernel z.1 z.2) (t,v) := by
  have hcoord (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => z.2 i) (t,v) :=
    (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt (t,v))
  have hu (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => regularInverse z.1 (z.2 i)) (t,v) :=
    AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g := fun z : ℂ × ℂ => regularInverse z.1 z.2) (hU i)
      (analyticAt_fst.prod (hcoord i))
  have hy (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => Complex.exp (Complex.I*regularInverse z.1 (z.2 i))) (t,v) :=
    analyticAt_cexp.comp (analyticAt_const.mul (hu i))
  have hz (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => Complex.exp (-Complex.I*regularPhase z.1 (z.2 i))) (t,v) :=
    analyticAt_cexp.comp (analyticAt_const.mul ((hcoord i).sub (hu i)))
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  have hden : 1-Complex.exp (-Complex.I*regularPhase t (v i))*
      Complex.exp (-Complex.I*regularPhase t (v j)) ≠ 0 := by
    intro he
    have hn : ‖Complex.exp (-Complex.I*regularPhase t (v i))*
        Complex.exp (-Complex.I*regularPhase t (v j))‖<1 := by
      rw [norm_mul]
      calc
        _ ≤ ‖Complex.exp (-Complex.I*regularPhase t (v i))‖*1 :=
          mul_le_mul_of_nonneg_left (hroot j).le (norm_nonneg _)
        _ < 1 := by simpa using hroot i
    rw [(sub_eq_zero.mp he).symm,norm_one] at hn
    exact (lt_irrefl _ hn)
  exact analyticAt_const.mul (((hy i).sub (hy j)).fun_div
    (analyticAt_const.sub ((hz i).mul (hz j))) hden)

/-- Constant ghost entries are analytic without borrowing any LT kernel. -/
theorem regularBorderedKernel_analyticAt {N : ℕ} (t : ℂ) (v : Fin N → ℂ)
    (hU : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,v i))
    (hroot : ∀ i, ‖Complex.exp (-Complex.I*regularPhase t (v i))‖<1) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => regularBorderedKernel z.1 z.2) (t,v) := by
  have hK := regularOrdinaryKernel_analyticAt t v hU hroot
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  cases i using Fin.cases <;> cases j using Fin.cases
  · exact analyticAt_const
  · exact analyticAt_const
  · exact analyticAt_const
  · rename_i i j
    exact analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hK i) j

/-- Primitive positive-epsilon source geometry discharges every inverse
analyticity and pair-denominator hypothesis above. -/
theorem source_regularOrdinaryKernel_analyticAt {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (t : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace t).re)
    (hSδ : (temperatureTrace t).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace t-Complex.cos (deformedAngles τ p m θ i)).im) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => regularOrdinaryKernel z.1 z.2)
      (t,sourceCoordinate τ p m t θ) := by
  have hw (i : Fin N) : (deformedAngles τ p m θ i).re=θ i := by
    simp [deformedAngles,Complex.mul_re]
  apply regularOrdinaryKernel_analyticAt
  · intro i
    exact global_one_sided_joint_analytic t (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by rw [hw]; exact (hθ i).1) (by rw [hw]; exact (hθ i).2) (hW i)
  · intro i
    rw [show regularPhase t (sourceCoordinate τ p m t θ i)=
      physicalPhase t (deformedAngles τ p m θ i) from
      global_one_sided_phase t (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
        (by rw [hw]; exact (hθ i).1) (by rw [hw]; exact (hθ i).2) (hW i),
      physicalPhase_root t _ (hW i)]
    exact physicalRoot_inside (Or.inl (hW i).ne')

/-- Primitive positive-epsilon source geometry discharges every inverse
analyticity and pair-denominator hypothesis above. -/
theorem source_regularBorderedKernel_analyticAt {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (t : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace t).re)
    (hSδ : (temperatureTrace t).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace t-Complex.cos (deformedAngles τ p m θ i)).im) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => regularBorderedKernel z.1 z.2)
      (t,sourceCoordinate τ p m t θ) := by
  have hw (i : Fin N) : (deformedAngles τ p m θ i).re=θ i := by
    simp [deformedAngles,Complex.mul_re]
  apply regularBorderedKernel_analyticAt
  · intro i
    exact global_one_sided_joint_analytic t (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by rw [hw]; exact (hθ i).1) (by rw [hw]; exact (hθ i).2) (hW i)
  · intro i
    rw [show regularPhase t (sourceCoordinate τ p m t θ i)=
      physicalPhase t (deformedAngles τ p m θ i) from
      global_one_sided_phase t (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
        (by rw [hw]; exact (hθ i).1) (by rw [hw]; exact (hθ i).2) (hW i),
      physicalPhase_root t _ (hW i)]
    exact physicalRoot_inside (Or.inl (hW i).ne')

end
end IsingBulk.HT22.Tail
