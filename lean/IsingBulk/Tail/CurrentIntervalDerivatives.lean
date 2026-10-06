import IsingBulk.Tail.CurrentDerivatives

/-! Differentiation through the full fixed [0,1] homotopy interval. Lambda is
a real integration variable, never an epsilon-dependent differentiation limit. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 1200000

abbrev CurrentShape (N : ℕ) := ℝ × (Fin N → ℝ)
def currentShapeDomain (N : ℕ) : Set (CurrentShape N) := Icc (0:ℝ) 1 ×ˢ angleBox N

def currentJointPoint (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (p : CurrentShape N) : Fin N → ℂ :=
  deformedPoint f r τ p.1 p.2

def currentJointNamedWeight (N : ℕ) (f : SelectorFunctions) (τ : ℝ) (q : Fin N)
    (p : CurrentShape N) : ℂ := namedCurrentAngularWeight N f τ p.1 q p.2

def currentJointWeight (N : ℕ) (f : SelectorFunctions) (τ : ℝ) (p : CurrentShape N) : ℂ :=
  ∑ q : Fin N, currentJointNamedWeight N f τ q p

theorem currentJointPoint_continuous (N : ℕ) (f : SelectorFunctions) (r τ : ℝ)
    (hp : Continuous f.p) (hm : Continuous f.m) : Continuous (currentJointPoint N f r τ) := by
  apply continuous_pi
  intro i
  unfold currentJointPoint deformedPoint retractionShift occupancy
  fun_prop

theorem currentJointNamedWeight_continuous (N : ℕ) (f : SelectorFunctions) (τ : ℝ) (q : Fin N)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a) :
    Continuous (currentJointNamedWeight N f τ q) := by
  have hpd : ContDiff ℝ ∞ (deriv f.p) := by apply ContDiff.deriv'; simpa using hp
  have hmd : ContDiff ℝ ∞ (deriv f.m) := by apply ContDiff.deriv'; simpa using hm
  have had : ContDiff ℝ ∞ (deriv f.a) := by apply ContDiff.deriv'; simpa using ha
  have hp' := hpd.continuous
  have hm' := hmd.continuous
  have ha' := had.continuous
  have hp0 := hp.continuous
  have hm0 := hm.continuous
  have ha0 := ha.continuous
  have hJ : Continuous (fun p : CurrentShape N => angularJacobian f τ p.1 p.2) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold angularJacobian retractionJacobian occupancy
    by_cases hij : i=j <;> simp only [hij,ite_true,ite_false] <;> fun_prop
  have hweight : Continuous (fun p : CurrentShape N => namedSelectorDerivative f q p.2) := by
    unfold namedSelectorDerivative
    fun_prop
  have hdet := hJ.matrix_det
  unfold currentJointNamedWeight namedCurrentAngularWeight
  fun_prop

theorem currentJointWeight_continuous (N : ℕ) (f : SelectorFunctions) (τ : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a) :
    Continuous (currentJointWeight N f τ) :=
  continuous_finsetSum _ (fun q _ => currentJointNamedWeight_continuous N f τ q hp hm ha)

/-- All finite source derivatives commute with the complete fixed lambda
integral. This theorem supplies the exact differentiated Stokes correction
before the small/large lambda split is introduced. -/
theorem currentIntegral_iteratedDeriv_integrable (N : ℕ) (hN : 0 < N) (f : SelectorFunctions)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0)
    (k : ℕ) {s : ℂ} (hs : s ∈ dampingDomain r) :
    IntervalIntegrable (fun lam : ℝ => differentiatedCurrentSlice N f r τ lam k s) volume 0 1 ∧
    iteratedDeriv k (currentIntegral N f r τ) s =
      ∫ lam : ℝ in 0..1, differentiatedCurrentSlice N f r τ lam k s := by
  let U := dampingDomain r
  let K := currentShapeDomain N
  let μ : Measure (CurrentShape N) := volume.prod volume
  let psi := currentJointPoint N f r τ
  let chi := currentJointWeight N f τ
  let chiq := currentJointNamedWeight N f τ
  let F := continuedContourDensity N
  let G := fun z : ℂ => ∫ p in K, chi p*F (z,psi p) ∂μ
  have hU : IsOpen U := dampingDomain_isOpen r
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hpsi : Continuous psi := currentJointPoint_continuous N f r τ hp.continuous hm.continuous
  have hchi : Continuous chi := currentJointWeight_continuous N f τ hp hm ha
  have hchiq (q : Fin N) : Continuous (chiq q) := currentJointNamedWeight_continuous N f τ q hp hm ha
  have hupper (z : ℂ) (hz : z ∈ U) (p : CurrentShape N) (hpK : p ∈ K) (i : Fin N) :
      0 < (sourceW z (psi p i)).im := by
    have hbase := sourceW_upper_of_margin hr hr1 hz.2 (deformedPoint_zero_norm f hr.le τ p.2 i)
    exact hbase.trans_le (deformed_sourceW_im_ge hN f hr hτ hpK.1.1 p.2 z hp0 hm0 hps hms i)
  have hF (z : ℂ) (hz : z ∈ U) (p : CurrentShape N) (hpK : p ∈ K) :
      AnalyticAt ℂ F (z,psi p) := by
    have hY := homotopy_y_gap_nonzero hN f hr hr1 hτ hpK.1.1 p.2 hp0 hm1
    have hZ : 1-coordinateProduct (fun i => selectedContinuedRoot z (psi p i)) ≠ 0 := by
      apply one_sub_coordinateProduct_ne_zero hN
      intro i
      unfold selectedContinuedRoot
      rw [continuedRoot_eq_interiorRoot (hupper z hz p hpK i)]
      exact interiorRoot_norm_lt_one (hupper z hz p hpK i)
    exact continuedContourDensity_analyticAt (p := (z,psi p)) hz.1
      (deformedPoint_nonzero f hr.ne' τ p.1 p.2)
      (fun i => Or.inl (Or.inl (hupper z hz p hpK i))) hY hZ
  have hpoint (j : ℕ) (z : ℂ) (hz : z ∈ U) (p : CurrentShape N) (hpK : p ∈ K) (q : Fin N) :
      iteratedDeriv j (fun w => namedCurrentDensity f r τ p.1 w q p.2) z =
        chiq q p*jointParameterJet F j (z,psi p) := by
    have he : (fun w => namedCurrentDensity f r τ p.1 w q p.2) =ᶠ[𝓝 z]
        (fun w => chiq q p*F (w,psi p)) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      change namedCurrentDensity f r τ p.1 w q p.2 =
        namedCurrentAngularWeight N f τ p.1 q p.2 *
          continuedContourDensity N (w,deformedPoint f r τ p.1 p.2)
      rw [← continuedNamedCurrentDensity_weighted f r τ p.1 w q p.2]
      unfold continuedNamedCurrentDensity namedCurrentDensity
      rw [continuedPulledDensity_eq_original f r τ p.1 w p.2 (hupper w hw p hpK)]
    have he' := he.iteratedDeriv_eq j
    rw [iteratedDeriv_const_mul_field] at he'
    simpa only [jointParameterJet_eq,iteratedDeriv_eq_iterate] using he'
  have hJcont (j : ℕ) (z : ℂ) (hz : z ∈ U) :
      ContinuousOn (fun p => jointParameterJet F j (z,psi p)) K := by
    intro p hpK
    exact ((jointParameterJet_analyticAt (hF z hz p hpK) j).continuousAt.comp
      (f := fun p => (z,psi p)) (continuous_const.prodMk hpsi).continuousAt).continuousWithinAt
  have hqcont (j : ℕ) (z : ℂ) (hz : z ∈ U) (q : Fin N) :
      ContinuousOn (fun p => chiq q p*jointParameterJet F j (z,psi p)) K :=
    (hchiq q).continuousOn.mul (hJcont j z hz)
  have hcont (j : ℕ) (z : ℂ) (hz : z ∈ U) :
      ContinuousOn (fun p => chi p*jointParameterJet F j (z,psi p)) K :=
    hchi.continuousOn.mul (hJcont j z hz)
  have hinner (j : ℕ) (z : ℂ) (hz : z ∈ U) (lam : ℝ) (hlam : lam ∈ Icc (0:ℝ) 1) :
      (∫ θ in angleBox N, chi (lam,θ)*jointParameterJet F j (z,psi (lam,θ))) =
        differentiatedCurrentSlice N f r τ lam j z := by
    have hqint (q : Fin N) : IntegrableOn (fun θ : Fin N → ℝ =>
        chiq q (lam,θ)*jointParameterJet F j (z,psi (lam,θ))) (angleBox N) := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      exact (hqcont j z hz q).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => ⟨hlam,hθ⟩)
    change (∫ θ in angleBox N, (∑ q, chiq q (lam,θ))*jointParameterJet F j (z,psi (lam,θ))) = _
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun q _ => hqint q)]
    apply Finset.sum_congr rfl
    intro q _
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    exact (hpoint j z hz (lam,θ) ⟨hlam,hθ⟩ q).symm
  have hprod (j : ℕ) (z : ℂ) (hz : z ∈ U) :
      (∫ p in K, chi p*jointParameterJet F j (z,psi p) ∂μ) =
        ∫ lam : ℝ in 0..1, differentiatedCurrentSlice N f r τ lam j z := by
    have hint : IntegrableOn (fun p => chi p*jointParameterJet F j (z,psi p)) K μ :=
      ContinuousOn.integrableOn_compact hK (hcont j z hz)
    change (∫ p in Icc (0:ℝ) 1 ×ˢ angleBox N, chi p*jointParameterJet F j (z,psi p)
      ∂(volume.prod volume)) = _
    rw [setIntegral_prod _ hint]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro lam hlam
    exact hinner j z hz lam hlam
  have he : currentIntegral N f r τ =ᶠ[𝓝 s] G := by
    filter_upwards [hU.mem_nhds hs] with z hz
    simpa only [G,jointParameterJet,Function.iterate_zero_apply,differentiatedCurrentSlice,
      iteratedDeriv_zero,currentIntegral] using (hprod 0 z hz).symm
  have hjet := compact_analytic_shape_integral_iteratedDeriv (μ := μ) hK hU F psi hpsi chi hchi hF k s hs
  have hjint : IntegrableOn (fun p => chi p*jointParameterJet F k (s,psi p)) K μ :=
    ContinuousOn.integrableOn_compact hK (hcont k s hs)
  have hjprod : Integrable (fun p : CurrentShape N => chi p*jointParameterJet F k (s,psi p))
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (angleBox N))) := by
    rw [Measure.prod_restrict]
    exact hjint
  have hjouter := hjprod.integral_prod_left
  have hjsource : IntegrableOn (fun lam : ℝ => differentiatedCurrentSlice N f r τ lam k s)
      (Icc (0:ℝ) 1) := by
    apply hjouter.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lam hlam
    exact hinner k s hs lam hlam
  have hjinterval : IntervalIntegrable (fun lam : ℝ => differentiatedCurrentSlice N f r τ lam k s)
      volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr
      (hjsource.mono_set Ioc_subset_Icc_self)
  refine ⟨hjinterval,?_⟩
  calc
    _ = iteratedDeriv k G s := he.iteratedDeriv_eq k
    _ = ∫ p in K, chi p*jointParameterJet F k (s,psi p) ∂μ := by
      simpa only [G,K,currentShapeDomain,angleBox,jointParameterJet_eq,iteratedDeriv_eq_iterate] using hjet
    _ = _ := hprod k s hs

/-- Equality-only compatibility endpoint. -/
theorem currentIntegral_iteratedDeriv (N : ℕ) (hN : 0 < N) (f : SelectorFunctions)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0)
    (k : ℕ) {s : ℂ} (hs : s ∈ dampingDomain r) :
    iteratedDeriv k (currentIntegral N f r τ) s =
      ∫ lam : ℝ in 0..1, differentiatedCurrentSlice N f r τ lam k s := by
  exact (currentIntegral_iteratedDeriv_integrable N hN f hr hr1 hτ hp hm ha hp0 hm0 hm1 hps hms k hs).2

end
end IsingBulk.Tail
