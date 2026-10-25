import IsingBulk.Joint.RegularEdges.CompactFullTails
import IsingBulk.Joint.RegularEdges.FullDifferentiatedTail
import IsingBulk.Joint.FormFactors.CompactIntegralJets

/-! # Actual coefficient mixed jets for independent complex edge parameters -/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology BigOperators

def independentComplexDensity {N : ℕ} (b : ℝ) (p : NumeratorParameter × (Fin N→ℂ)) : ℂ :=
  complexDensity b (fun _ => p.1.2.1) (fun _ => p.1.2.2) p.1.1 p.2

def independentAngularCoefficient (n : ℕ) (b : ℝ) (p : NumeratorParameter) : ℂ :=
  angularCoefficient n b (fun _ => p.2.1) (fun _ => p.2.2) p.1

def independentUpperDomain : Set NumeratorParameter := {p | 0<p.1.im ∧ 0<p.2.1.im ∧ p.2.2≠0}

theorem independentUpperDomain_isOpen : IsOpen independentUpperDomain :=
  (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)).inter
    ((isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_fst.comp continuous_snd))).inter
      (isOpen_ne_fun (continuous_snd.comp continuous_snd) continuous_const))

theorem independentComplexDensity_analyticAt {N : ℕ} (hN : 0<N) {b : ℝ}
    {v : NumeratorParameter} (hu : 0<v.1.im) (hB : 0<v.2.1.im) (hS : v.2.2≠0)
    (q : Fin N→ℝ) :
    AnalyticAt ℂ (independentComplexDensity b) (v,fun i => (q i:ℂ)) := by
  let p := (v,fun i => (q i:ℂ))
  have dq (i : Fin N) : AnalyticAt ℂ (fun x : NumeratorParameter × (Fin N → ℂ) => x.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dB : AnalyticAt ℂ (fun x : NumeratorParameter × (Fin N → ℂ) => x.1.2.1) p :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have dS : AnalyticAt ℂ (fun x : NumeratorParameter × (Fin N → ℂ) => x.1.2.2) p :=
    analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
  have dr (i : Fin N) : AnalyticAt ℂ
      (fun x : NumeratorParameter × (Fin N → ℂ) => edgeComplexRoot b (fun _ => x.1.2.1) x.1.1 (x.2 i)) p := by
    have him := Transverse.dispersion_im_pos (b := b) hu hB (q i)
    apply AnalyticAt.fun_comp_of_eq
      (f := fun x : NumeratorParameter × (Fin N → ℂ) => (b:ℂ)+x.1.1+x.1.2.1*(1-Complex.cos (x.2 i)))
      (g := continuedRoot) (continuedRoot_analyticAt (Or.inl (Or.inl him)))
      ((analyticAt_const.add (analyticAt_fst.comp analyticAt_fst)).add
        (dB.mul (analyticAt_const.sub (Complex.analyticAt_cos.comp (dq i)))))
    simp [dispersion,Complex.ofReal_cos,p]
  have hn (i : Fin N) : ‖edgeComplexRoot b (fun _ => v.2.1) v.1 (q i:ℂ)‖ < 1 := by
    simpa using edgeRoot_norm_lt_one (b := b) (B := fun _ => v.2.1) hu hB (q i)
  have hpair (i j : Fin N) : 1-edgeComplexRoot b (fun _ => v.2.1) v.1 (q i:ℂ)*edgeComplexRoot b (fun _ => v.2.1) v.1 (q j:ℂ)≠0 :=
    one_sub_mul_ne_zero_of_norm_lt_one (hn i) (hn j)
  have hZ : 1-∏ i,edgeComplexRoot b (fun _ => v.2.1) v.1 (q i:ℂ)≠0 :=
    one_sub_coordinateProduct_ne_zero hN hn
  have dZ := Finset.univ.analyticAt_fun_prod (fun i _ => dr i)
  unfold independentComplexDensity complexDensity
  refine (((((dB.pow _).mul ((dS.inv hS).pow _)).mul ?_).mul ?_)).mul
    ((analyticAt_const.add dZ).div (analyticAt_const.sub dZ) hZ)
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dr i)).div (analyticAt_const.sub ((dr i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  · apply (firstStrictPairs N).analyticAt_fun_prod
    intro ij _
    exact ((((analyticAt_const.mul (dr ij.1)).mul (dr ij.2)).mul
      ((Complex.analyticAt_sin.comp (((dq ij.1).sub (dq ij.2)).div_const)).pow 2))).div
        ((analyticAt_const.sub ((dr ij.1).mul (dr ij.2))).pow 2) (pow_ne_zero _ (hpair ij.1 ij.2))


@[simp] theorem independentComplexDensity_real {N : ℕ} (b : ℝ) (p : NumeratorParameter)
    (q : Fin N→ℝ) :
    independentComplexDensity b (p,fun i => (q i:ℂ))=
      edgeAngularDensity b (fun _ => p.2.1) (fun _ => p.2.2) p.1 q :=
  complexDensity_real b _ _ _ q

theorem independentComplexDensity_eq_full {N : ℕ} (hN : 0<N) {b : ℝ}
    {p : NumeratorParameter} (hp : p∈independentUpperDomain) (q : Fin N→ℝ) :
    independentComplexDensity b (p,fun i => (q i:ℂ))=independentFullIntegrand b p q := by
  rw [independentComplexDensity_real]
  exact angularDensity_eq_fullIntegrand hN hp.1 hp.2.1 q

theorem independentFullIntegrand_centered {n : ℕ} {b : ℝ} {p : NumeratorParameter}
    (hp : p∈independentUpperDomain) (q : Fin n→ℝ) :
    independentFullIntegrand b p (centeredFullAngles n q)=
      independentComplexDensity b (p,fun i => ((shapeExtend q i:ℝ):ℂ)) := by
  rw [←independentComplexDensity_eq_full (by omega) hp,independentComplexDensity_real,
    independentComplexDensity_real]
  exact angularDensity_wrapAngle b _ _ _ (shapeExtend q)

theorem edgeAngleMeasure_integral_eq_vector {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (n : ℕ) (f : (Fin n→ℝ) → G) :
    (∫ q, f q ∂Measure.pi (fun _ : Fin n => edgeAngleMeasure))=
      ((2*Real.pi:ℂ)⁻¹)^n • ∫ q in edgeCenteredCube n, f q := by
  let _ := NormedSpace.restrictScalars ℝ ℂ G
  rw [edgeAngleMeasure_pi_eq,integral_smul_measure]
  simp only [ENNReal.toReal_pow,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity : 0≤2*Real.pi),
    RCLike.real_smul_eq_coe_smul (K := ℂ),edgeCenteredCube]
  change (Complex.ofReal ((2*Real.pi)⁻¹^n)) • _ = _
  push_cast
  rfl

/-- Finite Frechet smoothness is obtained from the actual compact analytic
kernel, independently of the tail bound. -/
theorem independentAngularCoefficient_contDiffAt (n j : ℕ) {b : ℝ}
    {p : NumeratorParameter} (hp : p∈independentUpperDomain) :
    ContDiffAt ℂ j (independentAngularCoefficient n b) p := by
  let K := edgeCenteredCube n
  let psi : (Fin n→ℝ) → (Fin (n+1)→ℂ) := fun q i => ((shapeExtend q i:ℝ):ℂ)
  let F : NumeratorParameter × (Fin (n+1)→ℂ) → ℂ := independentComplexDensity b
  have hpsi : Continuous psi := by unfold psi shapeExtend; fun_prop
  have hF : ∀ v∈independentUpperDomain, ∀ q∈K, AnalyticAt ℂ F (v,psi q) := by
    intro v hv q _
    exact independentComplexDensity_analyticAt (by omega) hv.1 hv.2.1 hv.2.2 (shapeExtend q)
  have he : independentAngularCoefficient n b =
      (fun v => edgeCoefficientNormalization n • ∫ q in K, F (v,psi q)) := by
    funext v
    simp only [independentAngularCoefficient,angularCoefficient,F,psi,
      independentComplexDensity_real,K,smul_eq_mul]
  rw [he]
  exact (FormFactors.compact_analytic_integral_contDiffAt j (μ := volume)
    (K := K) isCompact_Icc independentUpperDomain_isOpen F psi hpsi hF hp).const_smul _

/-- Exact differentiation of the literal complete coefficient in all three
independent complex parameters, with its original factorial normalization. -/
theorem independentAngularCoefficient_mixed_jets (n j : ℕ) {b : ℝ}
    {p : NumeratorParameter} (hp : p∈independentUpperDomain) :
    iteratedFDeriv ℂ j (independentAngularCoefficient n b) p =
      (((n+1).factorial:ℂ)⁻¹) • ∫ q : Fin n→ℝ,
        iteratedFDeriv ℂ j (fun x => independentFullIntegrand b x (centeredFullAngles n q)) p
          ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  let K := edgeCenteredCube n
  let psi : (Fin n→ℝ) → (Fin (n+1)→ℂ) := fun q i => ((shapeExtend q i:ℝ):ℂ)
  let F : NumeratorParameter × (Fin (n+1)→ℂ) → ℂ := independentComplexDensity b
  have hpsi : Continuous psi := by unfold psi shapeExtend; fun_prop
  have hF : ∀ v∈independentUpperDomain, ∀ q∈K, AnalyticAt ℂ F (v,psi q) := by
    intro v hv q _
    exact independentComplexDensity_analyticAt (by omega) hv.1 hv.2.1 hv.2.2 (shapeExtend q)
  have he : independentAngularCoefficient n b =
      (fun v => edgeCoefficientNormalization n • ∫ q in K, F (v,psi q)) := by
    funext v
    simp only [independentAngularCoefficient,angularCoefficient,F,psi,
      independentComplexDensity_real,K,smul_eq_mul]
  have hcont := FormFactors.compact_analytic_integral_contDiffAt j (μ := volume)
    (K := K) isCompact_Icc independentUpperDomain_isOpen F psi hpsi hF hp
  rw [he,iteratedFDeriv_const_smul_apply' hcont]
  rw [FormFactors.compact_analytic_integral_iteratedFDeriv j (μ := volume) (K := K) isCompact_Icc
    independentUpperDomain_isOpen F psi hpsi hF hp]
  have heq : (∫ q in K, iteratedFDeriv ℂ j (fun v => F (v,psi q)) p)=
      ∫ q in K, iteratedFDeriv ℂ j (fun v => independentFullIntegrand b v (centeredFullAngles n q)) p := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro q _
    have hlocal : (fun v => F (v,psi q)) =ᶠ[𝓝 p]
        (fun v => independentFullIntegrand b v (centeredFullAngles n q)) := by
      filter_upwards [independentUpperDomain_isOpen.mem_nhds hp] with v hv
      exact (independentFullIntegrand_centered hv q).symm
    exact (hlocal.iteratedFDeriv ℂ j).eq_of_nhds
  rw [heq,edgeCoefficientNormalization,mul_smul]
  congr 1
  exact (edgeAngleMeasure_integral_eq_vector n _).symm

/-- Genuine coefficient derivatives, not merely formal integrand jets, have
summable full-particle tails uniformly on one compact-family polydisk. -/
theorem compact_actual_coefficient_summable_mixed_jets {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ j : ℕ, ∃ G : ℕ→ℝ,
      Summable G ∧ (∀ k, 0≤G k) ∧
      ∀ v∈K, ∀ x∈ball ((0:ℂ),v) δ, 0<x.1.im → ∀ k : ℕ,
      ‖iteratedFDeriv ℂ j (independentAngularCoefficient (2*j+3+k) b) x‖≤G k := by
  obtain ⟨δ,hδ,hall⟩ := compact_full_tail_summable_mixed_jets hb hK hB hS
  obtain ⟨η,c,hη,_,hroot⟩ := compact_roots_polydisks hb hK hB hS
  refine ⟨min δ η,lt_min hδ hη,?_⟩
  intro j
  obtain ⟨G,hG,hG0,hbound⟩ := hall j
  refine ⟨G,hG,hG0,?_⟩
  intro v hv x hx hi k
  have hxδ := ball_subset_ball (min_le_left δ η) hx
  have hxη := ball_subset_ball (min_le_right δ η) hx
  have hupper : x∈independentUpperDomain := ⟨hi,(hroot v hv).1 x hxη⟩
  rw [independentAngularCoefficient_mixed_jets _ j hupper,norm_smul]
  have hfac : ‖(((2*j+3+k+1).factorial:ℂ)⁻¹)‖≤1 := by
    simp only [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (2*j+3+k+1))
  exact (mul_le_mul_of_nonneg_right hfac (norm_nonneg _)).trans
    (by simpa only [one_mul] using hbound v hv x hxδ hi k)

/-- The full jet series is explicitly split into its finite low-particle part
and the complete summable high-particle tail. No low order is omitted. -/
theorem compact_actual_jets_finite_tail_split {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ j : ℕ, ∃ G : ℕ→ℝ,
      Summable G ∧ (∀ k, 0≤G k) ∧
      ∀ v∈K, ∀ x∈ball ((0:ℂ),v) δ, 0<x.1.im →
      Summable (fun n => iteratedFDeriv ℂ j (independentAngularCoefficient n b) x) ∧
      (∑' n, iteratedFDeriv ℂ j (independentAngularCoefficient n b) x)=
        (∑ n∈Finset.range (2*j+3), iteratedFDeriv ℂ j (independentAngularCoefficient n b) x)+
        ∑' k, iteratedFDeriv ℂ j (independentAngularCoefficient (2*j+3+k) b) x ∧
      ∀ k, ‖iteratedFDeriv ℂ j (independentAngularCoefficient (2*j+3+k) b) x‖≤G k := by
  obtain ⟨δ,hδ,hall⟩ := compact_actual_coefficient_summable_mixed_jets hb hK hB hS
  refine ⟨δ,hδ,?_⟩
  intro j
  obtain ⟨G,hG,hG0,hbound⟩ := hall j
  refine ⟨G,hG,hG0,?_⟩
  intro v hv x hx hi
  have htail : Summable (fun k => iteratedFDeriv ℂ j (independentAngularCoefficient (2*j+3+k) b) x) :=
    Summable.of_norm_bounded hG (hbound v hv x hx hi)
  have hs : Summable (fun n => iteratedFDeriv ℂ j (independentAngularCoefficient n b) x) :=
    (summable_nat_add_iff (2*j+3)).mp (by simpa only [Nat.add_comm] using htail)
  refine ⟨hs,?_,hbound v hv x hx hi⟩
  simpa only [Nat.add_comm] using (hs.sum_add_tsum_nat_add (2*j+3)).symm

end
end IsingBulk.Joint.RegularEdges
