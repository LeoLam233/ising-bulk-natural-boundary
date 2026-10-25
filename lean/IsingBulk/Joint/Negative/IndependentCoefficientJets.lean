import IsingBulk.Joint.RegularEdges.IndependentCoefficientJets
import IsingBulk.Joint.Negative.FamilyUpperJetMajorant
import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsActual
import IsingBulk.Joint.Negative.FamilyBoundaryIdentity
import IsingBulk.Joint.Negative.UpperPeriod

/-! # Actual independent negative coefficients and complete interior jets -/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
  IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
  IsingBulk.Joint.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology BigOperators

def independentNegativeCoefficient (n : ℕ) (b : ℝ) (v : NumeratorParameter) : ℂ :=
  (edgeCoefficientNormalization n*(-1:ℂ)^((n+1).choose 2)) •
    ∫ q in edgeCenteredCube n, independentComplexDensity b
      (v,fun i => ((negativeUnwrappedAngles n q i:ℝ):ℂ))

theorem independentFullIntegrand_negative {n : ℕ} {b : ℝ} {p : NumeratorParameter}
    (hp : p∈independentUpperDomain) (q : Fin n→ℝ) :
    independentFullIntegrand b p (negativeShiftedAngles n q)=
      independentComplexDensity b (p,fun i => ((negativeUnwrappedAngles n q i:ℝ):ℂ)) := by
  rw [←independentComplexDensity_eq_full (by omega) hp,independentComplexDensity_real,
    independentComplexDensity_real]
  exact angularDensity_wrapAngle b _ _ _ (negativeUnwrappedAngles n q)

/-- Finite Frechet smoothness is obtained from the actual compact analytic
kernel, independently of the tail bound. -/
theorem independentNegativeCoefficient_contDiffAt (n j : ℕ) {b : ℝ}
    {p : NumeratorParameter} (hp : p∈independentUpperDomain) :
    ContDiffAt ℂ j (independentNegativeCoefficient n b) p := by
  let K := edgeCenteredCube n
  let psi : (Fin n→ℝ) → (Fin (n+1)→ℂ) := fun q i => ((negativeUnwrappedAngles n q i:ℝ):ℂ)
  let F : NumeratorParameter × (Fin (n+1)→ℂ) → ℂ := independentComplexDensity b
  have hpsi : Continuous psi := by
    apply continuous_pi
    intro i
    exact Complex.continuous_ofReal.comp ((continuous_apply i).comp (negativeUnwrappedAngles_continuous n))
  have hF : ∀ v∈independentUpperDomain, ∀ q∈K, AnalyticAt ℂ F (v,psi q) := by
    intro v hv q _
    exact independentComplexDensity_analyticAt (by omega) hv.1 hv.2.1 hv.2.2 (negativeUnwrappedAngles n q)
  have he : independentNegativeCoefficient n b =
      (fun v => (edgeCoefficientNormalization n*(-1:ℂ)^((n+1).choose 2)) • ∫ q in K, F (v,psi q)) := by
    funext v
    rfl
  rw [he]
  exact (FormFactors.compact_analytic_integral_contDiffAt j (μ := volume)
    (K := K) isCompact_Icc independentUpperDomain_isOpen F psi hpsi hF hp).const_smul _

/-- Exact differentiation of the literal complete coefficient in all three
independent complex parameters, with its original factorial normalization. -/
theorem independentNegativeCoefficient_mixed_jets (n j : ℕ) {b : ℝ}
    {p : NumeratorParameter} (hp : p∈independentUpperDomain) :
    iteratedFDeriv ℂ j (independentNegativeCoefficient n b) p =
      ((((n+1).factorial:ℂ)⁻¹)*(-1:ℂ)^((n+1).choose 2)) • ∫ q : Fin n→ℝ,
        iteratedFDeriv ℂ j (fun x => independentFullIntegrand b x (negativeShiftedAngles n q)) p
          ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  let K := edgeCenteredCube n
  let psi : (Fin n→ℝ) → (Fin (n+1)→ℂ) := fun q i => ((negativeUnwrappedAngles n q i:ℝ):ℂ)
  let F : NumeratorParameter × (Fin (n+1)→ℂ) → ℂ := independentComplexDensity b
  have hpsi : Continuous psi := by
    apply continuous_pi
    intro i
    exact Complex.continuous_ofReal.comp ((continuous_apply i).comp (negativeUnwrappedAngles_continuous n))
  have hF : ∀ v∈independentUpperDomain, ∀ q∈K, AnalyticAt ℂ F (v,psi q) := by
    intro v hv q _
    exact independentComplexDensity_analyticAt (by omega) hv.1 hv.2.1 hv.2.2 (negativeUnwrappedAngles n q)
  have he : independentNegativeCoefficient n b =
      (fun v => (edgeCoefficientNormalization n*(-1:ℂ)^((n+1).choose 2)) • ∫ q in K, F (v,psi q)) := by
    funext v
    rfl
  have hcont := FormFactors.compact_analytic_integral_contDiffAt j (μ := volume)
    (K := K) isCompact_Icc independentUpperDomain_isOpen F psi hpsi hF hp
  rw [he,iteratedFDeriv_const_smul_apply' hcont]
  rw [FormFactors.compact_analytic_integral_iteratedFDeriv j (μ := volume) (K := K) isCompact_Icc
    independentUpperDomain_isOpen F psi hpsi hF hp]
  have heq : (∫ q in K, iteratedFDeriv ℂ j (fun v => F (v,psi q)) p)=
      ∫ q in K, iteratedFDeriv ℂ j (fun v => independentFullIntegrand b v (negativeShiftedAngles n q)) p := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro q _
    have hlocal : (fun v => F (v,psi q)) =ᶠ[𝓝 p]
        (fun v => independentFullIntegrand b v (negativeShiftedAngles n q)) := by
      filter_upwards [independentUpperDomain_isOpen.mem_nhds hp] with v hv
      exact (independentFullIntegrand_negative hv q).symm
    exact (hlocal.iteratedFDeriv ℂ j).eq_of_nhds
  rw [heq,edgeAngleMeasure_integral_eq_vector n _,smul_smul]
  congr 1
  unfold edgeCoefficientNormalization
  ring

/-- Genuine coefficient derivatives, not merely formal integrand jets, have
summable full-particle tails uniformly on one compact-family polydisk. -/
theorem compact_negative_coefficient_summable_mixed_jets {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ j : ℕ, ∃ G : ℕ→ℝ,
      Summable G ∧ (∀ k, 0≤G k) ∧
      ∀ v∈K, ∀ x∈ball ((0:ℂ),v) δ, 0<x.1.im → ∀ k : ℕ,
      ‖iteratedFDeriv ℂ j (independentNegativeCoefficient (2*j+3+k) b) x‖≤G k := by
  obtain ⟨δ,hδ,hall⟩ := compact_negative_tail_summable_mixed_jets hb hK hB hS
  obtain ⟨η,c,hη,_,hroot⟩ := compact_roots_polydisks hb hK hB hS
  refine ⟨min δ η,lt_min hδ hη,?_⟩
  intro j
  obtain ⟨G,hG,hG0,hbound⟩ := hall j
  refine ⟨G,hG,hG0,?_⟩
  intro v hv x hx hi k
  have hxδ := ball_subset_ball (min_le_left δ η) hx
  have hxη := ball_subset_ball (min_le_right δ η) hx
  have hupper : x∈independentUpperDomain := ⟨hi,(hroot v hv).1 x hxη⟩
  rw [independentNegativeCoefficient_mixed_jets _ j hupper,norm_smul,norm_mul,
    norm_pow,norm_neg,norm_one,one_pow,mul_one]
  have hfac : ‖(((2*j+3+k+1).factorial:ℂ)⁻¹)‖≤1 := by
    simp only [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (2*j+3+k+1))
  exact (mul_le_mul_of_nonneg_right hfac (norm_nonneg _)).trans
    (by simpa only [one_mul] using hbound v hv x hxδ hi k)


/-- The analytic independent integral is the complete shifted period on its
actual upper physical side, with its sign and factorial unchanged. -/
theorem independentNegativeCoefficient_eq_period (n : ℕ) {b : ℝ} {p : NumeratorParameter}
    (hp : p∈independentUpperDomain) :
    independentNegativeCoefficient n b p=
      negativeShiftedPeriod b (fun _=>p.2.1) (fun _=>p.2.2) n p.1 := by
  unfold independentNegativeCoefficient negativeShiftedPeriod
  rw [edgeAngleMeasure_integral_eq_vector]
  simp only [smul_eq_mul]
  have he : (∫q in edgeCenteredCube n, independentComplexDensity b
      (p,fun i=>((negativeUnwrappedAngles n q i:ℝ):ℂ)))=
      ∫q in edgeCenteredCube n,negativeShiftedFullIntegrand b
        (fun _=>p.2.1) (fun _=>p.2.2) n p.1 q := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro q _
    exact (independentFullIntegrand_negative hp q).symm
  rw [he,edgeCoefficientNormalization]
  ring

/-- Pointwise physical attachment for the actual particle amplitude. -/
theorem independentNegativeCoefficient_eq_weighted_continued (n : ℕ) {b : ℝ}
    {K : Coupling} {amp : ℂ}
    (hp : physicalNegativeParameter b K amp∈independentUpperDomain) :
    independentNegativeCoefficient n b (physicalNegativeParameter b K amp)=
      amp^(n+1)*continuedAngularCoefficient n K := by
  rw [independentNegativeCoefficient_eq_period n hp]
  change negativeShiftedPeriod b (fun _=> -T K/IsingBulk.Joint.S K)
    (fun _=>IsingBulk.Joint.S K/amp) n (physicalNegativeParameter b K amp).1=_
  rw [negativeShiftedPeriod_div_scale b (fun _=> -T K/IsingBulk.Joint.S K)
    (fun _=>IsingBulk.Joint.S K) (fun _=>amp)]
  congr 1
  exact (IsingBulk.Joint.Negative.continuedAngularCoefficient_eq_negativeShiftedPeriod n
    (B := fun _=> -T K/IsingBulk.Joint.S K) (S := fun _=>IsingBulk.Joint.S K)
    (K := K) (u := (physicalNegativeParameter b K amp).1) rfl rfl
    (by dsimp [physicalNegativeParameter]; ring) hp.1 hp.2.1).symm

end
end IsingBulk.Joint.Negative
