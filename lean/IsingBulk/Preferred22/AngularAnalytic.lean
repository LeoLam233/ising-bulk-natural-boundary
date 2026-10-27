import IsingBulk.Preferred22.PhysicalAnalytic
import IsingBulk.Preferred22.PhysicalSymmetries
import IsingBulk.First.CompactIntegralHolomorphic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Holomorphy and differentiation of the actual finite constrained angular
coefficient. The integration domain is the complete angular box. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Filter Set MeasureTheory
open scoped BigOperators Topology

theorem angular_product_norm_lt_one {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 1 < ‖s‖)
    (θ : Fin N → ℝ) : ‖∏ i, angularRoots s θ i‖ < 1 := by
  rw [norm_prod]
  have h := Finset.prod_lt_prod_of_nonempty₀
    (s := (Finset.univ : Finset (Fin N))) (f := fun i => ‖angularRoots s θ i‖)
    (g := fun _ => (1 : ℝ))
    (fun i _ => norm_pos_iff.mpr (physicalRoot_ne_zero _))
    (fun i _ => angularRoots_inside hs θ i)
    ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  simpa using h

theorem angular_product_denominator_ne_zero {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 1 < ‖s‖) (θ : Fin N → ℝ) : 1 - ∏ i, angularRoots s θ i ≠ 0 := by
  intro he
  have hp := (sub_eq_zero.mp he).symm
  have h := angular_product_norm_lt_one hN hs θ
  rw [hp,norm_one] at h
  exact (lt_irrefl 1) h

def complexAngleRoot (w : ℂ) : ℂ := Complex.exp (Complex.I*w)

def complexAngularRoots {N : ℕ} (p : ℂ × (Fin N → ℂ)) (i : Fin N) : ℂ :=
  physicalRoot (temperatureTrace p.1 - Complex.cos (p.2 i))

def complexAngularDensity {N : ℕ} (p : ℂ × (Fin N → ℂ)) : ℂ :=
  let y := fun i => complexAngleRoot (p.2 i)
  let z := complexAngularRoots p
  let Z := ∏ i, z i
  (1+Z)/(1-Z) * ((-Complex.I)^N * (∏ i, z i/y i) * (rationalKernel y z).det) *
    ∏ i, oneBody (z i)

theorem complexAngularRoots_real {N : ℕ} (s : ℂ) (θ : Fin N → ℝ) :
    complexAngularRoots (s,fun i => (θ i : ℂ)) = angularRoots s θ := by
  ext i
  simp only [complexAngularRoots, angularRoots, angularW, ← Complex.ofReal_cos]

theorem complexAngularDensity_real {N : ℕ} (s : ℂ) (θ : Fin N → ℝ) :
    complexAngularDensity (s,fun i => (θ i : ℂ)) = fullAngularDensity s θ := by
  simp only [complexAngularDensity, fullAngularDensity, complexAngularRoots_real,
    complexAngleRoot, angleRoot, gaugeKernel_det_normalization]

theorem complexAngularDensity_analyticAt {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 1 < ‖s‖)
    (θ : Fin N → ℝ) :
    AnalyticAt ℂ (@complexAngularDensity N) (s,fun i => (θ i : ℂ)) := by
  let c : ℂ × (Fin N → ℂ) := (s,fun i => (θ i : ℂ))
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hw (i : Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => p.2 i) c :=
    (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt c)
  have hy (i : Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => complexAngleRoot (p.2 i)) c :=
    (analyticAt_const.mul (hw i)).cexp
  have hS : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => temperatureTrace p.1) c :=
    analyticAt_fst.add (analyticAt_fst.inv hs0)
  have hz (i : Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => complexAngularRoots p i) c := by
    have hWi : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
        temperatureTrace p.1 - Complex.cos (p.2 i)) c :=
      hS.sub (Complex.analyticAt_cos.comp (hw i))
    have he : temperatureTrace c.1 - Complex.cos (c.2 i) = angularW s (θ i) := by
      simp only [c, angularW, ← Complex.ofReal_cos]
    exact (physicalRoot_analyticAt (angularW_off_segment hs (θ i))).comp_of_eq hWi he
  have hzreal : complexAngularRoots c = angularRoots s θ := complexAngularRoots_real s θ
  have hden (i j : Fin N) : 1 - complexAngularRoots c i * complexAngularRoots c j ≠ 0 := by
    rw [hzreal]
    exact angular_pair_denominator_ne_zero hs θ i j
  have hZ := Finset.univ.analyticAt_fun_prod (fun i _ => hz i)
  have hZ0 : 1 - ∏ i, complexAngularRoots c i ≠ 0 := by
    rw [hzreal]
    exact angular_product_denominator_ne_zero hN hs θ
  have hR (i j : Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
      rationalKernel (fun l => complexAngleRoot (p.2 l)) (complexAngularRoots p) i j) c :=
    ((hy i).sub (hy j)).div (analyticAt_const.sub ((hz i).mul (hz j))) (hden i j)
  have hdet : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
      (rationalKernel (fun i => complexAngleRoot (p.2 i)) (complexAngularRoots p)).det) c := by
    simp only [Matrix.det_apply']
    exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
      analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hR (σ i) i)))
  have hratio := Finset.univ.analyticAt_fun_prod (fun i _ =>
    (hz i).div (hy i) (Complex.exp_ne_zero _))
  have hbody : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
      ∏ i, oneBody (complexAngularRoots p i)) c := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (analyticAt_const.mul (hz i)).div (analyticAt_const.sub ((hz i).pow 2))
    change 1-(complexAngularRoots c i)^2 ≠ 0
    simpa only [pow_two] using hden i i
  exact (((analyticAt_const.add hZ).div (analyticAt_const.sub hZ) hZ0).mul
    ((analyticAt_const.mul hratio).mul hdet)).mul hbody

def complexConstrainedAngles {n : ℕ} (θ : Fin n → ℝ) : Fin (n+1) → ℂ :=
  fun i => (constrainedAngles θ i : ℂ)

theorem continuous_complexConstrainedAngles (n : ℕ) : Continuous (@complexConstrainedAngles n) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [complexConstrainedAngles, constrainedAngles, Fin.snoc_last]
    exact Complex.continuous_ofReal.comp
      (continuous_finsetSum (Finset.univ : Finset (Fin n))
        (fun j _ => (continuous_apply j : Continuous (fun θ : Fin n → ℝ => θ j)))).neg
  · simp only [complexConstrainedAngles, constrainedAngles, Fin.snoc_castSucc]
    exact Complex.continuous_ofReal.comp (continuous_apply j)

/-- Every fixed coefficient is analytic on the whole exterior. This is not
a claim of normal convergence of the complete particle series. -/
theorem coefficient_analyticAt (N : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    AnalyticAt ℂ (coefficient N) s := by
  cases N with
  | zero => exact analyticAt_const
  | succ n =>
    let K : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Icc (-Real.pi) Real.pi)
    have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
    have hB : angularBox n =ᵐ[volume] K := Measure.pi_Ioc_ae_eq_pi_Icc
    have hU : IsOpen {t : ℂ | 1 < ‖t‖} := isOpen_lt continuous_const continuous_norm
    have hi := IsingBulk.First.compact_analytic_shape_integral_analyticAt
      (μ := (volume : Measure (Fin n → ℝ)))
      hK hU (@complexAngularDensity (n+1)) complexConstrainedAngles
      (continuous_complexConstrainedAngles n) (fun _ : Fin n → ℝ => (1 : ℂ)) continuous_const
      (fun t ht θ _ => complexAngularDensity_analyticAt (by omega) ht (constrainedAngles θ)) hs
    have heq : (fun t : ℂ => ∫ θ in K, (1:ℂ)*complexAngularDensity (t,complexConstrainedAngles θ)) =
        fun t => ∫ θ in angularBox n, fullAngularDensity t (constrainedAngles θ) := by
      funext t
      have hf (θ : Fin n → ℝ) : (1:ℂ)*complexAngularDensity (t,complexConstrainedAngles θ) =
          fullAngularDensity t (constrainedAngles θ) := by
        rw [one_mul]
        change complexAngularDensity (t,fun i => (constrainedAngles θ i : ℂ)) = _
        exact complexAngularDensity_real t (constrainedAngles θ)
      simp_rw [hf]
      exact setIntegral_congr_set hB.symm
    rw [heq] at hi
    exact analyticAt_const.mul hi

end
end IsingBulk.Preferred22
