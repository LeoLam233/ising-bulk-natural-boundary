import IsingBulk.Preferred22.CollectiveAnalytic
import IsingBulk.Preferred22.MixedTransport

/-! Actual smooth source coordinates and the physical transport factors.
Real bump functions retain real derivatives throughout. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

/-- The literal source q map is jointly C∞ in the real angles and complex
parameter on the actual upper physical branch. -/
theorem preferredSourceCoordinate_contDiffAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredSourceCoordinate τ p m z.1 z.2) (s,θ) := by
  have hcoe : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
  have hs : s≠0 := by intro hs; rw [hs] at hSi; simp [temperatureTrace] at hSi
  have htrace : AnalyticAt ℂ temperatureTrace s := analyticAt_id.add (analyticAt_id.inv hs)
  have ht : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => temperatureTrace z.1) (s,θ) :=
    ContDiffAt.comp (f := fun z : ℂ × (Fin N → ℝ) => z.1) (g := temperatureTrace) (s,θ)
      (htrace.contDiffAt.restrict_scalars ℝ) contDiffAt_fst
  have hB : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredMovingBranch z.1) (s,θ) :=
    ContDiffAt.comp (f := fun z : ℂ × (Fin N → ℝ) => z.1) (g := preferredMovingBranch) (s,θ)
      ((preferredMovingBranch_analyticAt_upper s hSi).contDiffAt.restrict_scalars ℝ) contDiffAt_fst
  apply contDiffAt_pi.mpr
  intro i
  have hw : ContDiff ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => deformedAngles τ p m z.2 i) := by
    unfold deformedAngles balancedShift occupancy
    fun_prop
  have harg : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)) (s,θ) := by
    have hcos : ContDiffAt ℝ ∞ Complex.cos (deformedAngles τ p m θ i) :=
      (show AnalyticAt ℂ Complex.cos (deformedAngles τ p m θ i) from Complex.analyticAt_cos).contDiffAt.restrict_scalars ℝ
    exact ht.sub (ContDiffAt.comp
      (f := fun z : ℂ × (Fin N → ℝ) => deformedAngles τ p m z.2 i)
      (g := Complex.cos) (s,θ) hcos hw.contDiffAt)
  have hφ : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredSourcePhase τ p m z.1 z.2 i) (s,θ) :=
    ContDiffAt.comp (f := fun z : ℂ × (Fin N → ℝ) =>
      temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)) (g := preferredArccos) (s,θ)
      ((IsingBulk.Branch.lowerArccos_analytic_of_upper (hW i)).contDiffAt.restrict_scalars ℝ) harg
  exact (hφ.add hw.contDiffAt).sub hB

/-- Source parameter holomorphy follows directly from the upper physical
phase, independently of an assumed inverse-coordinate derivative formula. -/
theorem preferredSourceCoordinate_parameter_analyticAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    AnalyticAt ℂ (fun t : ℂ => preferredSourceCoordinate τ p m t θ) s := by
  have hs : s≠0 := by intro hs; rw [hs] at hSi; simp [temperatureTrace] at hSi
  have htrace : AnalyticAt ℂ temperatureTrace s := analyticAt_id.add (analyticAt_id.inv hs)
  apply analyticAt_pi_iff.mpr
  intro i
  have hφ : AnalyticAt ℂ (fun t : ℂ => preferredSourcePhase τ p m t θ i) s :=
    AnalyticAt.comp (f := fun t : ℂ => temperatureTrace t-Complex.cos (deformedAngles τ p m θ i))
      (g := preferredArccos) (IsingBulk.Branch.lowerArccos_analytic_of_upper (hW i))
      (htrace.sub analyticAt_const)
  exact (hφ.add analyticAt_const).sub (preferredMovingBranch_analyticAt_upper s hSi)

/-- The complete occupancy differential is globally C∞ for the actual
smooth real bumps, including their derivative-dependent rank corrections. -/
theorem preferredContourMatrix_contDiff {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (preferredContourMatrix (N := N) τ p m) := by
  have hcoe : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
  have hp' : ContDiff ℝ ∞ (deriv p) := (contDiff_infty_iff_deriv.mp hp).2
  have hm' : ContDiff ℝ ∞ (deriv m) := (contDiff_infty_iff_deriv.mp hm).2
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  by_cases hij : i=j
  · simp only [preferredContourMatrix,shiftJacobian,hij,ite_true]
    fun_prop
  · simp only [preferredContourMatrix,shiftJacobian,hij,ite_false]
    fun_prop

/-- Matrix inversion is applied to the actual smooth occupancy matrix only
where its determinant is nonzero. The proof uses the literal adjugate. -/
theorem preferredContourMatrix_inverse_contDiffAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (θ : Fin N → ℝ)
    (hM : (preferredContourMatrix τ p m θ).det≠0) :
    ContDiffAt ℝ ∞ (fun x : Fin N → ℝ => (preferredContourMatrix τ p m x)⁻¹) θ := by
  have hmat := preferredContourMatrix_contDiff (N := N) τ p m hp hm
  have hentry (i j : Fin N) : ContDiff ℝ ∞ (fun x : Fin N → ℝ => preferredContourMatrix τ p m x i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hmat i)) j
  have hdet : ContDiff ℝ ∞ (fun x : Fin N → ℝ => (preferredContourMatrix τ p m x).det) := by
    simp only [Matrix.det_apply]
    fun_prop
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hu (k l : Fin N) : ContDiff ℝ ∞ (fun x : Fin N → ℝ =>
      ((preferredContourMatrix τ p m x).updateRow j (Pi.single i 1)) k l) := by
    by_cases hk : k=j
    · simp only [Matrix.updateRow_apply,hk,ite_true]
      fun_prop
    · simpa only [Matrix.updateRow_apply,hk,ite_false] using hentry k l
  have hadj : ContDiff ℝ ∞ (fun x : Fin N → ℝ => (preferredContourMatrix τ p m x).adjugate i j) := by
    simp only [Matrix.adjugate_apply,Matrix.det_apply]
    fun_prop
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact (hdet.contDiffAt.inv hM).mul hadj.contDiffAt

/-- The actual collective residual composed with the real occupancy source
is jointly smooth across all partial collisions. The full-equality R pole
is explicitly excluded by the genuine source denominator. -/
theorem preferredSourceCollective_contDiffAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re)
    (hq : ∀ i, preferredSourceCoordinate τ p m s θ i∈D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i))≠0) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2)) (s,θ) := by
  have ha := preferredResidualCollective_analyticAt_of_curvature s (preferredSourceCoordinate τ p m s θ)
    D c hc hD hU (preferredMovingBranch_analyticAt_upper s hSi) hcurv hq hR
  exact ContDiffAt.comp (f := fun z : ℂ × (Fin N → ℝ) => (z.1,preferredSourceCoordinate τ p m z.1 z.2))
    (g := fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,θ)
    (ha.contDiffAt.restrict_scalars ℝ)
    (contDiffAt_fst.prodMk (preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hSi hW))

theorem preferredSourceCollective_parameter_analyticAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re)
    (hq : ∀ i, preferredSourceCoordinate τ p m s θ i∈D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i))≠0) :
    AnalyticAt ℂ (fun t : ℂ => preferredResidualCollective t (preferredSourceCoordinate τ p m t θ)) s := by
  have ha := preferredResidualCollective_analyticAt_of_curvature s (preferredSourceCoordinate τ p m s θ)
    D c hc hD hU (preferredMovingBranch_analyticAt_upper s hSi) hcurv hq hR
  exact AnalyticAt.comp (f := fun t : ℂ => (t,preferredSourceCoordinate τ p m t θ))
    (g := fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) ha
    (analyticAt_id.prod (preferredSourceCoordinate_parameter_analyticAt τ p m s θ hSi hW))

/-- The actual physical product phase, before any regular-coordinate
normalization. -/
def preferredSourceProductPhase {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  Complex.exp (-Complex.I*preferredSourcePhaseSum τ p m s θ)

theorem preferredSourceProductPhase_eq_roots {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    preferredSourceProductPhase τ p m s θ=
      ∏ i, physicalRoot (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)) := by
  unfold preferredSourceProductPhase preferredSourcePhaseSum
  rw [Finset.mul_sum,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact preferredArccos_physical_upper _ (hW i)

theorem preferredSourceProductPhase_norm_lt_one {N : ℕ} (hN : 0<N)
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    ‖preferredSourceProductPhase τ p m s θ‖<1 := by
  have hphase (i : Fin N) : (preferredSourcePhase τ p m s θ i).im<0 :=
    (IsingBulk.Branch.lowerArccos_sheet_of_upper (hW i)).2.2.2
  have hsum : (∑ i, (preferredSourcePhase τ p m s θ i).im)<0 := by
    have hh := Finset.sum_lt_sum (s := Finset.univ)
      (fun i _ => (hphase i).le)
      ⟨⟨0,hN⟩,Finset.mem_univ _,hphase ⟨0,hN⟩⟩
    simpa only [Finset.sum_const_zero] using hh
  have hre : (-Complex.I*preferredSourcePhaseSum τ p m s θ).re=
      ∑ i, (preferredSourcePhase τ p m s θ i).im := by
    simp [preferredSourcePhaseSum,Complex.mul_re]
  rw [preferredSourceProductPhase,Complex.norm_exp,hre]
  exact Real.exp_lt_one_iff.mpr hsum

def preferredPhaseResolvent (z : ℂ) : ℂ :=
  (1+Complex.exp (-Complex.I*z))/(1-Complex.exp (-Complex.I*z))

def preferredSourceResolvent {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  preferredPhaseResolvent (preferredSourcePhaseSum τ p m s θ)

/-- Chain rule for the actual complex-parameter/real-angular material
operator. Angular derivatives are retained as real derivatives. -/
theorem preferred_material_chain_rule {N : ℕ} (V : Fin N → ℂ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (g : ℂ → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hFs : DifferentiableAt ℂ (fun t => F t θ) s)
    (hFθ : ∀ i, DifferentiableAt ℝ (fun x => F s (Function.update θ i x)) (θ i))
    (hg : DifferentiableAt ℂ g (F s θ)) :
    deriv (fun t : ℂ => g (F t θ)) s-
      (∑ i, V i*deriv (fun x : ℝ => g (F s (Function.update θ i x))) (θ i))=
      deriv g (F s θ)*(deriv (fun t : ℂ => F t θ) s-
        ∑ i, V i*deriv (fun x : ℝ => F s (Function.update θ i x)) (θ i)) := by
  have hs : HasDerivAt (fun t : ℂ => g (F t θ))
      (deriv g (F s θ)*deriv (fun t : ℂ => F t θ) s) s := by
    convert! hg.hasDerivAt.comp s hFs.hasDerivAt using 1
  have hx (i : Fin N) : HasDerivAt (fun x : ℝ => g (F s (Function.update θ i x)))
      (deriv (fun x : ℝ => F s (Function.update θ i x)) (θ i)*deriv g (F s θ)) (θ i) := by
    convert! hg.hasDerivAt.scomp_of_eq (θ i) (hFθ i).hasDerivAt
      (by simp only [Function.update_eq_self]) using 1
  rw [hs.deriv]
  simp_rw [(hx _).deriv]
  rw [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The unchanged physical simple-pole quotient is frozen by the literal
collective transport. Its nonzero denominator follows from the actual
physical branch for all N, rather than being supplied as a tail hypothesis. -/
theorem preferredSourceResolvent_material_freeze {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (s : ℂ) (θ : Fin N → ℝ) (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hM : (preferredContourMatrix τ p m θ).det≠0)
    (hc : ∀ i j,
      preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)=
        preferredSourceUQ s (preferredSourceCoordinate τ p m s θ j) →
      preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i)=
        preferredMovingInverse s (preferredSourceCoordinate τ p m s θ j))
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i))≠0) :
    deriv (fun t : ℂ => preferredSourceResolvent τ p m t θ) s-
      (∑ j, preferredSourceAngularField .right τ p m s θ j *
        deriv (fun x : ℝ => preferredSourceResolvent τ p m s (Function.update θ j x)) (θ j))=0 := by
  have hFs : DifferentiableAt ℂ (fun t : ℂ => preferredSourcePhaseSum τ p m t θ) s := by
    simpa only [preferredSourcePhaseSum,Finset.sum_fn] using
      (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
        preferredSourcePhase_parameter_hasDerivAt τ δ p m s θ i hδ hδπ hS hSi hSδ (hθ i) (hW i))).differentiableAt
  have hFθ (j : Fin N) : DifferentiableAt ℝ
      (fun x : ℝ => preferredSourcePhaseSum τ p m s (Function.update θ j x)) (θ j) := by
    simpa only [preferredSourcePhaseSum,Finset.sum_fn] using
      (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
        preferredSourcePhase_angular_hasDerivAt τ δ p m hp hm s θ i j hδ hδπ hS hSδ (hθ i) (hW i))).differentiableAt
  have hden : 1-Complex.exp (-Complex.I*preferredSourcePhaseSum τ p m s θ)≠0 := by
    intro he
    have hz : preferredSourceProductPhase τ p m s θ=1 := (sub_eq_zero.mp he).symm
    have hn := preferredSourceProductPhase_norm_lt_one hN τ p m s θ hW
    rw [hz,norm_one] at hn
    exact (lt_irrefl 1) hn
  have he : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-Complex.I*z)) (preferredSourcePhaseSum τ p m s θ) :=
    analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id)
  have hg : DifferentiableAt ℂ preferredPhaseResolvent (preferredSourcePhaseSum τ p m s θ) :=
    ((analyticAt_const.add he).div (analyticAt_const.sub he) hden).differentiableAt
  simp only [preferredSourceResolvent]
  rw [preferred_material_chain_rule _ _ _ s θ hFs hFθ hg]
  rw [preferredSourcePhaseSum_material_freeze τ δ p m hp hm s θ hδ hδπ hS hSi hSδ hθ hW hM hc hR,mul_zero]

/-- The two actual inverse derivatives composed with the physical occupancy
coordinate retain joint real smoothness. -/
theorem preferredSourceInverseDerivatives_contDiffAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hU : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ i)) :
    (ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      fun i => preferredSourceUQ z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)) (s,θ)) ∧
    (ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      fun i => preferredSourceUDot z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)) (s,θ)) := by
  have hχ := preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hSi hW
  have hmap (i : Fin N) : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      (z.1,preferredSourceCoordinate τ p m z.1 z.2 i)) (s,θ) :=
    contDiffAt_fst.prodMk (contDiffAt_pi.mp hχ i)
  constructor
  · apply contDiffAt_pi.mpr
    intro i
    exact ContDiffAt.comp
      (f := fun z : ℂ × (Fin N → ℝ) => (z.1,preferredSourceCoordinate τ p m z.1 z.2 i))
      (g := fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2) (s,θ)
      ((preferredSourceUQ_analyticAt_of_joint s _ (hU i)).contDiffAt.restrict_scalars ℝ) (hmap i)
  · apply contDiffAt_pi.mpr
    intro i
    exact ContDiffAt.comp
      (f := fun z : ℂ × (Fin N → ℝ) => (z.1,preferredSourceCoordinate τ p m z.1 z.2 i))
      (g := fun z : ℂ × ℂ => preferredSourceUDot z.1 z.2) (s,θ)
      ((preferredSourceUDot_analyticAt_of_joint s _ (hU i)).contDiffAt.restrict_scalars ℝ) (hmap i)

theorem preferredSourceInverseDerivatives_parameter_analyticAt {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hU : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ i)) :
    (AnalyticAt ℂ (fun t : ℂ => fun i => preferredSourceUQ t (preferredSourceCoordinate τ p m t θ i)) s) ∧
    (AnalyticAt ℂ (fun t : ℂ => fun i => preferredSourceUDot t (preferredSourceCoordinate τ p m t θ i)) s) := by
  have hχ := preferredSourceCoordinate_parameter_analyticAt τ p m s θ hSi hW
  have hmap (i : Fin N) : AnalyticAt ℂ (fun t : ℂ => (t,preferredSourceCoordinate τ p m t θ i)) s :=
    analyticAt_id.prod (analyticAt_pi_iff.mp hχ i)
  constructor
  · apply analyticAt_pi_iff.mpr
    intro i
    exact AnalyticAt.comp (f := fun t : ℂ => (t,preferredSourceCoordinate τ p m t θ i))
      (g := fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2)
      (preferredSourceUQ_analyticAt_of_joint s _ (hU i)) (hmap i)
  · apply analyticAt_pi_iff.mpr
    intro i
    exact AnalyticAt.comp (f := fun t : ℂ => (t,preferredSourceCoordinate τ p m t θ i))
      (g := fun z : ℂ × ℂ => preferredSourceUDot z.1 z.2)
      (preferredSourceUDot_analyticAt_of_joint s _ (hU i)) (hmap i)

/-- The actual complete angular representative is jointly C∞ on the
regular source domain. Its occupancy matrix and real bump derivatives are
retained; no holomorphic continuation of the bumps is introduced. -/
theorem preferredSourceAngularField_contDiffAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re)
    (hq : ∀ i, preferredSourceCoordinate τ p m s θ i∈D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i))≠0)
    (hM : (preferredContourMatrix τ p m θ).det≠0) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredSourceAngularField .right τ p m z.1 z.2) (s,θ) := by
  have hB := preferredSourceCollective_contDiffAt τ p m hp hm s θ hSi hW D c hc hD hU hcurv hq hR
  obtain ⟨hv,hu⟩ := preferredSourceInverseDerivatives_contDiffAt τ p m hp hm s θ hSi hW
    (fun i => hU _ (hq i))
  have hMinv : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => (preferredContourMatrix τ p m z.2)⁻¹) (s,θ) :=
    ContDiffAt.comp (f := fun z : ℂ × (Fin N → ℝ) => z.2)
      (g := fun x : Fin N → ℝ => (preferredContourMatrix τ p m x)⁻¹) (s,θ)
      (preferredContourMatrix_inverse_contDiffAt τ p m hp hm θ hM) contDiffAt_snd
  have hMi (i j : Fin N) := contDiffAt_pi.mp (contDiffAt_pi.mp hMinv i) j
  have hBi (i : Fin N) := contDiffAt_pi.mp hB i
  have hui (i : Fin N) := contDiffAt_pi.mp hu i
  have hvi (i : Fin N) := contDiffAt_pi.mp hv i
  apply contDiffAt_pi.mpr
  intro i
  simp only [preferredSourceAngularField,preferredAngularRepresentative,preferredResidualField,Matrix.mulVec,dotProduct]
  exact (ContDiffAt.sum (fun j _ => (hMi i j).mul
    ((hui j).add ((hvi j).mul (hBi j))))).neg

theorem preferredSourceAngularField_parameter_analyticAt {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re)
    (hq : ∀ i, preferredSourceCoordinate τ p m s θ i∈D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i))≠0) :
    AnalyticAt ℂ (fun t : ℂ => preferredSourceAngularField .right τ p m t θ) s := by
  have hB := preferredSourceCollective_parameter_analyticAt τ p m s θ hSi hW D c hc hD hU hcurv hq hR
  obtain ⟨hv,hu⟩ := preferredSourceInverseDerivatives_parameter_analyticAt τ p m s θ hSi hW
    (fun i => hU _ (hq i))
  have hBi (i : Fin N) := analyticAt_pi_iff.mp hB i
  have hui (i : Fin N) := analyticAt_pi_iff.mp hu i
  have hvi (i : Fin N) := analyticAt_pi_iff.mp hv i
  apply analyticAt_pi_iff.mpr
  intro i
  simp only [preferredSourceAngularField,preferredAngularRepresentative,preferredResidualField,Matrix.mulVec,dotProduct]
  exact (Finset.analyticAt_fun_sum Finset.univ (fun j _ => analyticAt_const.mul
    ((hui j).add ((hvi j).mul (hBi j))))).neg

/-- The unchanged coordinate Jacobian is jointly smooth in the actual
physical source and holomorphic in its physical parameter. -/
theorem preferredCoordinateJacobian_contDiffAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hU : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ i))
    (hQ : ∀ i, preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)≠0) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredCoordinateJacobian τ p m z.1 z.2) (s,θ) := by
  obtain ⟨hv,_⟩ := preferredSourceInverseDerivatives_contDiffAt τ p m hp hm s θ hSi hW hU
  have hvi (i : Fin N) := (contDiffAt_pi.mp hv i).inv (hQ i)
  have hmat : ContDiff ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredContourMatrix τ p m z.2) :=
    (preferredContourMatrix_contDiff τ p m hp hm).comp contDiff_snd
  have hentry (i j : Fin N) := contDiff_pi.mp (contDiff_pi.mp hmat i) j
  have hdet : ContDiff ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => (preferredContourMatrix τ p m z.2).det) := by
    simp only [Matrix.det_apply]
    fun_prop
  unfold preferredCoordinateJacobian
  exact hdet.contDiffAt.mul (contDiffAt_prod (fun i _ => hvi i))

theorem preferredCoordinateJacobian_parameter_analyticAt {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hU : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ i))
    (hQ : ∀ i, preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)≠0) :
    AnalyticAt ℂ (fun t : ℂ => preferredCoordinateJacobian τ p m t θ) s := by
  obtain ⟨hv,_⟩ := preferredSourceInverseDerivatives_parameter_analyticAt τ p m s θ hSi hW hU
  have hvi (i : Fin N) := (analyticAt_pi_iff.mp hv i).inv (hQ i)
  unfold preferredCoordinateJacobian
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod Finset.univ (fun i _ => hvi i))

/-- Real angular Jacobian of a genuinely smooth coordinate map. -/
def preferredRealCoordinateJacobian {N : ℕ}
    (F : (ℝ × (Fin N → ℝ)) → (Fin N → ℂ)) (z : ℝ × (Fin N → ℝ)) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun k j => fderiv ℝ (fun x => F x k) z (0,Pi.single j 1)

def preferredRealCoordinateSpeed {N : ℕ}
    (F : (ℝ × (Fin N → ℝ)) → (Fin N → ℂ)) (z : ℝ × (Fin N → ℝ)) : Fin N → ℂ :=
  fun k => fderiv ℝ (fun x => F x k) z (1,0)

def preferredRealResidualJacobian {N : ℕ}
    (B : (Fin N → ℝ) → (Fin N → ℂ)) (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun k i => fderiv ℝ (fun x => B x k) θ (Pi.single i 1)

/-- Coordinate Piola identity with every derivative premise discharged
from genuine real C∞ regularity and Schwarz symmetry. The residual field
requires only its actual first derivative. No real cutoff is complexified. -/
theorem preferred_real_coordinate_piola {N : ℕ}
    (F : (ℝ × (Fin N → ℝ)) → (Fin N → ℂ))
    (B : (Fin N → ℝ) → (Fin N → ℂ)) (t : ℝ) (θ : Fin N → ℝ)
    (hF : ContDiffAt ℝ ∞ F (t,θ)) (hB : DifferentiableAt ℝ B θ)
    (hA : (preferredRealCoordinateJacobian F (t,θ)).det≠0) :
    deriv (fun u : ℝ => (preferredRealCoordinateJacobian F (u,θ)).det) t-
      (∑ i, deriv (fun u : ℝ =>
        (((preferredRealCoordinateJacobian F (t,Function.update θ i u))⁻¹).mulVec
          (preferredRealCoordinateSpeed F (t,Function.update θ i u)-B (Function.update θ i u))) i *
            (preferredRealCoordinateJacobian F (t,Function.update θ i u)).det) (θ i))=
      (preferredRealCoordinateJacobian F (t,θ)).det *
        Matrix.trace ((preferredRealCoordinateJacobian F (t,θ))⁻¹*preferredRealResidualJacobian B θ) := by
  let e (j : Fin N) : ℝ × (Fin N → ℝ) := (0,Pi.single j 1)
  let e₀ : ℝ × (Fin N → ℝ) := (1,0)
  let A := fun u x => preferredRealCoordinateJacobian F (u,x)
  let a := preferredRealCoordinateSpeed F (t,θ)
  let v := fun x => preferredRealCoordinateSpeed F (t,x)-B x
  let P : Matrix (Fin N) (Fin N) ℂ := fun k j =>
    fderiv ℝ (fun z => fderiv ℝ (fun x => F x k) z (e j)) (t,θ) e₀
  let Q := preferredRealResidualJacobian B θ
  let H : Fin N → Fin N → Fin N → ℂ := fun i j k =>
    fderiv ℝ (fun z => fderiv ℝ (fun x => F x k) z (e j)) (t,θ) (e i)
  have hFk (k : Fin N) : ContDiffAt ℝ ∞ (fun x => F x k) (t,θ) := contDiffAt_pi.mp hF k
  have hpart (k : Fin N) (w : ℝ × (Fin N → ℝ)) :
      ContDiffAt ℝ ∞ (fun z => fderiv ℝ (fun x => F x k) z w) (t,θ) :=
    ((hFk k).fderiv_right (by simp : (∞:ℕ∞ω)+1≤∞)).clm_apply contDiffAt_const
  have hsym (k : Fin N) (w w' : ℝ × (Fin N → ℝ)) :
      fderiv ℝ (fun z => fderiv ℝ (fun x => F x k) z w) (t,θ) w'=
        fderiv ℝ (fun z => fderiv ℝ (fun x => F x k) z w') (t,θ) w := by
    have hd := ((hFk k).fderiv_right (by simp : (1:ℕ∞ω)+1≤∞)).differentiableAt (by norm_num)
    simp only [fderiv_clm_apply hd (differentiableAt_const _),fderiv_const_apply,
      ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]
    exact (hFk k).isSymmSndFDerivAt (by simp) w' w
  have hH : ∀ i j, H i j=H j i := by
    intro i j
    funext k
    exact hsym k (e j) (e i)
  have hAt (k j : Fin N) : HasDerivAt (fun u : ℝ => A u θ k j) (P k j) t := by
    have hh := ((hpart k (e j)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t θ))
    convert! hh using 1
  have hAx (i k j : Fin N) : HasDerivAt (fun u : ℝ => A t (Function.update θ i u) k j)
      (H i j k) (θ i) := by
    have hh := ((hpart k (e j)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
      ((hasDerivAt_const (θ i) t).prodMk (hasDerivAt_update θ i (θ i))) (by simp)
    convert! hh using 1
  have hvx (i k : Fin N) : HasDerivAt (fun u : ℝ => v (Function.update θ i u) k)
      (P k i-Q k i) (θ i) := by
    have ha := ((hpart k e₀).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
      ((hasDerivAt_const (θ i) t).prodMk (hasDerivAt_update θ i (θ i))) (by simp)
    have hb := (differentiableAt_pi.mp hB k).hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
      (hasDerivAt_update θ i (θ i)) (by simp)
    have hspeed : HasDerivAt (fun u : ℝ => preferredRealCoordinateSpeed F (t,Function.update θ i u) k)
        (P k i) (θ i) := by
      convert! ha using 1
      exact hsym k (e i) e₀
    convert! hspeed.sub hb using 1
  have hAc : ContinuousAt (fun x => A t x) θ := by
    apply continuousAt_pi.mpr
    intro k
    apply continuousAt_pi.mpr
    intro j
    exact ContinuousAt.comp (f := fun x : Fin N → ℝ => (t,x))
      (g := fun z => fderiv ℝ (fun x => F x k) z (e j))
      (hpart k (e j)).continuousAt (continuousAt_const.prodMk continuousAt_id)
  have hh := preferred_weighted_scalar_transport (fun _ => (1:ℝ)) (fun _ => (0:ℝ))
    (fun _ _ => (1:ℂ)) A v t θ (0 : (Fin N → ℂ) →ₗ[ℂ] ℂ) 0 a (B θ) P Q H hH rfl hAc hA
    (fun i => by simpa using hasDerivAt_const (θ i) (1:ℝ))
    (by simpa using hasDerivAt_const t (1:ℂ))
    (fun i => by simpa using hasDerivAt_const (θ i) (1:ℂ)) hAt hAx hvx
  simpa only [preferredAngularVelocity,one_mul,mul_one,LinearMap.zero_apply,zero_add,
    Complex.ofReal_zero,Complex.ofReal_one,mul_zero,zero_mul,Finset.sum_const_zero,sub_zero,A,v,Q] using hh

/-- The actual q source with a real parameter line, used only to apply
Schwarz to the real angular variables; the physical parameter remains
holomorphic. -/
def preferredRealSourceChart {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ)
    (z : ℝ × (Fin N → ℝ)) : Fin N → ℂ :=
  preferredSourceCoordinate τ p m (s+(z.1:ℂ)) z.2

theorem preferredRealSourceChart_contDiffAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace (s+(t:ℂ))).im)
    (hW : ∀ i, 0<(temperatureTrace (s+(t:ℂ))-Complex.cos (deformedAngles τ p m θ i)).im) :
    ContDiffAt ℝ ∞ (preferredRealSourceChart τ p m s) (t,θ) := by
  have hcoe : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × (Fin N → ℝ) => (s+(z.1:ℂ),z.2)) := by fun_prop
  exact ContDiffAt.comp
    (f := fun z : ℝ × (Fin N → ℝ) => (s+(z.1:ℂ),z.2))
    (g := fun z : ℂ × (Fin N → ℝ) => preferredSourceCoordinate τ p m z.1 z.2) (t,θ)
    (preferredSourceCoordinate_contDiffAt τ p m hp hm (s+(t:ℂ)) θ hSi hW) hmap.contDiffAt

/-- The real-line chart uses exactly the original angular Jacobian. -/
theorem preferredRealSourceChart_jacobian {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace (s+(t:ℂ))).im)
    (hW : ∀ i, 0<(temperatureTrace (s+(t:ℂ))-Complex.cos (deformedAngles τ p m θ i)).im) :
    preferredRealCoordinateJacobian (preferredRealSourceChart τ p m s) (t,θ)=
      preferredSourceJacobian τ p m (s+(t:ℂ)) θ := by
  have hF := preferredRealSourceChart_contDiffAt τ p m hp hm s t θ hSi hW
  ext k j
  have hk := (contDiffAt_pi.mp hF k).differentiableAt (by simp)
  have hh := hk.hasFDerivAt.comp_hasDerivAt_of_eq (θ j)
    ((hasDerivAt_const (θ j) t).prodMk (hasDerivAt_update θ j (θ j)))
    (by simp only [Function.update_eq_self])
  exact hh.deriv.symm

/-- Actual complex parameter differentiation agrees with the real-line
speed, with no analytic extension of an angular bump. -/
theorem preferredRealSourceChart_speed {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace (s+(t:ℂ))).im)
    (hW : ∀ i, 0<(temperatureTrace (s+(t:ℂ))-Complex.cos (deformedAngles τ p m θ i)).im) :
    preferredRealCoordinateSpeed (preferredRealSourceChart τ p m s) (t,θ)=
      fun i => deriv (fun z : ℂ => preferredSourceCoordinate τ p m z θ i) (s+(t:ℂ)) := by
  have hF := preferredRealSourceChart_contDiffAt τ p m hp hm s t θ hSi hW
  have hhol := preferredSourceCoordinate_parameter_analyticAt τ p m (s+(t:ℂ)) θ hSi hW
  funext i
  have hreal := ((contDiffAt_pi.mp hF i).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t θ))
  have hcomplex := (analyticAt_pi_iff.mp hhol i).differentiableAt.hasDerivAt.comp (t:ℂ)
    ((hasDerivAt_id (t:ℂ)).const_add s)
  have hh : HasDerivAt (fun u : ℝ => preferredSourceCoordinate τ p m (s+(u:ℂ)) θ i)
      (deriv (fun z : ℂ => preferredSourceCoordinate τ p m z θ i) (s+(t:ℂ))) t := by
    convert! hcomplex.comp_ofReal using 1
    simp only [mul_one]
  exact hreal.unique hh

/-- The chart velocity is the literal complete occupancy angular field. -/
theorem preferredRealSourceChart_velocity {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace (s+(t:ℂ))).re) (hSi : 0<(temperatureTrace (s+(t:ℂ))).im)
    (hSδ : (temperatureTrace (s+(t:ℂ))).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace (s+(t:ℂ))-Complex.cos (deformedAngles τ p m θ i)).im) :
    (preferredRealCoordinateJacobian (preferredRealSourceChart τ p m s) (t,θ))⁻¹.mulVec
      (preferredRealCoordinateSpeed (preferredRealSourceChart τ p m s) (t,θ)-
        preferredResidualCollective (s+(t:ℂ)) (preferredSourceCoordinate τ p m (s+(t:ℂ)) θ))=
      preferredSourceAngularField .right τ p m (s+(t:ℂ)) θ := by
  have hp' := hp.differentiable (by simp)
  have hm' := hm.differentiable (by simp)
  rw [preferredRealSourceChart_jacobian τ p m hp hm s t θ hSi hW,
    preferredRealSourceChart_speed τ p m hp hm s t θ hSi hW,
    preferredSourceJacobian_inverse τ δ p m hp' hm' (s+(t:ℂ)) θ hδ hδπ hS hSδ hθ hW]
  have hspeed (i : Fin N) := (preferredSourceCoordinate_parameter_hasDerivAt τ δ p m (s+(t:ℂ)) θ i
    hδ hδπ hS hSi hSδ (hθ i) (hW i)).deriv
  have hv (i : Fin N) : preferredSourceUQ (s+(t:ℂ)) (preferredSourceCoordinate τ p m (s+(t:ℂ)) θ i)≠0 := by
    have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
    exact (preferred_global_one_sided_q_regular (s+(t:ℂ)) (deformedAngles τ p m θ i) δ
      hδ hδπ hS hSδ (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2
  funext i
  simp only [preferredSourceAngularField,preferredAngularRepresentative,preferredResidualField,
    Matrix.mul_diagonal,Matrix.mulVec,dotProduct,Pi.sub_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hspeed]
  field_simp [hv j]
  ring

/-- An open physical one-sided source chart. These are primitive dispersion
and angular inequalities, not any transport or tail conclusion. -/
def PreferredSourceRegime {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (z : ℂ × (Fin N → ℝ)) : Prop :=
  0<(temperatureTrace z.1).re ∧ 0<(temperatureTrace z.1).im ∧
  (temperatureTrace z.1).re<2*Real.cos δ ∧
  (∀ i, z.2 i∈Set.Ioo (-Real.pi-δ) δ) ∧
  ∀ i, 0<(temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)).im

theorem preferredSourceRegime_isOpen {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Continuous p) (hm : Continuous m) :
    IsOpen {z : ℂ × (Fin N → ℝ) | PreferredSourceRegime τ δ p m z} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨s,θ⟩ ⟨hS,hSi,hSδ,hθ,hW⟩
  have hs : s≠0 := by intro hs; rw [hs] at hSi; simp [temperatureTrace] at hSi
  have ht : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => temperatureTrace z.1) (s,θ) := by
    unfold temperatureTrace
    exact continuousAt_fst.add (continuousAt_fst.inv₀ hs)
  have hr : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => (temperatureTrace z.1).re) (s,θ) :=
    Complex.continuous_re.continuousAt.comp ht
  have hi : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => (temperatureTrace z.1).im) (s,θ) :=
    Complex.continuous_im.continuousAt.comp ht
  have hθev : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ), ∀ i, z.2 i∈Set.Ioo (-Real.pi-δ) δ := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun z : ℂ × (Fin N → ℝ) => z.2 i) (s,θ) := by fun_prop
    filter_upwards [continuousAt_const.eventually_lt hc (hθ i).1,
      hc.eventually_lt continuousAt_const (hθ i).2] with z hzlo hzhi
    exact ⟨hzlo,hzhi⟩
  have hWev : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ),
      ∀ i, 0<(temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)).im := by
    apply Filter.eventually_all.mpr
    intro i
    have hw : Continuous (fun z : ℂ × (Fin N → ℝ) => deformedAngles τ p m z.2 i) := by
      unfold deformedAngles balancedShift occupancy
      fun_prop
    have hc : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
        (temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)).im) (s,θ) :=
      Complex.continuous_im.continuousAt.comp (ht.sub (Complex.continuous_cos.comp hw).continuousAt)
    exact continuousAt_const.eventually_lt hc (hW i)
  filter_upwards [continuousAt_const.eventually_lt hr hS,continuousAt_const.eventually_lt hi hSi,
    hr.eventually_lt continuousAt_const hSδ,hθev,hWev] with z hzS hzSi hzSδ hzθ hzW
  exact ⟨hzS,hzSi,hzSδ,hzθ,hzW⟩

/-- The literal trace is the divergence in the actual inverse q frame. -/
theorem preferred_source_residual_trace {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2) (hS : 0<(temperatureTrace s).re)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hB : DifferentiableAt ℝ
      (fun x : Fin N → ℝ => preferredResidualCollective s (preferredSourceCoordinate τ p m s x)) θ) :
    Matrix.trace ((preferredSourceJacobian τ p m s θ)⁻¹*
      preferredRealResidualJacobian
        (fun x => preferredResidualCollective s (preferredSourceCoordinate τ p m s x)) θ)=
      preferredRegularDivergenceCoefficient τ p m s θ := by
  have hd (a i : Fin N) : preferredRealResidualJacobian
      (fun x => preferredResidualCollective s (preferredSourceCoordinate τ p m s x)) θ a i=
      deriv (fun u : ℝ => preferredResidualCollective s
        (preferredSourceCoordinate τ p m s (Function.update θ i u)) a) (θ i) := by
    have hh := (differentiableAt_pi.mp hB a).hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
      (hasDerivAt_update θ i (θ i)) (by simp only [Function.update_eq_self])
    exact hh.deriv.symm
  unfold preferredRegularDivergenceCoefficient
  simp_rw [preferredCoordinateFrame_eq_inverse_jacobian τ δ p m hp hm s θ _ _
    hδ hδπ hS hSδ hθ hW]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,hd]
  exact Finset.sum_comm

/-- The actual Jacobian satisfies the complete scalar Piola identity.
Every matrix derivative and every mixed partial is obtained from the
literal C∞ source map; no Piola equation is assumed. -/
theorem preferredCoordinateJacobian_piola {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hreg : PreferredSourceRegime τ δ p m (s,θ))
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re)
    (hq : ∀ i, preferredSourceCoordinate τ p m s θ i∈D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i))≠0)
    (hM : (preferredContourMatrix τ p m θ).det≠0) :
    deriv (fun t : ℂ => preferredCoordinateJacobian τ p m t θ) s-
      (∑ i, deriv (fun u : ℝ =>
        preferredSourceAngularField .right τ p m s (Function.update θ i u) i*
          preferredCoordinateJacobian τ p m s (Function.update θ i u)) (θ i))=
      preferredCoordinateJacobian τ p m s θ*preferredRegularDivergenceCoefficient τ p m s θ := by
  obtain ⟨hS,hSi,hSδ,hθo,hW⟩ := hreg
  have hθ (i : Fin N) : θ i∈Set.Icc (-Real.pi-δ) δ := ⟨(hθo i).1.le,(hθo i).2.le⟩
  have hp' := hp.differentiable (by simp)
  have hm' := hm.differentiable (by simp)
  let F := preferredRealSourceChart (N := N) τ p m s
  let B := fun x : Fin N → ℝ => preferredResidualCollective s (preferredSourceCoordinate τ p m s x)
  have hF : ContDiffAt ℝ ∞ F (0,θ) := by
    simpa only [Complex.ofReal_zero,add_zero] using
      preferredRealSourceChart_contDiffAt τ p m hp hm s 0 θ (by simpa using hSi) (by simpa using hW)
  have hBc := preferredSourceCollective_contDiffAt τ p m hp hm s θ hSi hW D c hc hD hU hcurv hq hR
  have hB : DifferentiableAt ℝ B θ :=
    (ContDiffAt.comp (f := fun x : Fin N → ℝ => (s,x))
      (g := fun z : ℂ × (Fin N → ℝ) => preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2)) θ
      hBc (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hA : preferredRealCoordinateJacobian F (0,θ)=preferredSourceJacobian τ p m s θ := by
    simpa only [Complex.ofReal_zero,add_zero] using preferredRealSourceChart_jacobian τ p m hp hm s 0 θ (by simpa using hSi) (by simpa using hW)
  have hAn : (preferredRealCoordinateJacobian F (0,θ)).det≠0 := by
    rw [hA]
    exact preferredSourceJacobian_det_ne_zero τ δ p m hp' hm' s θ hδ hδπ hS hSδ hθ hW hM
  have hpiola := preferred_real_coordinate_piola F B 0 θ hF hB hAn
  have hregEv : ∀ᶠ z : ℝ × (Fin N → ℝ) in 𝓝 (0,θ),
      PreferredSourceRegime τ δ p m (s+(z.1:ℂ),z.2) := by
    have hg : Continuous (fun z : ℝ × (Fin N → ℝ) => (s+(z.1:ℂ),z.2)) := by fun_prop
    have ht : Filter.Tendsto (fun z : ℝ × (Fin N → ℝ) => (s+(z.1:ℂ),z.2))
        (𝓝 (0,θ)) (𝓝 (s,θ)) := by simpa only [Complex.ofReal_zero,add_zero] using hg.tendsto (0,θ)
    exact ht.eventually ((preferredSourceRegime_isOpen τ δ p m hp.continuous hm.continuous).mem_nhds
      ⟨hS,hSi,hSδ,hθo,hW⟩)
  have hdet : (fun z : ℝ × (Fin N → ℝ) => (preferredRealCoordinateJacobian F z).det)
      =ᶠ[𝓝 (0,θ)] (fun z => preferredCoordinateJacobian τ p m (s+(z.1:ℂ)) z.2) := by
    filter_upwards [hregEv] with z hz
    obtain ⟨hzS,hzSi,hzSδ,hzθ,hzW⟩ := hz
    rw [preferredRealSourceChart_jacobian τ p m hp hm s z.1 z.2 hzSi hzW]
    exact preferredSourceJacobian_det τ δ p m hp' hm' _ _ hδ hδπ hzS hzSδ
      (fun i => ⟨(hzθ i).1.le,(hzθ i).2.le⟩) hzW
  have hvel : (fun x : Fin N → ℝ =>
      (preferredRealCoordinateJacobian F (0,x))⁻¹.mulVec
        (preferredRealCoordinateSpeed F (0,x)-B x))
      =ᶠ[𝓝 θ] preferredSourceAngularField .right τ p m s := by
    have ht : Filter.Tendsto (fun x : Fin N → ℝ => ((0:ℝ),x)) (𝓝 θ) (𝓝 (0,θ)) :=
      (continuous_const.prodMk continuous_id).tendsto θ
    filter_upwards [ht.eventually hregEv] with x hx
    simp only [Complex.ofReal_zero,add_zero] at hx
    obtain ⟨hxS,hxSi,hxSδ,hxθ,hxW⟩ := hx
    simpa only [Complex.ofReal_zero,add_zero] using
      preferredRealSourceChart_velocity τ δ p m hp hm s 0 x hδ hδπ
        (by simpa using hxS) (by simpa using hxSi) (by simpa using hxSδ)
        (fun i => ⟨(hxθ i).1.le,(hxθ i).2.le⟩) (by simpa using hxW)
  have hdetParam : (fun u : ℝ => (preferredRealCoordinateJacobian F (u,θ)).det)
      =ᶠ[𝓝 0] (fun u : ℝ => preferredCoordinateJacobian τ p m (s+(u:ℂ)) θ) :=
    hdet.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto 0)
  have hdetAngular : (fun x : Fin N → ℝ => (preferredRealCoordinateJacobian F (0,x)).det)
      =ᶠ[𝓝 θ] preferredCoordinateJacobian τ p m s := by
    have hh := hdet.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto θ)
    simpa only [Function.comp_def,id_eq,Complex.ofReal_zero,add_zero] using hh
  have hflux (i : Fin N) :
      deriv (fun u : ℝ => ((preferredRealCoordinateJacobian F (0,Function.update θ i u))⁻¹.mulVec
        (preferredRealCoordinateSpeed F (0,Function.update θ i u)-B (Function.update θ i u))) i*
          (preferredRealCoordinateJacobian F (0,Function.update θ i u)).det) (θ i)=
      deriv (fun u : ℝ => preferredSourceAngularField .right τ p m s (Function.update θ i u) i*
        preferredCoordinateJacobian τ p m s (Function.update θ i u)) (θ i) := by
    have ht : Filter.Tendsto (fun u : ℝ => Function.update θ i u) (𝓝 (θ i)) (𝓝 θ) := by
      have hh : Continuous (fun u : ℝ => Function.update θ i u) := by fun_prop
      simpa only [Function.update_eq_self] using hh.tendsto (θ i)
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hvel.comp_tendsto ht,hdetAngular.comp_tendsto ht] with u huV huJ
    dsimp only [Function.comp_def] at huV huJ
    rw [huV,huJ]
  have hv (i : Fin N) : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)≠0 := by
    have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
    exact (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2
  have hJ := preferredCoordinateJacobian_parameter_analyticAt τ p m s θ hSi hW (fun i => hU _ (hq i)) hv
  have hJ0 : HasDerivAt (fun t : ℂ => preferredCoordinateJacobian τ p m t θ)
      (deriv (fun t : ℂ => preferredCoordinateJacobian τ p m t θ) s) (s+(0:ℂ)) := by
    simpa only [add_zero] using hJ.differentiableAt.hasDerivAt
  have hJreal : HasDerivAt (fun u : ℝ => preferredCoordinateJacobian τ p m (s+(u:ℂ)) θ)
      (deriv (fun t : ℂ => preferredCoordinateJacobian τ p m t θ) s) 0 := by
    convert! (hJ0.comp (0:ℂ) ((hasDerivAt_id (0:ℂ)).const_add s)).comp_ofReal using 1
    simp only [mul_one]
  rw [hdetParam.deriv_eq,hJreal.deriv] at hpiola
  simp_rw [hflux] at hpiola
  rw [hA,preferredSourceJacobian_det τ δ p m hp' hm' s θ hδ hδπ hS hSδ hθ hW,
    preferred_source_residual_trace τ δ p m hp' hm' s θ hδ hδπ hS hSδ hθ hW hB] at hpiola
  exact hpiola

/-- Product calculus for the literal physical transport. The Jacobian
Piola and frozen-phase identities are used only after being separately
proved for the actual source factors. -/
theorem preferredTransportStep_factored {N : ℕ}
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ)
    (J H G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) (c : ℂ)
    (hJs : DifferentiableAt ℂ (fun t => J t θ) s)
    (hHs : DifferentiableAt ℂ (fun t => H t θ) s)
    (hGs : DifferentiableAt ℂ (fun t => G t θ) s)
    (hJθ : ∀ i, DifferentiableAt ℝ (fun x => J s (Function.update θ i x)) (θ i))
    (hHθ : ∀ i, DifferentiableAt ℝ (fun x => H s (Function.update θ i x)) (θ i))
    (hGθ : ∀ i, DifferentiableAt ℝ (fun x => G s (Function.update θ i x)) (θ i))
    (hVθ : ∀ i, DifferentiableAt ℝ (fun x => V s (Function.update θ i x) i) (θ i))
    (hPiola : deriv (fun t => J t θ) s-
      (∑ i, deriv (fun x => V s (Function.update θ i x) i*J s (Function.update θ i x)) (θ i))=J s θ*c)
    (hfreeze : deriv (fun t => H t θ) s-
      (∑ i, V s θ i*deriv (fun x => H s (Function.update θ i x)) (θ i))=0) :
    preferredTransportStep V (fun t x => J t x*H t x*G t x) s θ=
      J s θ*H s θ*(deriv (fun t => G t θ) s-
        (∑ i, V s θ i*deriv (fun x => G s (Function.update θ i x)) (θ i))+c*G s θ) := by
  let j := J s θ
  let h := H s θ
  let g := G s θ
  let jp := deriv (fun t => J t θ) s
  let hp := deriv (fun t => H t θ) s
  let gp := deriv (fun t => G t θ) s
  let a := fun i => deriv (fun x => V s (Function.update θ i x) i*J s (Function.update θ i x)) (θ i)
  let hx := fun i => deriv (fun x => H s (Function.update θ i x)) (θ i)
  let gx := fun i => deriv (fun x => G s (Function.update θ i x)) (θ i)
  have hparam : deriv (fun t => J t θ*H t θ*G t θ) s=(jp*h+j*hp)*g+(j*h)*gp := by
    exact ((hJs.hasDerivAt.mul hHs.hasDerivAt).mul hGs.hasDerivAt).deriv
  have hangular (i : Fin N) :
      deriv (fun x => V s (Function.update θ i x) i*
        (J s (Function.update θ i x)*H s (Function.update θ i x)*G s (Function.update θ i x))) (θ i)=
      a i*(h*g)+(V s θ i*j)*(hx i*g+h*gx i) := by
    have ha : HasDerivAt (fun x : ℝ => V s (Function.update θ i x) i*J s (Function.update θ i x))
        (a i) (θ i) :=
      (show DifferentiableAt ℝ (fun x : ℝ => V s (Function.update θ i x) i*J s (Function.update θ i x)) (θ i)
        from (hVθ i).mul (hJθ i)).hasDerivAt
    have hh := ha.mul ((hHθ i).hasDerivAt.mul (hGθ i).hasDerivAt)
    have he : (fun x => V s (Function.update θ i x) i*
        (J s (Function.update θ i x)*H s (Function.update θ i x)*G s (Function.update θ i x)))=
        fun x => (V s (Function.update θ i x) i*J s (Function.update θ i x))*
          (H s (Function.update θ i x)*G s (Function.update θ i x)) := by funext x; ring
    rw [he]
    convert! hh.deriv using 1
    simp only [Pi.mul_apply,Function.update_eq_self,h,g,j,hx,gx]
  have hsum : (∑ i, (a i*(h*g)+(V s θ i*j)*(hx i*g+h*gx i)))=
      (∑ i, a i)*(h*g)+j*(∑ i, V s θ i*hx i)*g+(j*h)*(∑ i, V s θ i*gx i) := by
    simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold preferredTransportStep preferredAngularDivergence
  rw [hparam]
  simp_rw [hangular]
  rw [hsum]
  change (jp*h+j*hp)*g+(j*h)*gp-((∑ i, a i)*(h*g)+j*(∑ i, V s θ i*hx i)*g+
    (j*h)*(∑ i, V s θ i*gx i))=j*h*(gp-(∑ i, V s θ i*gx i)+c*g)
  change jp-(∑ i, a i)=j*c at hPiola
  change hp-(∑ i, V s θ i*hx i)=0 at hfreeze
  linear_combination h*g*hPiola+j*g*hfreeze

/-- Exact initial physical factorization into the unchanged coordinate
Jacobian, unchanged simple-pole resolvent, and literal regular seed. -/
theorem preferredPhysicalSeed_factorized {N : ℕ} (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    preferredPhysicalSeed .right τ η p m r s θ=
      preferredCoordinateJacobian τ p m s θ*preferredSourceResolvent τ p m s θ*
        preferredRegularSeed τ η p m r s θ := by
  have hU (i : Fin N) : preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i)=
      deformedAngles τ p m θ i := by
    have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
    exact preferred_global_one_sided_inverse s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)
  have hZ : preferredRegularProductPhase s (preferredSourceCoordinate τ p m s θ)=
      preferredSourceProductPhase τ p m s θ := by
    unfold preferredRegularProductPhase preferredSourceProductPhase preferredSourcePhaseSum
    simp_rw [preferred_regular_phase_on_source τ p m s θ hU]
  rw [preferred_one_sided_seed_eq_regular .right τ δ η p m r s θ hδ hδπ hS hSδ hθ hW]
  unfold preferredRegularAmplitude
  rw [hZ]
  unfold preferredRegularSeed preferredSourceResolvent preferredPhaseResolvent preferredSourceProductPhase
  ring

/-- The actual physical total phase is jointly smooth in the original real
angle variables and holomorphic in the complex temperature parameter. -/
theorem preferredSourcePhaseSum_contDiffAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredSourcePhaseSum τ p m z.1 z.2) (s,θ) := by
  have hχ := preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hSi hW
  have hcoe : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
  have hB : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredMovingBranch z.1) (s,θ) :=
    ContDiffAt.comp (f := fun z : ℂ × (Fin N → ℝ) => z.1) (g := preferredMovingBranch) (s,θ)
      ((preferredMovingBranch_analyticAt_upper s hSi).contDiffAt.restrict_scalars ℝ) contDiffAt_fst
  unfold preferredSourcePhaseSum
  apply ContDiffAt.sum
  intro i _
  have hw : ContDiff ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => deformedAngles τ p m z.2 i) := by
    unfold deformedAngles balancedShift occupancy
    fun_prop
  simp_rw [preferredSourcePhase_coordinate_identity]
  exact ((contDiffAt_pi.mp hχ i).sub hw.contDiffAt).add hB

theorem preferredSourcePhaseSum_parameter_analyticAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    AnalyticAt ℂ (fun t : ℂ => preferredSourcePhaseSum τ p m t θ) s := by
  have hχ := preferredSourceCoordinate_parameter_analyticAt τ p m s θ hSi hW
  unfold preferredSourcePhaseSum
  apply Finset.analyticAt_fun_sum Finset.univ
  intro i _
  simp_rw [preferredSourcePhase_coordinate_identity]
  exact ((analyticAt_pi_iff.mp hχ i).sub analyticAt_const).add
    (preferredMovingBranch_analyticAt_upper s hSi)

theorem preferredPhaseResolvent_analyticAt_source {N : ℕ} (hN : 0<N)
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    AnalyticAt ℂ preferredPhaseResolvent (preferredSourcePhaseSum τ p m s θ) := by
  have hden : 1-Complex.exp (-Complex.I*preferredSourcePhaseSum τ p m s θ)≠0 := by
    intro he
    have hz : preferredSourceProductPhase τ p m s θ=1 := (sub_eq_zero.mp he).symm
    have hn := preferredSourceProductPhase_norm_lt_one hN τ p m s θ hW
    rw [hz,norm_one] at hn
    exact (lt_irrefl 1) hn
  have he : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-Complex.I*z)) (preferredSourcePhaseSum τ p m s θ) :=
    analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id)
  exact (analyticAt_const.add he).div (analyticAt_const.sub he) hden

theorem preferredSourceResolvent_contDiffAt {N : ℕ} (hN : 0<N)
    (τ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredSourceResolvent τ p m z.1 z.2) (s,θ) :=
  ContDiffAt.comp (f := fun z : ℂ × (Fin N → ℝ) => preferredSourcePhaseSum τ p m z.1 z.2)
    (g := preferredPhaseResolvent) (s,θ)
    ((preferredPhaseResolvent_analyticAt_source hN τ p m s θ hW).contDiffAt.restrict_scalars ℝ)
    (preferredSourcePhaseSum_contDiffAt τ p m hp hm s θ hSi hW)

theorem preferredSourceResolvent_parameter_analyticAt {N : ℕ} (hN : 0<N)
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im) :
    AnalyticAt ℂ (fun t : ℂ => preferredSourceResolvent τ p m t θ) s :=
  AnalyticAt.comp (f := fun t : ℂ => preferredSourcePhaseSum τ p m t θ) (g := preferredPhaseResolvent)
    (preferredPhaseResolvent_analyticAt_source hN τ p m s θ hW)
    (preferredSourcePhaseSum_parameter_analyticAt τ p m s θ hSi hW)

/-- The complete actual physical transport descends to the regular scalar
operator with the original Jacobian and simple pole left unchanged. This
is the physical one-step identity needed by every marked-minor iteration. -/
theorem preferred_physical_transport_factorization {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hreg : PreferredSourceRegime τ δ p m (s,θ))
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈D, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hcurv : ∀ z∈D, c≤(deriv (preferredSourceUQ s) z).re)
    (hq : ∀ i, preferredSourceCoordinate τ p m s θ i∈D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i))≠0)
    (hM : (preferredContourMatrix τ p m θ).det≠0)
    (G : ℂ → (Fin N → ℝ) → ℂ)
    (hGs : DifferentiableAt ℂ (fun t => G t θ) s)
    (hGθ : ∀ i, DifferentiableAt ℝ (fun x => G s (Function.update θ i x)) (θ i)) :
    preferredTransportStep (preferredSourceAngularField .right τ p m)
      (fun t x => preferredCoordinateJacobian τ p m t x*preferredSourceResolvent τ p m t x*G t x) s θ=
      preferredCoordinateJacobian τ p m s θ*preferredSourceResolvent τ p m s θ*
        preferredRegularTransportStep τ p m G s θ := by
  obtain ⟨hS,hSi,hSδ,hθo,hW⟩ := hreg
  have hθ (i : Fin N) : θ i∈Set.Icc (-Real.pi-δ) δ := ⟨(hθo i).1.le,(hθo i).2.le⟩
  have hv (i : Fin N) : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)≠0 := by
    have hwre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
    exact (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
      (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)).2
  have hJ := preferredCoordinateJacobian_contDiffAt τ p m hp hm s θ hSi hW (fun i => hU _ (hq i)) hv
  have hH := preferredSourceResolvent_contDiffAt hN τ p m hp hm s θ hSi hW
  have hV := preferredSourceAngularField_contDiffAt τ p m hp hm s θ hSi hW D c hc hD hU hcurv hq hR hM
  have hcoord (F : ℂ × (Fin N → ℝ) → ℂ) (hF : DifferentiableAt ℝ F (s,θ)) (i : Fin N) :
      DifferentiableAt ℝ (fun x => F (s,Function.update θ i x)) (θ i) :=
    (hF.hasFDerivAt.comp_hasDerivAt_of_eq (θ i)
      ((hasDerivAt_const (θ i) s).prodMk (hasDerivAt_update θ i (θ i)))
      (by simp only [Function.update_eq_self])).differentiableAt
  have huq (z : ℂ) (hz : z∈D) : DifferentiableAt ℂ (preferredSourceUQ s) z := by
    have hh := preferredSourceUQ_analyticAt_of_joint s z (hU z hz)
    exact (AnalyticAt.comp (f := fun q : ℂ => (s,q))
      (g := fun x : ℂ × ℂ => preferredSourceUQ x.1 x.2) hh
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hcoll (i j : Fin N)
      (he : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)=
        preferredSourceUQ s (preferredSourceCoordinate τ p m s θ j)) :
      preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i)=
        preferredMovingInverse s (preferredSourceCoordinate τ p m s θ j) :=
    congrArg (preferredMovingInverse s)
      (preferredSourceUQ_injectiveOn s D c hc hD huq hcurv (hq i) (hq j) he)
  have hpiola := preferredCoordinateJacobian_piola τ δ p m hp hm s θ hδ hδπ
    ⟨hS,hSi,hSδ,hθo,hW⟩ D c hc hD hU hcurv hq hR hM
  have hfreeze := preferredSourceResolvent_material_freeze hN τ δ p m
    (hp.differentiable (by simp)) (hm.differentiable (by simp)) s θ hδ hδπ hS hSi hSδ hθ hW hM hcoll hR
  have hh := preferredTransportStep_factored (preferredSourceAngularField .right τ p m)
    (preferredCoordinateJacobian τ p m) (preferredSourceResolvent τ p m) G s θ
    (preferredRegularDivergenceCoefficient τ p m s θ)
    (preferredCoordinateJacobian_parameter_analyticAt τ p m s θ hSi hW (fun i => hU _ (hq i)) hv).differentiableAt
    (preferredSourceResolvent_parameter_analyticAt hN τ p m s θ hSi hW).differentiableAt hGs
    (fun i => hcoord _ (hJ.differentiableAt (by simp)) i)
    (fun i => hcoord _ (hH.differentiableAt (by simp)) i) hGθ
    (fun i => hcoord _ ((contDiffAt_pi.mp hV i).differentiableAt (by simp)) i)
    hpiola hfreeze
  rw [preferredRegularTransportStep_eq]
  exact hh

end
end IsingBulk.Preferred22
