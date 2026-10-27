import IsingBulk.Preferred22.ContourLegality
import IsingBulk.Preferred22.PhysicalKernel
import IsingBulk.Anisotropic.NegativeCycles.DensityForm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! The literal balanced constrained homotopy from LT22 Section 5.
Only finite-dimensional branch and Stokes infrastructure is reused. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Topology
open Set Filter MeasureTheory

/- The following three finite-box definitions/identity are adapted from the
proper foundational CapTransport module of the pinned LT repository. Only cap
splitting is reused; there are no cutoff or asymptotic assumptions. -/
open IsingBulk.Anisotropic.NegativeCycles

def cylinderFaceFlux {n : ℕ}
    (form : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    (a b : ParameterSpace n) (i : Fin (n+1)) : ℂ :=
  (∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      (-1:ℤ)^i.val • form (i.insertNth (b i) x)
        (i.removeNth (fun k => (Pi.single k (1:ℝ) : ParameterSpace n)))) -
    ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      (-1:ℤ)^i.val • form (i.insertNth (a i) x)
        (i.removeNth (fun k => (Pi.single k (1:ℝ) : ParameterSpace n)))

def cylinderCapIntegral {n : ℕ}
    (form : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    (a b : ParameterSpace n) (t : ℝ) : ℂ :=
  ∫ x in Icc (a ∘ (0:Fin (n+1)).succAbove) (b ∘ (0:Fin (n+1)).succAbove),
    form ((0:Fin (n+1)).insertNth t x)
      ((0:Fin (n+1)).removeNth (fun k => (Pi.single k (1:ℝ) : ParameterSpace n)))

theorem cylinderBoundaryFlux_caps {n : ℕ}
    (form : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    (a b : ParameterSpace n) :
    boxBoundaryFlux form a b=cylinderCapIntegral form a b (b 0)-cylinderCapIntegral form a b (a 0)+
      ∑ i : Fin n, cylinderFaceFlux form a b i.succ := by
  change (∑ i : Fin (n+1), cylinderFaceFlux form a b i)=_
  rw [Fin.sum_univ_succ]
  congr 1
  simp [cylinderFaceFlux,cylinderCapIntegral]

def contourRoots {N : ℕ} (s : ℂ) (y : Fin N → ℂ) : Fin N → ℂ :=
  fun i => physicalRoot (complexW s (y i))

/-- The full physical density written without square-root gauges. -/
def rootFreeDensity {N : ℕ} (s : ℂ) (y : Fin N → ℂ) : ℂ :=
  let z : Fin N → ℂ := contourRoots s y
  let Z := ∏ i, z i
  (1+Z)/(1-Z) * ((-Complex.I)^N*(∏ i, z i/y i)*(rationalKernel y z).det) *
    ∏ i, oneBody (z i)

theorem complexW_angleRoot (s : ℂ) (θ : ℝ) :
    complexW s (angleRoot θ) = angularW s θ := by
  rw [complexW, angleRoot_trace]
  unfold angularW
  ring

theorem fullAngularDensity_eq_rootFreeDensity {N : ℕ} (s : ℂ) (θ : Fin N → ℝ) :
    fullAngularDensity s θ = rootFreeDensity s (fun i => angleRoot (θ i)) := by
  have he : contourRoots s (fun i => angleRoot (θ i)) = angularRoots s θ := by
    funext i
    simp only [contourRoots, angularRoots, complexW_angleRoot]
  simp only [fullAngularDensity, rootFreeDensity, he, gaugeKernel_det_normalization]

theorem complex_product_gap {N : ℕ} (hN : 0 < N) (z : Fin N → ℂ)
    (hz : ∀ i, z i ≠ 0) (hzi : ∀ i, ‖z i‖ < 1) : 1-∏ i, z i ≠ 0 := by
  have hp : ‖∏ i, z i‖ < 1 := by
    rw [norm_prod]
    calc
      _ < ∏ _i : Fin N, (1:ℝ) := Finset.prod_lt_prod_of_nonempty₀
        (fun i _ => norm_pos_iff.mpr (hz i)) (fun i _ => hzi i)
        ⟨⟨0,hN⟩, Finset.mem_univ _⟩
      _ = 1 := by simp
  intro hh
  have he : (∏ i, z i)=1 := (sub_eq_zero.mp hh).symm
  simp [he] at hp

theorem complex_pair_gap {u v : ℂ} (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    1-u*v ≠ 0 := by
  intro hh
  have he : u*v=1 := (sub_eq_zero.mp hh).symm
  have hp : ‖u*v‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg u, norm_nonneg v]
  simp [he] at hp

theorem contour_differentiable_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g h : E → ℂ} {x : E} (hg : DifferentiableAt ℂ g x) (hh : DifferentiableAt ℂ h x)
    (hne : h x ≠ 0) : DifferentiableAt ℂ (fun y => g y/h y) x := by
  simpa only [div_eq_mul_inv, Pi.inv_apply] using hg.fun_mul (hh.inv hne)

set_option backward.isDefEq.respectTransparency false in
theorem rootFreeDensity_differentiableAt {N : ℕ} (hN : 0 < N) (s : ℂ)
    (y : Fin N → ℂ) (hy : ∀ i, y i ≠ 0)
    (hW : ∀ i, 0 < (complexW s (y i)).im) :
    DifferentiableAt ℂ (rootFreeDensity (N := N) s) y := by
  let z : (Fin N → ℂ) → Fin N → ℂ := contourRoots s
  have hz0 : ∀ i, z y i ≠ 0 := fun i => physicalRoot_ne_zero _
  have hzi : ∀ i, ‖z y i‖ < 1 := fun i => physicalRoot_inside (Or.inl (hW i).ne')
  have dz : ∀ i, DifferentiableAt ℂ (fun x => z x i) y := by
    intro i
    have dw : DifferentiableAt ℂ (fun x : Fin N → ℂ => complexW s (x i)) y := by
      unfold complexW
      have di : DifferentiableAt ℂ (fun x : Fin N → ℂ => x i) y :=
        differentiableAt_apply i y
      have ha : DifferentiableAt ℂ (fun x : Fin N → ℂ => x i+(x i)⁻¹) y :=
        di.add (di.inv (hy i))
      convert! (differentiableAt_const (temperatureTrace s)).sub
        (ha.mul_const (2⁻¹:ℂ)) using 1
    exact (physicalRoot_differentiableAt_upper (hW i)).comp y dw
  have dZ : DifferentiableAt ℂ (fun x => ∏ i, z x i) y :=
    (HasFDerivAt.finsetProd (fun i _ => (dz i).hasFDerivAt)).differentiableAt
  have dzy : DifferentiableAt ℂ (fun x : Fin N → ℂ => ∏ i, z x i/x i) y :=
    (HasFDerivAt.finsetProd (fun i _ =>
      (contour_differentiable_div (dz i) (differentiableAt_apply i y) (hy i)).hasFDerivAt)).differentiableAt
  have dentry (i j : Fin N) :
      DifferentiableAt ℂ (fun x => rationalKernel x (z x) i j) y := by
    exact contour_differentiable_div
      ((differentiableAt_apply i y).sub (differentiableAt_apply j y))
      ((differentiableAt_const (1:ℂ)).sub ((dz i).mul (dz j))) (complex_pair_gap (hzi i) (hzi j))
  have ddet : DifferentiableAt ℂ (fun x => (rationalKernel x (z x)).det) y := by
    simp only [Matrix.det_apply']
    apply DifferentiableAt.fun_sum
    intro σ _
    exact ((HasFDerivAt.finsetProd (fun i _ =>
      (dentry (σ i) i).hasFDerivAt)).differentiableAt).const_mul _
  have db : DifferentiableAt ℂ (fun x => ∏ i, oneBody (z x i)) y := by
    apply HasFDerivAt.differentiableAt
    apply HasFDerivAt.finsetProd
    intro i _
    exact (contour_differentiable_div ((dz i).const_mul 2)
      ((differentiableAt_const (1:ℂ)).sub ((dz i).pow 2))
      (by simpa [pow_two] using complex_pair_gap (hzi i) (hzi i))).hasFDerivAt
  exact ((contour_differentiable_div ((differentiableAt_const (1:ℂ)).add dZ)
    ((differentiableAt_const (1:ℂ)).sub dZ)
    (complex_product_gap hN (z y) hz0 hzi)).mul ((dzy.const_mul _).mul ddet)).mul db

def constrainedComplex {n : ℕ} (x : Fin n → ℂ) : Fin (n+1) → ℂ :=
  Fin.snoc x (-∑ i, x i)

theorem constrainedAngles_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (@constrainedAngles n) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedAngles, Fin.snoc_last]
    fun_prop
  · simp only [constrainedAngles, Fin.snoc_castSucc]
    fun_prop

theorem constrainedComplex_contDiff (n : ℕ) :
    ContDiff ℂ ∞ (@constrainedComplex n) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedComplex, Fin.snoc_last]
    fun_prop
  · simp only [constrainedComplex, Fin.snoc_castSucc]
    fun_prop

def constrainedLogDensity (n : ℕ) (s : ℂ) (x : Fin n → ℂ) : ℂ :=
  rootFreeDensity s (fun i => Complex.exp (constrainedComplex x i))

theorem constrainedLogDensity_differentiableAt (n : ℕ) (s : ℂ) (x : Fin n → ℂ)
    (hW : ∀ i, 0 < (complexW s (Complex.exp (constrainedComplex x i))).im) :
    DifferentiableAt ℂ (constrainedLogDensity n s) x := by
  have he : DifferentiableAt ℂ (fun y => fun i => Complex.exp (constrainedComplex y i)) x := by
    apply differentiableAt_pi.mpr
    intro i
    exact Complex.differentiableAt_exp.comp x
      (((contDiff_apply ℂ ℂ i).comp (constrainedComplex_contDiff n)).differentiable (by simp) x)
  exact (rootFreeDensity_differentiableAt (by omega) s _ (fun i => Complex.exp_ne_zero _) hW).comp x he

def freeLogHomotopy {n : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) : Fin n → ℂ :=
  fun j => Complex.I*(θ j:ℂ)+(lam:ℂ)*balancedShift τ p m (constrainedAngles θ) j.castSucc

theorem constrained_homotopy_extension {n : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) :
    constrainedComplex (freeLogHomotopy τ lam p m θ) =
      fun i => Complex.I*(constrainedAngles θ i:ℂ)+
        (lam:ℂ)*balancedShift τ p m (constrainedAngles θ) i := by
  have hs := balancedShift_sum τ p m (constrainedAngles θ)
  rw [Fin.sum_univ_castSucc] at hs
  have hl : balancedShift τ p m (constrainedAngles θ) (Fin.last n) =
      -∑ i : Fin n, balancedShift τ p m (constrainedAngles θ) i.castSucc := by
    linarith
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedComplex, Fin.snoc_last, freeLogHomotopy]
    rw [hl]
    simp only [constrainedAngles, Fin.snoc_last, Finset.sum_add_distrib,
      ← Finset.mul_sum, Complex.ofReal_neg, Complex.ofReal_sum]
    ring
  · simp only [constrainedComplex, Fin.snoc_castSucc, freeLogHomotopy, constrainedAngles]

theorem exp_constrained_homotopy {n : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) (i : Fin (n+1)) :
    Complex.exp (constrainedComplex (freeLogHomotopy τ lam p m θ) i) =
      homotopyRoot τ lam p m (constrainedAngles θ) i := by
  rw [constrained_homotopy_extension]
  rfl

theorem balancedShift_contDiff (N : ℕ) (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (fun θ : Fin N → ℝ => balancedShift τ p m θ) := by
  apply contDiff_pi.mpr
  intro i
  unfold balancedShift occupancy
  fun_prop

theorem freeLogHomotopy_contDiff (n : ℕ) (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (fun x : ℝ × (Fin n → ℝ) => freeLogHomotopy τ x.1 p m x.2) := by
  have hs := (balancedShift_contDiff (n+1) τ p m hp hm).comp (constrainedAngles_contDiff n)
  have ho : ContDiff ℝ ∞ Complex.ofReal := Complex.ofRealCLM.contDiff
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_const.mul (ho.comp ((contDiff_apply ℝ ℝ i).comp contDiff_snd))).add
    ((ho.comp contDiff_fst).mul
      (ho.comp (((contDiff_apply ℝ ℝ i.castSucc).comp hs).comp contDiff_snd)))

def parameterHomotopy {n : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (x : Fin (n+1) → ℝ) : Fin n → ℂ :=
  freeLogHomotopy τ (x 0) p m (fun i => x i.succ)

theorem parameterHomotopy_contDiff (n : ℕ) (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (@parameterHomotopy n τ p m) := by
  change ContDiff ℝ ∞ ((fun x : ℝ × (Fin n → ℝ) => freeLogHomotopy τ x.1 p m x.2) ∘
    (fun x : Fin (n+1) → ℝ => (x 0, fun i => x i.succ)))
  exact (freeLogHomotopy_contDiff n τ p m hp hm).comp (by fun_prop)

theorem constrained_bump_periodic {n : ℕ} (p : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (θ : Fin n → ℝ) (q : Fin n) :
    (fun i => p (constrainedAngles (θ+Pi.single q (2*Real.pi)) i)) =
      fun i => p (constrainedAngles θ i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedAngles, Fin.snoc_last, Pi.add_apply,
      Finset.sum_add_distrib]
    rw [Fintype.sum_pi_single']
    have he : -((∑ j, θ j) + 2*Real.pi) = -(∑ j, θ j)-2*Real.pi := by ring
    rw [he]
    exact hp.sub_eq _
  · simp only [constrainedAngles, Fin.snoc_castSucc, Pi.add_apply]
    by_cases hj : j=q
    · subst j
      simpa using hp (θ q)
    · simp [hj]

theorem constrained_shift_periodic {n : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (θ : Fin n → ℝ) (q : Fin n) :
    balancedShift τ p m (constrainedAngles (θ+Pi.single q (2*Real.pi))) =
      balancedShift τ p m (constrainedAngles θ) := by
  have hp' := constrained_bump_periodic p hp θ q
  have hm' := constrained_bump_periodic m hm θ q
  funext i
  have hpi := congrFun hp' i
  have hmi := congrFun hm' i
  have hP : occupancy p (constrainedAngles (θ+Pi.single q (2*Real.pi))) =
      occupancy p (constrainedAngles θ) := congrArg (fun f : Fin (n+1) → ℝ => ∑ i, f i) hp'
  have hQ : occupancy m (constrainedAngles (θ+Pi.single q (2*Real.pi))) =
      occupancy m (constrainedAngles θ) := congrArg (fun f : Fin (n+1) → ℝ => ∑ i, f i) hm'
  simp only [balancedShift, hP, hQ, hpi, hmi]

theorem freeLogHomotopy_periodic {n : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (θ : Fin n → ℝ) (q : Fin n) :
    freeLogHomotopy τ lam p m (θ+Pi.single q (2*Real.pi)) =
      freeLogHomotopy τ lam p m θ + Pi.single q (2*Real.pi*Complex.I) := by
  unfold freeLogHomotopy
  rw [constrained_shift_periodic τ p m hp hm]
  funext i
  by_cases hi : i=q
  · subst i
    simp
    ring
  · simp [hi]

theorem parameterHomotopy_periodic {n : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (x : Fin (n+1) → ℝ) (q : Fin n) :
    parameterHomotopy τ p m (x+Pi.single q.succ (2*Real.pi)) =
      parameterHomotopy τ p m x + Pi.single q (2*Real.pi*Complex.I) := by
  have hzero : (x+Pi.single q.succ (2*Real.pi) : Fin (n+1) → ℝ) 0 = x 0 := by
    simp [Fin.succ_ne_zero]
  have htail : (fun i => (x+Pi.single q.succ (2*Real.pi) : Fin (n+1) → ℝ) i.succ) =
      (fun i => x i.succ)+Pi.single q (2*Real.pi) := by
    funext i
    simp [Pi.single_apply, Fin.succ_inj]
  unfold parameterHomotopy
  rw [hzero, htail, freeLogHomotopy_periodic τ (x 0) p m hp hm]

theorem constrained_exp_periodic {n : ℕ} (x : Fin n → ℂ) (q : Fin n) :
    (fun i => Complex.exp (constrainedComplex (x+Pi.single q (2*Real.pi*Complex.I)) i)) =
      fun i => Complex.exp (constrainedComplex x i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedComplex, Fin.snoc_last, Pi.add_apply,
      Finset.sum_add_distrib]
    rw [Fintype.sum_pi_single']
    simp only [neg_add, Complex.exp_add, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, inv_one, mul_one]
  · simp only [constrainedComplex, Fin.snoc_castSucc, Pi.add_apply]
    by_cases hj : j=q
    · subst j
      simp [Complex.exp_add, Complex.exp_two_pi_mul_I]
    · simp [hj]

theorem constrainedLogDensity_periodic (n : ℕ) (s : ℂ) (x : Fin n → ℂ) (q : Fin n) :
    constrainedLogDensity n s (x+Pi.single q (2*Real.pi*Complex.I)) =
      constrainedLogDensity n s x := by
  unfold constrainedLogDensity
  rw [constrained_exp_periodic]

theorem parameterHomotopy_fderiv_periodic {n : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (x : Fin (n+1) → ℝ) (q : Fin n) :
    fderiv ℝ (parameterHomotopy τ p m) (x+Pi.single q.succ (2*Real.pi)) =
      fderiv ℝ (parameterHomotopy τ p m) x := by
  have he := congrArg (fun f : (Fin (n+1) → ℝ) → (Fin n → ℂ) => fderiv ℝ f x)
    (funext (fun y => parameterHomotopy_periodic τ p m hp hm y q))
  rwa [fderiv_comp_add_right, fderiv_add_const] at he

def constrainedPullback {n : ℕ} (s : ℂ) (τ : ℝ) (p m : ℝ → ℝ) :=
  chainPullback (densityForm (constrainedLogDensity n s)) (parameterHomotopy τ p m)

theorem constrainedPullback_periodic {n : ℕ} (s : ℂ) (τ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (x : Fin (n+1) → ℝ) (q : Fin n) :
    constrainedPullback s τ p m (x+Pi.single q.succ (2*Real.pi)) =
      constrainedPullback s τ p m x := by
  ext v
  simp only [constrainedPullback,
    IsingBulk.Anisotropic.NegativeCycles.densityForm_chainPullback,
    parameterHomotopy_periodic τ p m hp hm,
    parameterHomotopy_fderiv_periodic τ p m hp hm,
    constrainedLogDensity_periodic]

def homotopyBoxLower (n : ℕ) : Fin (n+1) → ℝ := Fin.cons 0 (fun _ => -Real.pi)
def homotopyBoxUpper (n : ℕ) : Fin (n+1) → ℝ := Fin.cons 1 (fun _ => Real.pi)

theorem homotopyBox_ordered (n : ℕ) : homotopyBoxLower n ≤ homotopyBoxUpper n := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · norm_num [homotopyBoxLower, homotopyBoxUpper]
  · simp only [homotopyBoxLower, homotopyBoxUpper, Fin.cons_succ]
    linarith [Real.pi_pos]

/-- Stokes on the complete constrained cylinder. Opposite angular faces cancel
by the proved periodicity of the actual pullback; no invariant-integral premise
or cutoff is used. -/
theorem constrained_whole_homotopy_caps (n : ℕ) (s : ℂ)
    (hS : 0 < (temperatureTrace s).im) (τ : ℝ) (hτ : 0 ≤ τ)
    (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (hp0 : ∀ x, 0 ≤ p x) (hm0 : ∀ x, 0 ≤ m x)
    (hps : ∀ x, Real.sin x ≤ 0 → p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → m x=0) :
    cylinderCapIntegral (constrainedPullback s τ p m)
      (homotopyBoxLower n) (homotopyBoxUpper n) 1 =
    cylinderCapIntegral (constrainedPullback s τ p m)
      (homotopyBoxLower n) (homotopyBoxUpper n) 0 := by
  have hhol (x) (hx : x ∈ Icc (homotopyBoxLower n) (homotopyBoxUpper n)) :
      DifferentiableAt ℂ (constrainedLogDensity n s) (parameterHomotopy τ p m x) := by
    apply constrainedLogDensity_differentiableAt
    intro i
    unfold parameterHomotopy
    rw [exp_constrained_homotopy]
    exact homotopy_complexW_im_pos hS hτ (hx.1 0) p m _ hp0 hm0 hps hms i
  have hboundary := holomorphic_chain_boundary_zero
    (densityForm (constrainedLogDensity n s)) (parameterHomotopy τ p m)
    (homotopyBox_ordered n)
    (fun x hx => densityForm_differentiableAt (hhol x hx))
    (fun x _ => ((parameterHomotopy_contDiff n τ p m hp hm).of_le (by simp)).contDiffAt)
  have hfaces (q : Fin n) :
      cylinderFaceFlux (constrainedPullback s τ p m)
        (homotopyBoxLower n) (homotopyBoxUpper n) q.succ = 0 := by
    unfold cylinderFaceFlux
    have he (x : Fin n → ℝ) :
        (q.succ.insertNth (homotopyBoxUpper n q.succ) x : Fin (n+1) → ℝ) =
          (q.succ.insertNth (homotopyBoxLower n q.succ) x : Fin (n+1) → ℝ)+Pi.single q.succ (2*Real.pi) := by
      funext i
      rcases q.succ.eq_self_or_eq_succAbove i with rfl | ⟨j,rfl⟩
      · simp [homotopyBoxUpper, homotopyBoxLower]
        ring
      · simp [Fin.succAbove_ne]
    simp_rw [he, constrainedPullback_periodic s τ p m hpp hmp]
    exact sub_self _
  change boxBoundaryFlux (constrainedPullback s τ p m)
    (homotopyBoxLower n) (homotopyBoxUpper n)=0 at hboundary
  rw [cylinderBoundaryFlux_caps] at hboundary
  simp only [hfaces, Finset.sum_const_zero, add_zero] at hboundary
  exact sub_eq_zero.mp hboundary

/-- The actual constrained angular Jacobian, in row-derivative convention.
Multiplication by −i converts logarithmic y coordinates to angular w coordinates. -/
def constrainedAngularJacobian {n : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => -Complex.I *
    (fderiv ℝ (parameterHomotopy τ p m) (Fin.cons lam θ) (Pi.single i.succ 1)) j

def deformedCoefficient (n : ℕ) (s : ℂ) (τ lam : ℝ) (p m : ℝ → ℝ) : ℂ :=
  ((Nat.factorial (n+1):ℂ)*(2*Real.pi:ℂ)^n)⁻¹ *
    ∫ θ in angularBox n,
      rootFreeDensity s (homotopyRoot τ lam p m (constrainedAngles θ)) *
        (constrainedAngularJacobian τ lam p m θ).det

theorem constrainedAngularJacobian_zero {n : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (θ : Fin n → ℝ) :
    constrainedAngularJacobian τ 0 p m θ = 1 := by
  have hH := (parameterHomotopy_contDiff n τ p m hp hm).differentiable (by simp)
  have hd (q : Fin n) :
      fderiv ℝ (parameterHomotopy τ p m) (Fin.cons 0 θ) (Pi.single q.succ 1) =
        fun j => if j=q then Complex.I else 0 := by
    have hh := (hH (Fin.cons 0 θ)).hasFDerivAt.comp_hasDerivAt_of_eq (θ q)
      (hasDerivAt_update (Fin.cons 0 θ) q.succ (θ q)) (by simp)
    have he : (fun t => parameterHomotopy τ p m (Function.update (Fin.cons 0 θ) q.succ t)) =
        fun t j => Complex.I*(Function.update θ q t j:ℂ) := by
      funext t j
      have hq : (0:Fin (n+1)) ≠ q.succ := (Fin.succ_ne_zero q).symm
      simp [parameterHomotopy, freeLogHomotopy, Function.update_apply, hq]
    simp only [Function.comp_def] at hh
    rw [he] at hh
    have hl : HasDerivAt (fun t j => Complex.I*(Function.update θ q t j:ℂ))
        (fun j => if j=q then Complex.I else 0) (θ q) := by
      apply hasDerivAt_pi.mpr
      intro j
      by_cases hj : j=q
      · subst j
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ q)).const_mul Complex.I
      · simpa [Function.update_of_ne hj, hj] using
          hasDerivAt_const (θ q) (Complex.I*(θ j:ℂ))
    exact hh.unique hl
  ext i j
  simp only [constrainedAngularJacobian, hd, Matrix.one_apply]
  by_cases hij : i=j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

theorem deformedCoefficient_zero (n : ℕ) (s : ℂ) (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    deformedCoefficient n s τ 0 p m = coefficient (n+1) s := by
  unfold deformedCoefficient coefficient
  congr 1
  apply setIntegral_congr_fun
  · exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  · intro θ _
    dsimp only
    rw [constrainedAngularJacobian_zero τ p m hp hm, Matrix.det_one, mul_one]
    have he : homotopyRoot τ 0 p m (constrainedAngles θ) =
        fun i => angleRoot (constrainedAngles θ i) := by
      funext i
      simp [homotopyRoot, angleRoot]
    rw [he, ← fullAngularDensity_eq_rootFreeDensity]

theorem deformedCoefficient_eq_cap (n : ℕ) (s : ℂ) (τ lam : ℝ) (p m : ℝ → ℝ) :
    deformedCoefficient n s τ lam p m =
      ((Nat.factorial (n+1):ℂ)*(2*Real.pi:ℂ)^n)⁻¹ * (-Complex.I)^n *
        cylinderCapIntegral (constrainedPullback s τ p m)
          (homotopyBoxLower n) (homotopyBoxUpper n) lam := by
  unfold deformedCoefficient
  have hbox : angularBox n =ᵐ[volume]
      Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi) :=
    Measure.univ_pi_Ioc_ae_eq_Icc
  rw [setIntegral_congr_set hbox]
  unfold cylinderCapIntegral
  simp only [homotopyBoxLower, homotopyBoxUpper, Function.comp_def,
    Fin.succAbove_zero, Fin.cons_succ, Fin.insertNth_zero', Fin.removeNth_zero,
    constrainedPullback, densityForm_chainPullback]
  rw [mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  have he : constrainedLogDensity n s (parameterHomotopy τ p m (Fin.cons lam θ)) =
      rootFreeDensity s (homotopyRoot τ lam p m (constrainedAngles θ)) := by
    unfold constrainedLogDensity parameterHomotopy
    simp only [Fin.cons_zero, Fin.cons_succ]
    congr 1
    funext i
    exact exp_constrained_homotopy τ lam p m θ i
  rw [he]
  let J : Matrix (Fin n) (Fin n) ℂ := fun i j =>
    fderiv ℝ (parameterHomotopy τ p m) (Fin.cons lam θ) (Pi.single i.succ 1) j
  have hm : constrainedAngularJacobian τ lam p m θ = (-Complex.I) • J := rfl
  rw [hm, Matrix.det_smul]
  simp only [Fintype.card_fin]
  change _ = _ * (_ * J.det)
  ring

/-- The exact whole-integral deformation asserted in Lemma 5.1. The conclusion
is the concrete manuscript coefficient, with its full density, all N−1 angular
integrals, and the actual constrained Jacobian. -/
theorem coefficient_eq_deformedCoefficient (n : ℕ) (s : ℂ)
    (hS : 0 < (temperatureTrace s).im) (τ : ℝ) (hτ : 0 ≤ τ)
    (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (hp0 : ∀ x, 0 ≤ p x) (hm0 : ∀ x, 0 ≤ m x)
    (hps : ∀ x, Real.sin x ≤ 0 → p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → m x=0) :
    coefficient (n+1) s = deformedCoefficient n s τ 1 p m := by
  rw [← deformedCoefficient_zero n s τ p m hp hm,
    deformedCoefficient_eq_cap, deformedCoefficient_eq_cap,
    constrained_whole_homotopy_caps n s hS τ hτ p m hp hm hpp hmp hp0 hm0 hps hms]

end
end IsingBulk.Preferred22
