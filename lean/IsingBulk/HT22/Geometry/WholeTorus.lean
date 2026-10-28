import IsingBulk.HT22.Geometry.BalancedHomotopy
import IsingBulk.Preferred22.ContourDeformation

/-!
# HT22: full signed constrained torus deformation, before localization

This is a density-generic Stokes theorem, not reuse of the LT even-density
coefficient identity.  The actual affine constraint and its balanced smooth
homotopy are explicit.  The only analytic hypothesis is holomorphicity of the
chosen density along this homotopy; a concrete odd-density application must
prove that hypothesis from its denominators.
-/

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped BigOperators ContDiff Topology
open Set Filter MeasureTheory IsingBulk.Preferred22
open IsingBulk.Anisotropic.NegativeCycles

def signedComplex {n : ℕ} (a : ℝ) (x : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.snoc x (Complex.I * (a : ℂ) - ∑ i, x i)

def signedFreeLogHomotopy {n : ℕ} (a τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) : Fin n → ℂ :=
  fun j => Complex.I * (θ j : ℂ) + (lam : ℂ) *
    (balancedShift τ p m (signedAngles a θ) j.castSucc : ℂ)

theorem signed_log_extension {n : ℕ} (a τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) :
    signedComplex a (signedFreeLogHomotopy a τ lam p m θ) =
      fun i => Complex.I * (signedAngles a θ i : ℂ) +
        (lam : ℂ) * (balancedShift τ p m (signedAngles a θ) i : ℂ) := by
  have hs := balancedShift_sum τ p m (signedAngles a θ)
  rw [Fin.sum_univ_castSucc] at hs
  have hl : balancedShift τ p m (signedAngles a θ) (Fin.last n) =
      -∑ i : Fin n, balancedShift τ p m (signedAngles a θ) i.castSucc := by linarith
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [signedComplex, Fin.snoc_last, signedFreeLogHomotopy]
    rw [hl]
    simp only [signedAngles, Fin.snoc_last, Finset.sum_add_distrib,
      ← Finset.mul_sum, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_sum]
    ring
  · simp only [signedComplex, Fin.snoc_castSucc, signedFreeLogHomotopy,
      signedAngles, Fin.snoc_castSucc]

theorem signed_exp_homotopy {n : ℕ} (a τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) (i : Fin (n + 1)) :
    Complex.exp (signedComplex a (signedFreeLogHomotopy a τ lam p m θ) i) =
      homotopyRoot τ lam p m (signedAngles a θ) i := by
  rw [signed_log_extension]
  rfl

theorem signedAngles_contDiff (n : ℕ) (a : ℝ) :
    ContDiff ℝ ∞ (@signedAngles n a) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [signedAngles, Fin.snoc_last]
    fun_prop
  · simp only [signedAngles, Fin.snoc_castSucc]
    fun_prop

theorem signedComplex_contDiff (n : ℕ) (a : ℝ) :
    ContDiff ℂ ∞ (@signedComplex n a) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [signedComplex, Fin.snoc_last]
    fun_prop
  · simp only [signedComplex, Fin.snoc_castSucc]
    fun_prop

theorem signedFreeLogHomotopy_contDiff (n : ℕ) (a τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (fun x : ℝ × (Fin n → ℝ) => signedFreeLogHomotopy a τ x.1 p m x.2) := by
  have hs := (balancedShift_contDiff (n+1) τ p m hp hm).comp (signedAngles_contDiff n a)
  have ho : ContDiff ℝ ∞ Complex.ofReal := Complex.ofRealCLM.contDiff
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_const.mul (ho.comp ((contDiff_apply ℝ ℝ i).comp contDiff_snd))).add
    ((ho.comp contDiff_fst).mul
      (ho.comp (((contDiff_apply ℝ ℝ i.castSucc).comp hs).comp contDiff_snd)))

def signedParameterHomotopy {n : ℕ} (a τ : ℝ) (p m : ℝ → ℝ)
    (x : Fin (n+1) → ℝ) : Fin n → ℂ :=
  signedFreeLogHomotopy a τ (x 0) p m (fun i => x i.succ)

theorem signedParameterHomotopy_contDiff (n : ℕ) (a τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (@signedParameterHomotopy n a τ p m) := by
  change ContDiff ℝ ∞ ((fun x : ℝ × (Fin n → ℝ) => signedFreeLogHomotopy a τ x.1 p m x.2) ∘
    (fun x : Fin (n+1) → ℝ => (x 0, fun i => x i.succ)))
  exact (signedFreeLogHomotopy_contDiff n a τ p m hp hm).comp (by fun_prop)

theorem signed_bump_periodic {n : ℕ} (a : ℝ) (p : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (θ : Fin n → ℝ) (q : Fin n) :
    (fun i => p (signedAngles a (θ+Pi.single q (2*Real.pi)) i)) =
      fun i => p (signedAngles a θ i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [signedAngles, Fin.snoc_last, Pi.add_apply, Finset.sum_add_distrib]
    rw [Fintype.sum_pi_single']
    rw [show a - ((∑ j, θ j) + 2*Real.pi) = (a - ∑ j, θ j) - 2*Real.pi by ring]
    exact hp.sub_eq _
  · simp only [signedAngles, Fin.snoc_castSucc, Pi.add_apply]
    by_cases hj : j=q
    · subst j
      simpa using hp (θ q)
    · simp [hj]

theorem signed_shift_periodic {n : ℕ} (a τ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (θ : Fin n → ℝ) (q : Fin n) :
    balancedShift τ p m (signedAngles a (θ+Pi.single q (2*Real.pi))) =
      balancedShift τ p m (signedAngles a θ) := by
  have hp' := signed_bump_periodic a p hp θ q
  have hm' := signed_bump_periodic a m hm θ q
  funext i
  have hpi := congrFun hp' i
  have hmi := congrFun hm' i
  have hP : occupancy p (signedAngles a (θ+Pi.single q (2*Real.pi))) =
      occupancy p (signedAngles a θ) := congrArg (fun f : Fin (n+1) → ℝ => ∑ i, f i) hp'
  have hQ : occupancy m (signedAngles a (θ+Pi.single q (2*Real.pi))) =
      occupancy m (signedAngles a θ) := congrArg (fun f : Fin (n+1) → ℝ => ∑ i, f i) hm'
  simp only [balancedShift, hP, hQ, hpi, hmi]

theorem signedFreeLogHomotopy_periodic {n : ℕ} (a τ lam : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (θ : Fin n → ℝ) (q : Fin n) :
    signedFreeLogHomotopy a τ lam p m (θ+Pi.single q (2*Real.pi)) =
      signedFreeLogHomotopy a τ lam p m θ + Pi.single q (2*Real.pi*Complex.I) := by
  unfold signedFreeLogHomotopy
  rw [signed_shift_periodic a τ p m hp hm]
  funext i
  by_cases hi : i=q
  · subst i
    simp
    ring
  · simp [hi]

theorem signedParameterHomotopy_periodic {n : ℕ} (a τ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (x : Fin (n+1) → ℝ) (q : Fin n) :
    signedParameterHomotopy a τ p m (x+Pi.single q.succ (2*Real.pi)) =
      signedParameterHomotopy a τ p m x + Pi.single q (2*Real.pi*Complex.I) := by
  have hzero : (x+Pi.single q.succ (2*Real.pi) : Fin (n+1) → ℝ) 0 = x 0 := by
    simp [Fin.succ_ne_zero]
  have htail : (fun i => (x+Pi.single q.succ (2*Real.pi) : Fin (n+1) → ℝ) i.succ) =
      (fun i => x i.succ)+Pi.single q (2*Real.pi) := by
    funext i
    simp [Pi.single_apply, Fin.succ_inj]
  unfold signedParameterHomotopy
  rw [hzero, htail, signedFreeLogHomotopy_periodic a τ (x 0) p m hp hm]

theorem signedParameterHomotopy_fderiv_periodic {n : ℕ} (a τ : ℝ) (p m : ℝ → ℝ)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (x : Fin (n+1) → ℝ) (q : Fin n) :
    fderiv ℝ (signedParameterHomotopy a τ p m) (x+Pi.single q.succ (2*Real.pi)) =
      fderiv ℝ (signedParameterHomotopy a τ p m) x := by
  have he := congrArg (fun f : (Fin (n+1) → ℝ) → (Fin n → ℂ) => fderiv ℝ f x)
    (funext (fun y => signedParameterHomotopy_periodic a τ p m hp hm y q))
  rwa [fderiv_comp_add_right, fderiv_add_const] at he

theorem signed_exp_periodic {n : ℕ} (a : ℝ) (x : Fin n → ℂ) (q : Fin n) :
    (fun i => Complex.exp (signedComplex a (x+Pi.single q (2*Real.pi*Complex.I)) i)) =
      fun i => Complex.exp (signedComplex a x i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [signedComplex, Fin.snoc_last, Pi.add_apply, Finset.sum_add_distrib]
    rw [Fintype.sum_pi_single']
    rw [show Complex.I * (a : ℂ) - ((∑ i, x i) + 2*Real.pi*Complex.I) =
      (Complex.I * (a : ℂ) - ∑ i, x i) - 2*Real.pi*Complex.I by ring]
    simp [Complex.exp_sub, Complex.exp_two_pi_mul_I]
  · simp only [signedComplex, Fin.snoc_castSucc, Pi.add_apply]
    by_cases hj : j=q
    · subst j
      simp [Complex.exp_add, Complex.exp_two_pi_mul_I]
    · simp [hj]

def signedPullback {n : ℕ} (f : (Fin n → ℂ) → ℂ) (a τ : ℝ) (p m : ℝ → ℝ) :=
  chainPullback (densityForm f) (signedParameterHomotopy a τ p m)

theorem signedPullback_periodic {n : ℕ} (f : (Fin n → ℂ) → ℂ) (a τ : ℝ)
    (p m : ℝ → ℝ)
    (hf : ∀ x q, f (x+Pi.single q (2*Real.pi*Complex.I)) = f x)
    (hp : Function.Periodic p (2*Real.pi)) (hm : Function.Periodic m (2*Real.pi))
    (x : Fin (n+1) → ℝ) (q : Fin n) :
    signedPullback f a τ p m (x+Pi.single q.succ (2*Real.pi)) =
      signedPullback f a τ p m x := by
  ext v
  simp only [signedPullback, densityForm_chainPullback,
    signedParameterHomotopy_periodic a τ p m hp hm,
    signedParameterHomotopy_fderiv_periodic a τ p m hp hm, hf]

/-- Stokes is applied to the entire closed signed torus.  No real bump is
analytically continued and no partition weight appears in the density. -/
theorem signed_whole_homotopy_caps (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (a τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (hf : ∀ x q, f (x+Pi.single q (2*Real.pi*Complex.I)) = f x)
    (hhol : ∀ x ∈ Icc (homotopyBoxLower n) (homotopyBoxUpper n),
      DifferentiableAt ℂ f (signedParameterHomotopy a τ p m x)) :
    cylinderCapIntegral (signedPullback f a τ p m)
      (homotopyBoxLower n) (homotopyBoxUpper n) 1 =
    cylinderCapIntegral (signedPullback f a τ p m)
      (homotopyBoxLower n) (homotopyBoxUpper n) 0 := by
  have hboundary := holomorphic_chain_boundary_zero
    (densityForm f) (signedParameterHomotopy a τ p m) (homotopyBox_ordered n)
    (fun x hx => densityForm_differentiableAt (hhol x hx))
    (fun x _ => ((signedParameterHomotopy_contDiff n a τ p m hp hm).of_le (by simp)).contDiffAt)
  have hfaces (q : Fin n) :
      cylinderFaceFlux (signedPullback f a τ p m)
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
    simp_rw [he, signedPullback_periodic f a τ p m hf hpp hmp]
    exact sub_self _
  change boxBoundaryFlux (signedPullback f a τ p m)
    (homotopyBoxLower n) (homotopyBoxUpper n) = 0 at hboundary
  rw [cylinderBoundaryFlux_caps] at hboundary
  simp only [hfaces, Finset.sum_const_zero, add_zero] at hboundary
  exact sub_eq_zero.mp hboundary

end
end IsingBulk.HT22.Geometry
