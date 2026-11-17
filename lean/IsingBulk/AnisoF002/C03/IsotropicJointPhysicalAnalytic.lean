import IsingBulk.AnisoF002.C03.IsotropicFullPhysicalHomotopy
import IsingBulk.AnisoF002.C03.RegularParameterJets

/-!
# Joint analyticity of the complete physical isotropic density

Temperature and every angle vary jointly. The physical small root
proves all one-body, pair, and product denominator conditions on the
whole upper-dispersion region; no additional analytic premise is used.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem isotropicBarePhysicalDensity_analytic_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (hN : 0 < N) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    {S : E → ℂ} {w : E → Fin N → ℂ} {p : E}
    (hS : AnalyticAt ℂ S p) (hw : ∀ i, AnalyticAt ℂ (fun q => w q i) p)
    (hupper : ∀ i, 0 < (isotropicDispersion (S p, w p i)).im) :
    AnalyticAt ℂ (fun q => isotropicBarePhysicalDensity (S q) σ (w q)) p := by
  have hd (i : Fin N) : AnalyticAt ℂ (fun q => isotropicDispersion (S q, w q i)) p :=
    hS.sub (Complex.analyticAt_cos.comp (hw i))
  have hr (i : Fin N) : AnalyticAt ℂ (fun q => isotropicInteriorRoot (S q, w q i)) p :=
    (isotropicInteriorRoot_analyticAt _ (hupper i)).comp
      (f := fun q => (S q, w q i)) (hS.prod (hw i))
  have hz (i : Fin N) : AnalyticAt ℂ (fun q => Complex.exp (w q i * Complex.I)) p :=
    ((hw i).mul analyticAt_const).cexp'
  have hp (i : Fin N) : AnalyticAt ℂ
      (fun q => upperPhysicalPhase (isotropicDispersion (S q, w q i))) p :=
    (upperPhysicalPhase_analyticAt _ (hupper i)).comp
      (f := fun q => isotropicDispersion (S q, w q i)) (hd i)
  have hb (i : Fin N) : AnalyticAt ℂ
      (fun q => (Complex.sinh (Complex.I * upperPhysicalPhase
        (isotropicDispersion (S q, w q i))))⁻¹) p := by
    apply (Complex.analyticAt_sinh.comp (analyticAt_const.mul (hp i))).inv
    change Complex.sinh (Complex.I * upperPhysicalPhase (isotropicDispersion (S p, w p i))) ≠ 0
    rw [mul_comm Complex.I, Complex.sinh_mul_I]
    exact mul_ne_zero (upperPhysicalPhase_sin_ne_zero _ (hupper i)) Complex.I_ne_zero
  have hpair (i j : Fin N) : AnalyticAt ℂ (fun q => canceledPair 1
      (isotropicInteriorRoot (S q, w q i)) (isotropicInteriorRoot (S q, w q j))
      (Complex.exp (w q i * Complex.I)) (Complex.exp (w q j * Complex.I))) p := by
    unfold canceledPair
    apply (((analyticAt_const.mul (((hz i).sub (hz j)).pow 2)).mul (hr i)).mul (hr j)).div
      (((hz i).mul (hz j)).mul ((analyticAt_const.sub ((hr i).mul (hr j))).pow 2))
    exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
      (pow_ne_zero _ (pair_root_denominator_ne_zero
        (upperEdgeRoot_norm_lt_one (hupper i)) (upperEdgeRoot_norm_lt_one (hupper j))))
  have hprod : AnalyticAt ℂ (fun q => ∏ i, isotropicInteriorRoot (S q, w q i)) p :=
    Finset.univ.analyticAt_fun_prod fun i _ => hr i
  unfold isotropicBarePhysicalDensity
  exact ((analyticAt_const.mul
    ((analyticAt_const.add (analyticAt_const.mul hprod)).div
      (analyticAt_const.sub (analyticAt_const.mul hprod))
      (physical_product_denominator_of_upper hN (S p) σ hσ (w p) hupper))).mul
      (Finset.univ.analyticAt_fun_prod fun i _ => hb i)).mul
        ((indexPairs N).analyticAt_fun_prod fun ij _ => hpair ij.1 ij.2)

theorem isotropicBarePhysicalDensity_joint_analyticAt {N : ℕ} (hN : 0 < N)
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1) (p : ℂ × (Fin N → ℂ))
    (hupper : ∀ i, 0 < (isotropicDispersion (p.1, p.2 i)).im) :
    AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) => isotropicBarePhysicalDensity q.1 σ q.2) p := by
  apply isotropicBarePhysicalDensity_analytic_parameter hN σ hσ analyticAt_fst _ hupper
  intro i
  exact (show (Fin N → ℂ) →L[ℂ] ℂ from ContinuousLinearMap.proj i).analyticAt _ |>.comp analyticAt_snd

theorem isotropic_physical_temperature_jets_continuous {N : ℕ} (hN : 0 < N)
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1) {S : ℂ} (hS : 0 < S.im) (j : ℕ) :
    Continuous (fun x : Fin N → ℝ => iteratedDeriv j
      (fun T => isotropicBarePhysicalDensity T σ (fun i => (x i : ℂ))) S) := by
  apply continuous_iff_continuousAt.2
  intro x
  have hu (i : Fin N) : 0 < (isotropicDispersion (S, (x i : ℂ))).im := by
    simpa only [isotropicDispersion, Complex.sub_im, ← Complex.ofReal_cos,
      Complex.ofReal_im, sub_zero] using hS
  have hj : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) =>
      iteratedDeriv j (fun T => isotropicBarePhysicalDensity T σ q.2) q.1)
      (S, fun i => (x i : ℂ)) :=
    parameterIteratedDeriv_analyticAt (isotropicBarePhysicalDensity_joint_analyticAt hN σ hσ _ hu) j
  have hm : ContinuousAt (fun y : Fin N → ℝ => (S, fun i => (y i : ℂ))) x :=
    continuousAt_const.prodMk (continuousAt_pi.2 fun i =>
      Complex.continuous_ofReal.continuousAt.comp (continuousAt_apply i x))
  exact hj.continuousAt.comp_of_eq
    (f := fun y : Fin N → ℝ => (S, fun i => (y i : ℂ))) hm rfl

end
end IsingBulk.AnisoF002.Isotropic
