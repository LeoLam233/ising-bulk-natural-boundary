import IsingBulk.First.DominatedAnalyticIntegral
import IsingBulk.First.FormFactorAnalytic
import IsingBulk.First.ComplementSourcePhaseSmooth
import IsingBulk.First.ComplementMixedRegularity
import IsingBulk.First.ComplementFullPhaseJets

/-! Actual joint regularity and measurable jets of the full angular/auxiliary
exponential density on a fixed-radius damped complex parameter domain. -/
namespace IsingBulk.First
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff
attribute [local fun_prop] source_complexOfReal_contDiff

theorem dampingDomain_isOpen (r : ℝ) : IsOpen (dampingDomain r) :=
  isOpen_iff_mem_nhds.mpr (fun _ hs => dampingDomain_mem_nhds hs)

theorem sourceFactorDenominator_ne_zero_damped (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hs : s ∈ dampingDomain r)
    (u : DoubleAngularVector N) (f : SingularFactorIndex N) :
    sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0 := by
  have hx : ∀ i, ‖angleTuple r u.1 i‖ < 1 := fun _ => (anglePoint_norm hr.le _).trans_lt hr1
  have hy : ∀ i, ‖angleTuple r u.2 i‖ < 1 := fun _ => (anglePoint_norm hr.le _).trans_lt hr1
  rcases f with b | (⟨b,i,j⟩ | i)
  · cases b
    · exact one_sub_coordinateProduct_ne_zero hN hx
    · exact one_sub_coordinateProduct_ne_zero hN hy
  · cases b <;> by_cases hij : i < j
    · simpa only [sourceFactorDenominator, hij, ite_true] using one_sub_mul_ne_zero_of_norm_lt_one (hx i) (hx j)
    · simp only [sourceFactorDenominator, hij, ite_false, ne_eq, one_ne_zero, not_false_eq_true]
    · simpa only [sourceFactorDenominator, hij, ite_true] using one_sub_mul_ne_zero_of_norm_lt_one (hy i) (hy j)
    · simp only [sourceFactorDenominator, hij, ite_false, ne_eq, one_ne_zero, not_false_eq_true]
  · simpa only [sourceS_sub_angularDispersionTrace, sourceFactorDenominator] using
      angularDispersion_ne_zero hr hr1 hs u i

def sourceAuxiliaryDensity {N : ℕ} (r : ℝ) (w : DoubleAngularVector N → ℝ)
    (J : Finset (SingularFactorIndex N)) (s : ℂ)
    (p : DoubleAngularVector N × (J → ℝ)) : ℂ :=
  localizedRegularAmplitude r s w J p.1 * Complex.exp
    (sourcePhaseSum r s (fun _ => 1) (fun _ => 1) (fun f : J => f.1) p.2 p.1)

theorem sourceAuxiliaryDensity_analyticAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ)
    (J : Finset (SingularFactorIndex N)) (p : DoubleAngularVector N × (J → ℝ))
    {s : ℂ} (hs : s ∈ dampingDomain r) :
    AnalyticAt ℂ (fun t => sourceAuxiliaryDensity r w J t p) s := by
  have hA := localizedRegularAmplitude_analyticAt r w J p.1 hs.1
    (fun f _ => sourceFactorDenominator_ne_zero_damped N hN hr hr1 hs p.1 f)
  have hP : AnalyticAt ℂ (fun t => sourcePhaseSum r t (fun _ => 1) (fun _ => 1)
      (fun f : J => f.1) p.2 p.1) s := by
    have he : (fun t => sourcePhaseSum r t (fun _ => 1) (fun _ => 1)
        (fun f : J => f.1) p.2 p.1) = (fun t => sourceTemperaturePhase t *
          (dispersionAuxiliaryTotal (fun f : J => f.1) p.2 : ℂ) +
          sourcePhaseSum r 0 (fun _ => 1) (fun _ => 1) (fun f : J => f.1) p.2 p.1) :=
      funext (fun t => sourcePhaseSum_temperature_split r t _ _ _ _ _)
    rw [he]
    exact ((sourceTemperaturePhase_analyticAt hs.1).mul analyticAt_const).add analyticAt_const
  exact hA.mul hP.cexp

theorem sourceAuxiliaryDensity_joint_contDiffAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, validSourceFactor f)
    (p : DoubleAngularVector N × (J → ℝ)) {s : ℂ} (hs : s ∈ dampingDomain r) :
    ContDiffAt ℝ ∞ (fun q : (DoubleAngularVector N × (J → ℝ)) × ℂ =>
      sourceAuxiliaryDensity r w J q.2 q.1) (p,s) := by
  have hA := localizedRegularAmplitude_joint_contDiffAt w hw J r s p.1 hr.ne' hs.1
    (fun f _ => sourceFactorDenominator_ne_zero_damped N hN hr hr1 hs p.1 f)
  have hA' : ContDiffAt ℝ ∞ (fun q : (DoubleAngularVector N × (J → ℝ)) × ℂ =>
      localizedRegularAmplitude r q.2 w J q.1.1) (p,s) := by
    exact hA.comp (p,s) (show ContDiffAt ℝ ∞
      (fun q : (DoubleAngularVector N × (J → ℝ)) × ℂ => ((r,q.2),q.1.1)) (p,s) by fun_prop)
  have hP := sourcePhaseSum_joint_contDiffAt (fun f : J => f.1) (fun f => hJ f.1 f.2)
    r s p.2 p.1 hr.ne' hs.1
  have hP' : ContDiffAt ℝ ∞ (fun q : (DoubleAngularVector N × (J → ℝ)) × ℂ =>
      sourcePhaseSum r q.2 (fun _ => 1) (fun _ => 1) (fun f : J => f.1) q.1.2 q.1.1) (p,s) := by
    let g : (DoubleAngularVector N × (J → ℝ)) × ℂ → ((ℝ × ℂ) × (J → ℝ)) × DoubleAngularVector N :=
      fun q => (((r,q.2),q.1.2),q.1.1)
    have hg : ContDiffAt ℝ ∞ g (p,s) := by dsimp [g]; fun_prop
    exact hP.comp (p,s) (f := g) hg
  exact hA'.mul hP'.cexp

theorem parameterized_iteratedDeriv_contDiffAt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P × ℂ → ℂ) (p : P) (s : ℂ) (hA : ContDiffAt ℝ ∞ A (p,s))
    (hhol : ∀ᶠ q : P × ℂ in 𝓝 (p,s), AnalyticAt ℂ (fun z => A (q.1,z)) q.2) (j : ℕ) :
    ContDiffAt ℝ ∞ (fun q : P × ℂ => iteratedDeriv j (fun z => A (q.1,z)) q.2) (p,s) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hA
  | succ j ih =>
    simp_rw [iteratedDeriv_succ]
    apply contDiffAt_parameterized_complex_deriv p s ih
    filter_upwards [hhol] with q hq
    exact (analyticAt_iteratedDeriv hq j).differentiableAt

theorem sourceAuxiliaryDensity_jet_continuous (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, validSourceFactor f)
    {s : ℂ} (hs : s ∈ dampingDomain r) (j : ℕ) :
    Continuous (fun p : DoubleAngularVector N × (J → ℝ) =>
      iteratedDeriv j (fun t => sourceAuxiliaryDensity r w J t p) s) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hnear : ∀ᶠ q : (DoubleAngularVector N × (J → ℝ)) × ℂ in 𝓝 (p,s), q.2 ∈ dampingDomain r :=
    continuousAt_snd.preimage_mem_nhds (dampingDomain_mem_nhds hs)
  let A : (DoubleAngularVector N × (J → ℝ)) × ℂ → ℂ :=
    fun q => sourceAuxiliaryDensity r w J q.2 q.1
  have hA : ContDiffAt ℝ ∞ A (p,s) :=
    sourceAuxiliaryDensity_joint_contDiffAt N hN hr hr1 w hw J hJ p hs
  have hhol : ∀ᶠ q : (DoubleAngularVector N × (J → ℝ)) × ℂ in 𝓝 (p,s),
      AnalyticAt ℂ (fun z => A (q.1,z)) q.2 := by
    filter_upwards [hnear] with q hq
    exact sourceAuxiliaryDensity_analyticAt N hN hr hr1 w J q.1 hq
  have hj : ContDiffAt ℝ ∞ (fun q : (DoubleAngularVector N × (J → ℝ)) × ℂ =>
      iteratedDeriv j (fun z => A (q.1,z)) q.2) (p,s) :=
    parameterized_iteratedDeriv_contDiffAt A p s hA hhol j
  let g : DoubleAngularVector N × (J → ℝ) → (DoubleAngularVector N × (J → ℝ)) × ℂ :=
    fun q => (q,s)
  have hg : ContinuousAt g p := continuousAt_id.prodMk continuousAt_const
  have hc := hj.continuousAt.comp (f := g) hg
  exact hc

end
end IsingBulk.First
