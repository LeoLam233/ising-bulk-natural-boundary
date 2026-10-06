import IsingBulk.First.DominatedAnalyticIntegral
import IsingBulk.First.FormFactorAnalytic
import IsingBulk.First.ComplementSourcePhaseSmooth
import IsingBulk.First.ComplementMixedRegularity
import IsingBulk.First.ComplementFullPhaseJets
import IsingBulk.First.OnsiteRegularity
import IsingBulk.First.SourceAuxiliaryRegularity

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

theorem onsiteFactorDenominator_ne_zero_damped (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hs : s ∈ dampingDomain r)
    (u : DoubleAngularVector N) (f : SingularFactorIndex N) :
    onsiteFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0 := by
  cases f with
  | inl b => exact one_ne_zero
  | inr f => exact sourceFactorDenominator_ne_zero_damped N hN hr hr1 hs u (.inr f)

def onsiteAuxiliaryDensity {N : ℕ} (r : ℝ) (w : DoubleAngularVector N → ℝ)
    (J : Finset (SingularFactorIndex N)) (s : ℂ)
    (p : DoubleAngularVector N × (J → ℝ)) : ℂ :=
  onsiteRegularAmplitude r s w J p.1 * Complex.exp
    (sourcePhaseSum r s (fun _ => 1) (fun _ => 1) (fun f : J => f.1) p.2 p.1)

theorem onsiteAuxiliaryDensity_analyticAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ)
    (J : Finset (SingularFactorIndex N)) (p : DoubleAngularVector N × (J → ℝ))
    {s : ℂ} (hs : s ∈ dampingDomain r) :
    AnalyticAt ℂ (fun t => onsiteAuxiliaryDensity r w J t p) s := by
  have hA := onsiteRegularAmplitude_analyticAt r w J p.1 hs.1
    (fun f _ => onsiteFactorDenominator_ne_zero_damped N hN hr hr1 hs p.1 f)
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

theorem onsiteAuxiliaryDensity_joint_contDiffAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, validSourceFactor f)
    (p : DoubleAngularVector N × (J → ℝ)) {s : ℂ} (hs : s ∈ dampingDomain r) :
    ContDiffAt ℝ ∞ (fun q : (DoubleAngularVector N × (J → ℝ)) × ℂ =>
      onsiteAuxiliaryDensity r w J q.2 q.1) (p,s) := by
  have hA := onsiteRegularAmplitude_joint_contDiffAt w hw J r s p.1 hr.ne' hs.1
    (fun f _ => onsiteFactorDenominator_ne_zero_damped N hN hr hr1 hs p.1 f)
  have hA' : ContDiffAt ℝ ∞ (fun q : (DoubleAngularVector N × (J → ℝ)) × ℂ =>
      onsiteRegularAmplitude r q.2 w J q.1.1) (p,s) := by
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

theorem onsiteAuxiliaryDensity_jet_continuous (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, validSourceFactor f)
    {s : ℂ} (hs : s ∈ dampingDomain r) (j : ℕ) :
    Continuous (fun p : DoubleAngularVector N × (J → ℝ) =>
      iteratedDeriv j (fun t => onsiteAuxiliaryDensity r w J t p) s) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hnear : ∀ᶠ q : (DoubleAngularVector N × (J → ℝ)) × ℂ in 𝓝 (p,s), q.2 ∈ dampingDomain r :=
    continuousAt_snd.preimage_mem_nhds (dampingDomain_mem_nhds hs)
  let A : (DoubleAngularVector N × (J → ℝ)) × ℂ → ℂ :=
    fun q => onsiteAuxiliaryDensity r w J q.2 q.1
  have hA : ContDiffAt ℝ ∞ A (p,s) :=
    onsiteAuxiliaryDensity_joint_contDiffAt N hN hr hr1 w hw J hJ p hs
  have hhol : ∀ᶠ q : (DoubleAngularVector N × (J → ℝ)) × ℂ in 𝓝 (p,s),
      AnalyticAt ℂ (fun z => A (q.1,z)) q.2 := by
    filter_upwards [hnear] with q hq
    exact onsiteAuxiliaryDensity_analyticAt N hN hr hr1 w J q.1 hq
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
