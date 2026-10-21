import IsingBulk.HT.Lie.OnsitePullback
import IsingBulk.HT.Lie.OnsiteAmplitude
import IsingBulk.Tail.MixedDensityAllOrder

/-! A fixed-background onsite analytic model. The compact displacement is
identically zero; no selected branch or compact correction field is added. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets IsingBulk.Lie Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def onsiteModelMap {N : ℕ} (J : Finset (Fin N)) (s : ℂ) (φ : Fin N → ℂ)
    (p : ℂ × (Fin N → ℂ)) : MixedActiveSpace N :=
  (p.1-s,((fun i => if i∈J then p.2 i-φ i else 0),0))

def onsiteDisplacement {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (φ : Fin N → ℂ) (t : ℂ) (x : Fin N → ℝ) : MixedActiveSpace N :=
  onsiteModelMap J s φ (t,mixedHybridMap J f r τ lam t x)

def onsiteActiveVelocity {N : ℕ} (J : Finset (Fin N)) (s : ℂ) (φ : Fin N → ℂ)
    (i : Fin N) (u : MixedActiveSpace N) : ℂ :=
  if i∈J then mixedActiveBranch regularA s φ i u else 0

def onsiteRegularModel {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (φ : Fin N → ℂ) (F : MixedActiveSpace N → ℂ)
    (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  mixedHybridVolume J f r τ lam t x*F (onsiteDisplacement J f r τ lam s φ t x)

@[simp] theorem onsiteDisplacement_base {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (x : Fin N → ℝ) :
    onsiteDisplacement J f r τ lam s (fun i => mixedContourPhase f r τ lam s x i) s x=0 := by
  apply Prod.ext
  · simp [onsiteDisplacement,onsiteModelMap]
  · apply Prod.ext
    · funext i
      by_cases hi : i ∈ J <;>
        simp [onsiteDisplacement,onsiteModelMap,mixedHybridMap,hi]
    · rfl

theorem onsiteModelMap_analytic {N : ℕ} (J : Finset (Fin N)) (s : ℂ) (φ : Fin N → ℂ)
    (p : ℂ × (Fin N → ℂ)) : AnalyticAt ℂ (onsiteModelMap J s φ) p := by
  unfold onsiteModelMap
  apply AnalyticAt.prod
  · exact analyticAt_fst.sub analyticAt_const
  · apply AnalyticAt.prod
    · apply analyticAt_pi_iff.mpr
      intro i
      by_cases hi : i∈J
      · simp only [hi,ite_true]
        exact (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _).comp analyticAt_snd).sub analyticAt_const
      · simp only [hi,ite_false]
        exact analyticAt_const
    · exact analyticAt_const

theorem onsiteActiveVelocity_source {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (φ : Fin N → ℂ) (t : ℂ) (x : Fin N → ℝ)
    (hbranch : ∀ i∈J,Real.sin (x i)<0) (i : Fin N) :
    onsiteActiveVelocity J s φ i (onsiteDisplacement J f r τ lam s φ t x)=
      onsiteBranchField J f r τ lam t x i := by
  by_cases hi : i∈J
  · simp only [onsiteActiveVelocity,onsiteBranchField,hi,ite_true,mixedActiveBranch,
      onsiteDisplacement,onsiteModelMap,mixedHybridMap]
    have hs : s+(t-s)=t := by ring
    have hφ : φ i+(mixedContourPhase f r τ lam t x i-φ i)=mixedContourPhase f r τ lam t x i := by ring
    rw [hs,hφ]
    exact mixed_actual_regularA f hr τ lam t x i (hbranch i hi)
  · simp [onsiteActiveVelocity,onsiteBranchField,hi]

theorem onsiteRegularModel_differentiable {N : ℕ}
    (J : Finset (Fin N)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (φ : Fin N → ℂ) (t : ℂ) (x : Fin N → ℝ) (ht : t≠0)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : ∀ i∈J,0<(sourceW t (deformedPoint f r τ lam x i)).im)
    (F : MixedActiveSpace N → ℂ)
    (hF : DifferentiableAt ℂ F (onsiteDisplacement J f r τ lam s φ t x)) :
    DifferentiableAt ℂ (fun z => onsiteRegularModel J f r τ lam s φ F z x) t ∧
    DifferentiableAt ℝ (onsiteRegularModel J f r τ lam s φ F t) x := by
  exact onsiteHybridPullback_differentiable J f hr τ lam t x ht hp hm hW
    (fun z ψ => F (onsiteModelMap J s φ (z,ψ)))
    (hF.comp (t,mixedHybridMap J f r τ lam t x)
      (onsiteModelMap_analytic J s φ (t,mixedHybridMap J f r τ lam t x)).differentiableAt)

theorem onsiteRegularModel_lie {n : ℕ}
    (J : Finset (Fin (n+1))) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (φ : Fin (n+1) → ℂ) (t : ℂ) (x : Fin (n+1) → ℝ) (ht : t≠0)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ i∈J,deriv f.p (x i)=0 ∧ deriv f.m (x i)=0)
    (hW : ∀ i∈J,0<(sourceW t (deformedPoint f r τ lam x i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ lam x i-(deformedPoint f r τ lam x i)⁻¹≠0)
    (F : MixedActiveSpace (n+1) → ℂ)
    (hF : DifferentiableAt ℂ F (onsiteDisplacement J f r τ lam s φ t x)) :
    lieStep (onsiteBranchField J f r τ lam) (onsiteRegularModel J f r τ lam s φ F) t x=
      onsiteRegularModel J f r τ lam s φ
        (fun u => fderiv ℂ F u (mixedActiveParameterDirection (n+1))) t x := by
  have hh := onsiteHybridPullback_lie J f hr τ lam t x ht hp hm hplateau hW hg
    (fun z ψ => F (onsiteModelMap J s φ (z,ψ)))
    (hF.comp (t,mixedHybridMap J f r τ lam t x)
      (onsiteModelMap_analytic J s φ (t,mixedHybridMap J f r τ lam t x)).differentiableAt)
  have hmap : HasDerivAt (fun z => onsiteModelMap J s φ (z,mixedHybridMap J f r τ lam t x))
      (mixedActiveParameterDirection (n+1)) t := by
    simpa only [onsiteModelMap,mixedActiveParameterDirection,Function.comp_def, id_eq] using
      ((hasDerivAt_id t).sub_const s).prodMk
        ((hasDerivAt_const t (fun i => if i∈J then mixedHybridMap J f r τ lam t x i-φ i else (0:ℂ))).prodMk
          (hasDerivAt_const t (0:ℂ)))
  have hd := (hF.hasFDerivAt.comp_hasDerivAt t hmap).deriv
  simp only [Function.comp_def] at hd
  change lieStep _ (onsiteRegularModel J f r τ lam s φ F) t x =
    mixedHybridVolume J f r τ lam t x*
      deriv (fun z => F (onsiteModelMap J s φ (z,mixedHybridMap J f r τ lam t x))) t at hh
  rw [hd] at hh
  exact hh

def _root_.IsingBulk.Tail.MixedDensityJetTerm.onsiteValue {N : ℕ} (T : MixedDensityJetTerm N (MixedActiveSpace N))
    (J : Finset (Fin N)) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (φ : Fin N → ℂ) (w : (Fin N → ℝ) → ℝ) (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  (cutoffJet T.cutoff w x:ℂ)*onsiteRegularModel J f r τ lam s φ T.regularPart t x

/-- The generic sparse term list specializes to zero residuals. -/
def onsiteJetTerms {N : ℕ} (J : Finset (Fin N)) (s : ℂ) (φ : Fin N → ℂ)
    (F : MixedActiveSpace N → ℂ) (k : ℕ) : List (MixedDensityJetTerm N (MixedActiveSpace N)) :=
  mixedDensityJetTerms (mixedActiveParameterDirection N) 0 0 (fun _ => 0) (fun _ => 0)
    F (onsiteActiveVelocity J s φ) k

theorem _root_.IsingBulk.Tail.MixedDensityJetTerm.onsite_step {n : ℕ}
    (T : MixedDensityJetTerm (n+1) (MixedActiveSpace (n+1)))
    (J : Finset (Fin (n+1))) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (φ : Fin (n+1) → ℂ) (t : ℂ) (x : Fin (n+1) → ℝ) (ht : t≠0)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ i∈J,deriv f.p (x i)=0 ∧ deriv f.m (x i)=0)
    (hbranch : ∀ i∈J,Real.sin (x i)<0)
    (hW : ∀ i∈J,0<(sourceW t (deformedPoint f r τ lam x i)).im)
    (hg : ∀ i∈J,deformedPoint f r τ lam x i-(deformedPoint f r τ lam x i)⁻¹≠0)
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w)
    (hT : DifferentiableAt ℂ T.regularPart (onsiteDisplacement J f r τ lam s φ t x)) :
    lieStep (onsiteBranchField J f r τ lam) (T.onsiteValue J f r τ lam s φ w) t x =
      ((mixedDensityActions (n+1)).map (fun a =>
        (T.child (mixedActiveParameterDirection (n+1)) 0 0 (fun _ => 0) (fun _ => 0)
          (onsiteActiveVelocity J s φ) a).onsiteValue J f r τ lam s φ w t x)).sum := by
  have hd := onsiteRegularModel_differentiable J f hr τ lam s φ t x ht hp hm hW T.regularPart hT
  change lieStep (onsiteBranchField J f r τ lam)
    (fun z y => (cutoffJet T.cutoff w y:ℂ)*onsiteRegularModel J f r τ lam s φ T.regularPart z y) t x = _
  rw [lieStep_real_weight _ _ _ t x
    ((cutoffJet_contDiff T.cutoff w hw).differentiable (by simp) x) hd.1 hd.2
    (onsiteBranchField_spatial_differentiable J f hr τ lam t x hp hm hg),
    onsiteRegularModel_lie J f hr τ lam s φ t x ht hp hm hplateau hW hg T.regularPart hT,
    mixedDensityActions_sum]
  have hc (i : Fin (n+1)) :
      (T.child (mixedActiveParameterDirection (n+1)) 0 0 (fun _ => 0) (fun _ => 0)
        (onsiteActiveVelocity J s φ) (some i)).onsiteValue J f r τ lam s φ w t x =
      -(onsiteBranchField J f r τ lam t x i*(cutoffJet (i::T.cutoff) w x:ℂ)*
        onsiteRegularModel J f r τ lam s φ T.regularPart t x) := by
    dsimp only [MixedDensityJetTerm.child,MixedDensityJetTerm.onsiteValue,onsiteRegularModel]
    rw [onsiteActiveVelocity_source J f hr τ lam s φ t x hbranch i]
    ring
  simp_rw [hc]
  rw [Finset.sum_neg_distrib,← Finset.sum_mul]
  have hz : mixedRegularDensityStep (mixedActiveParameterDirection (n+1))
      0 0 (fun _ => 0) (fun _ => 0) T.regularPart =
      (fun u => fderiv ℂ T.regularPart u (mixedActiveParameterDirection (n+1))) := by
    funext u
    simp [mixedRegularDensityStep]
  simp only [MixedDensityJetTerm.child,MixedDensityJetTerm.onsiteValue,cutoffJet,hz]
  ring

end
end IsingBulk.HT.Lie
