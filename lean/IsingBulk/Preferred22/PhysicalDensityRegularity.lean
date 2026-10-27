import IsingBulk.Preferred22.MixedTransport
import IsingBulk.Preferred22.ZerothContinuity
import IsingBulk.Preferred22.AngularAnalytic

/-! Mixed regularity of the literal physical density and its genuine
real-angular/complex-parameter transport recursion. Square-root gauge
factors are eliminated by their exact determinant identity. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- The complete complex angular density is genuinely analytic at every
physical off-segment configuration, not just at real angles. -/
theorem preferred_complexAngularDensity_analyticAt {N : ℕ} (hN : 0<N)
    (s : ℂ) (w : Fin N → ℂ) (hs : s≠0)
    (hW : ∀ i, OffRealSegment (temperatureTrace s-Complex.cos (w i))) :
    AnalyticAt ℂ (@complexAngularDensity N) (s,w) := by
  let c : ℂ × (Fin N → ℂ) := (s,w)
  have hw (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.2 i) c :=
    (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt c)
  have hy (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => complexAngleRoot (x.2 i)) c :=
    (analyticAt_const.mul (hw i)).cexp
  have hS : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => temperatureTrace x.1) c :=
    analyticAt_fst.add (analyticAt_fst.inv hs)
  have hz (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => complexAngularRoots x i) c := by
    have hWi := hS.sub (Complex.analyticAt_cos.comp (hw i))
    exact (physicalRoot_analyticAt (hW i)).comp_of_eq hWi rfl
  have hzi (i : Fin N) : ‖complexAngularRoots c i‖<1 := physicalRoot_inside (hW i)
  have hden (i j : Fin N) : 1-complexAngularRoots c i*complexAngularRoots c j≠0 := by
    intro he
    have hh : complexAngularRoots c i*complexAngularRoots c j=1 := (sub_eq_zero.mp he).symm
    have hn : ‖complexAngularRoots c i*complexAngularRoots c j‖<1 := by
      rw [norm_mul]
      nlinarith [hzi i,hzi j,norm_nonneg (complexAngularRoots c i),norm_nonneg (complexAngularRoots c j)]
    simp [hh] at hn
  have hZ := Finset.univ.analyticAt_fun_prod (fun i _ => hz i)
  have hZ0 : 1-∏ i,complexAngularRoots c i≠0 := by
    have hprod : ‖∏ i,complexAngularRoots c i‖<1 := by
      rw [norm_prod]
      have hh := Finset.prod_lt_prod_of_nonempty₀
        (s := (Finset.univ : Finset (Fin N)))
        (f := fun i => ‖complexAngularRoots c i‖) (g := fun _ => (1:ℝ))
        (fun i _ => norm_pos_iff.mpr (physicalRoot_ne_zero _))
        (fun i _ => hzi i) ⟨⟨0,hN⟩,Finset.mem_univ _⟩
      simpa only [Finset.prod_const_one] using hh
    intro he
    have hh := (sub_eq_zero.mp he).symm
    rw [hh,norm_one] at hprod
    exact (lt_irrefl 1) hprod
  have hR (i j : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      rationalKernel (fun k => complexAngleRoot (x.2 k)) (complexAngularRoots x) i j) c :=
    ((hy i).sub (hy j)).div (analyticAt_const.sub ((hz i).mul (hz j))) (hden i j)
  have hdet : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      (rationalKernel (fun i => complexAngleRoot (x.2 i)) (complexAngularRoots x)).det) c := by
    simp only [Matrix.det_apply']
    exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
      analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hR (σ i) i)))
  have hratio := Finset.univ.analyticAt_fun_prod (fun i _ =>
    (hz i).div (hy i) (Complex.exp_ne_zero _))
  have hbody : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      ∏ i,oneBody (complexAngularRoots x i)) c := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (analyticAt_const.mul (hz i)).div (analyticAt_const.sub ((hz i).pow 2))
    change 1-(complexAngularRoots c i)^2≠0
    simpa only [pow_two] using hden i i
  exact (((analyticAt_const.add hZ).div (analyticAt_const.sub hZ) hZ0).mul
    ((analyticAt_const.mul hratio).mul hdet)).mul hbody

theorem preferredDeformedPhysicalDensity_eq_complex {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    preferredDeformedPhysicalDensity τ p m s θ=
      complexAngularDensity (s,deformedAngles τ p m θ) := by
  simp only [preferredDeformedPhysicalDensity,complexAngularDensity,complexAngularRoots,
    complexAngleRoot,gaugeKernel_det_normalization]
  rfl

/-- Genuine real smoothness of every source cutoff cell, including each
fixed left anchor. No complex continuation of a bump is used. -/
theorem preferredCellWeight_contDiff {N : ℕ} (cell : PreferredTransportCell N)
    (η p m r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (preferredCellWeight cell η p m r) := by
  cases cell with
  | right =>
    unfold preferredCellWeight preferredLowerWeight preferredRightWeight lowerWeight occupancy
    fun_prop
  | anchor a =>
    unfold preferredCellWeight preferredLowerWeight preferredAnchorWeight lowerWeight occupancy
    fun_prop

/-- The literal normalized physical seed is jointly C∞ in real angles and
the two real components of s at every actual physical configuration. -/
theorem preferredPhysicalSeed_contDiffAt {N : ℕ} (hN : 0<N)
    (cell : PreferredTransportCell N) (τ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hr : ContDiff ℝ ∞ r) (s : ℂ) (θ : Fin N → ℝ) (hs : s≠0)
    (hW : ∀ i, OffRealSegment (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i))) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredPhysicalSeed cell τ η p m r z.1 z.2) (s,θ) := by
  have hcoe : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
  have hw : ContDiff ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => deformedAngles τ p m z.2) := by
    apply contDiff_pi.mpr
    intro i
    unfold deformedAngles balancedShift occupancy
    fun_prop
  have hD : ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredDeformedPhysicalDensity τ p m z.1 z.2) (s,θ) := by
    simp_rw [preferredDeformedPhysicalDensity_eq_complex]
    exact ContDiffAt.comp (f := fun z : ℂ × (Fin N → ℝ) => (z.1,deformedAngles τ p m z.2))
      (g := @complexAngularDensity N) (s,θ)
      ((preferred_complexAngularDensity_analyticAt hN s _ hs hW).contDiffAt.restrict_scalars ℝ)
      (contDiffAt_fst.prodMk hw.contDiffAt)
  have hM : ContDiff ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => (preferredContourMatrix τ p m z.2).det) := by
    simp_rw [preferredContourMatrix_eq_full]
    exact (fullAngularJacobian_det_contDiff 1 τ p m hp hm).comp contDiff_snd
  have hweight : ContDiff ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      (preferredCellWeight cell η p m r z.2:ℂ)) :=
    hcoe.comp ((preferredCellWeight_contDiff cell η p m r hη hp hm hr).comp contDiff_snd)
  exact (((hweight.contDiffAt.mul hM.contDiffAt).mul hD).div_const _)

/-- Complex parameter analyticity of the same actual physical seed. -/
theorem preferredPhysicalSeed_parameter_analyticAt {N : ℕ} (hN : 0<N)
    (cell : PreferredTransportCell N) (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (hs : s≠0)
    (hW : ∀ i, OffRealSegment (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i))) :
    AnalyticAt ℂ (fun t : ℂ => preferredPhysicalSeed cell τ η p m r t θ) s := by
  have hD : AnalyticAt ℂ (fun t : ℂ => preferredDeformedPhysicalDensity τ p m t θ) s := by
    simp_rw [preferredDeformedPhysicalDensity_eq_complex]
    exact AnalyticAt.comp (f := fun t : ℂ => (t,deformedAngles τ p m θ))
      (g := @complexAngularDensity N) (preferred_complexAngularDensity_analyticAt hN s _ hs hW)
      (analyticAt_id.prod analyticAt_const)
  exact (analyticAt_const.mul hD).div_const

/-- The genuine physical transport step preserves mixed smoothness on an
open source domain; the angular derivative remains the literal real one. -/
theorem preferredTransportStep_mixed {N : ℕ}
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ) (A : ℂ → (Fin N → ℝ) → ℂ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hV : ∀ i, PreferredMixedSmoothOn (fun z => V z.1 z.2 i) Ω)
    (hA : PreferredMixedSmoothOn (fun z => A z.1 z.2) Ω) :
    PreferredMixedSmoothOn (fun z => preferredTransportStep V A z.1 z.2) Ω := by
  exact (hA.parameter hΩ).sub (PreferredMixedSmoothOn.sum
    (fun i => ((hV i).mul hA).coordinate hΩ i))

/-- All literal physical descendants inherit regularity from finite base
data. No derivative bound is assumed or concluded here. -/
theorem preferredTransportedDensity_mixed_of_base {N : ℕ}
    (cell : PreferredTransportCell N) (τ : ℝ) (η p m r : ℝ → ℝ)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hV : ∀ i, PreferredMixedSmoothOn
      (fun z => preferredSourceAngularField cell τ p m z.1 z.2 i) Ω)
    (hseed : PreferredMixedSmoothOn (fun z => preferredPhysicalSeed cell τ η p m r z.1 z.2) Ω)
    (j : ℕ) :
    PreferredMixedSmoothOn (fun z => preferredTransportedDensity cell τ η p m r j z.1 z.2) Ω := by
  induction j with
  | zero => exact hseed
  | succ j ih => exact preferredTransportStep_mixed _ _ Ω hΩ hV ih

end
end IsingBulk.Preferred22
