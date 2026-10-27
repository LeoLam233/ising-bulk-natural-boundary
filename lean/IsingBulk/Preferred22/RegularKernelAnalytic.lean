import IsingBulk.Preferred22.RegularMarkedKernel
import IsingBulk.Preferred22.ComplexKernelBridge
import IsingBulk.Preferred22.ContourLegality

/-! Local analyticity of the literal regular kernel on actual physical
phases.  The root-in-disk condition proves every pair denominator nonzero;
no regularity is asserted across an artificial totalized zero quotient. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem phase_pair_sinh_ne {φ ψ : ℂ}
    (hφ : ‖Complex.exp (-Complex.I*φ)‖ < 1)
    (hψ : ‖Complex.exp (-Complex.I*ψ)‖ < 1) :
    Complex.sinh (Complex.I*(φ+ψ)/2) ≠ 0 := by
  intro hz
  have he : Complex.exp (-(Complex.I*(φ+ψ)/2))^2 =
      Complex.exp (-Complex.I*φ)*Complex.exp (-Complex.I*ψ) := by
    simp only [pow_two, ←Complex.exp_add]
    congr 1
    ring
  have hh := exp_sinh_identity (Complex.I*(φ+ψ)/2)
  rw [hz,mul_zero,he] at hh
  have hp : Complex.exp (-Complex.I*φ)*Complex.exp (-Complex.I*ψ)=1 :=
    (sub_eq_zero.mp hh.symm).symm
  have hn : ‖Complex.exp (-Complex.I*φ)*Complex.exp (-Complex.I*ψ)‖ < 1 := by
    rw [norm_mul]
    calc
      _ ≤ ‖Complex.exp (-Complex.I*φ)‖*1 :=
        mul_le_mul_of_nonneg_left hψ.le (norm_nonneg _)
      _ < 1 := by simpa using hφ
  rw [hp,norm_one] at hn
  exact (lt_irrefl 1) hn

theorem preferredRegularKernel_analyticAt {N : ℕ} (s : ℂ) (q : Fin N → ℂ)
    (hU : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q i))
    (hB : AnalyticAt ℂ preferredMovingBranch s)
    (hphase : ∀ i, ‖Complex.exp (-Complex.I*preferredRegularPhase s (q i))‖ < 1) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredRegularKernel z.1 z.2) (s,q) := by
  have hq (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => z.2 i) (s,q) :=
    (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt (s,q))
  have hu (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => preferredMovingInverse z.1 (z.2 i)) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (hU i) (analyticAt_fst.prod (hq i))
  have hb : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredMovingBranch z.1) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => z.1)
      (g := preferredMovingBranch) hB analyticAt_fst
  have hph (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => preferredRegularPhase z.1 (z.2 i)) (s,q) :=
    ((hq i).sub (hu i)).add hb
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  have hn := Complex.analyticAt_sin.comp (((hu i).sub (hu j)).div_const (c := (2:ℂ)))
  have hda : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) =>
      Complex.I*(preferredRegularPhase z.1 (z.2 i)+preferredRegularPhase z.1 (z.2 j))/2)
      (s,q) := (analyticAt_const.mul ((hph i).add (hph j))).div_const
  have hd := Complex.analyticAt_sinh.comp hda
  exact hn.fun_div hd (phase_pair_sinh_ne (hphase i) (hphase j))

theorem preferred_regular_physical_kernel_marked_expansion {N k : ℕ}
    (s : ℂ) (q : Fin N → ℂ)
    (hU : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q i))
    (hB : AnalyticAt ℂ preferredMovingBranch s)
    (hphase : ∀ i, ‖Complex.exp (-Complex.I*preferredRegularPhase s (q i))‖ < 1)
    (v : Fin k → ℂ × (Fin N → ℂ)) :
    iteratedFDeriv ℂ k (fun z : ℂ × (Fin N → ℂ) => (preferredRegularKernel z.1 z.2).det) (s,q) v =
      ∑ marks ∈ preferredKernelJetSupport N k,
        preferredKernelJetCoefficient s q v marks *
          preferredMarkedMinor (preferredRegularKernel s q) marks :=
  preferred_regular_kernel_grouped_marked_expansion s q
    ((preferredRegularKernel_analyticAt s q hU hB hphase).contDiffAt) v

theorem deformedAngles_re {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    (deformedAngles τ p m θ i).re = θ i := by
  simp [deformedAngles, Complex.mul_re]

/-- The literal regular phase agrees with the physical source phase on the
whole one-sided lifted contour, rather than only at the lower branch point. -/
theorem preferred_source_regular_phase_eq {N : ℕ}
    (s : ℂ) (τ : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) (δ : ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, -Real.pi-δ≤θ i ∧ θ i≤δ)
    (hW : ∀ i, 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (i : Fin N) :
    preferredRegularPhase s (preferredSourceCoordinate τ p m s θ i) =
      preferredSourcePhase τ p m s θ i := by
  have hInv := preferred_global_one_sided_inverse s (deformedAngles τ p m θ i) δ
    hδ hδπ hS hSδ
    (by simpa only [deformedAngles_re] using (hθ i).1)
    (by simpa only [deformedAngles_re] using (hθ i).2) (hW i)
  change preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i) =
    deformedAngles τ p m θ i at hInv
  rw [preferredRegularPhase,hInv,preferredSourceCoordinate]
  ring

/-- Local joint analyticity of the actual regular kernel at every point on
the complete one-sided balanced contour. Physical branch legality supplies
all pair denominators; no analyticity or tail bound is assumed. -/
theorem preferred_source_regular_kernel_analyticAt {N : ℕ}
    (s : ℂ) (τ : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) (δ : ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, -Real.pi-δ≤θ i ∧ θ i≤δ)
    (hτ : 0≤τ) (hp0 : ∀ x, 0≤p x) (hm0 : ∀ x, 0≤m x)
    (hps : ∀ x, Real.sin x≤0 → p x=0)
    (hms : ∀ x, 0≤Real.sin x → m x=0) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredRegularKernel z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ) := by
  have hW (i : Fin N) :
      0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im := by
    rw [←complexW_homotopyRoot_eq]
    exact homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1)
      p m θ hp0 hm0 hps hms i
  apply preferredRegularKernel_analyticAt
  · intro i
    exact preferred_global_one_sided_joint_analytic s (deformedAngles τ p m θ i) δ
      hδ hδπ hS hSi hSδ
      (by simpa only [deformedAngles_re] using (hθ i).1)
      (by simpa only [deformedAngles_re] using (hθ i).2) (hW i)
  · exact preferredMovingBranch_analyticAt_upper s hSi
  · intro i
    rw [preferred_source_regular_phase_eq s τ p m θ δ hδ hδπ hS hSδ hθ hW i]
    rw [preferredSourcePhase,preferredArccos_physical_upper _ (hW i)]
    exact physicalRoot_inside (Or.inl (hW i).ne')

theorem preferred_source_regular_kernel_marked_expansion {N k : ℕ}
    (s : ℂ) (τ : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) (δ : ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, -Real.pi-δ≤θ i ∧ θ i≤δ)
    (hτ : 0≤τ) (hp0 : ∀ x, 0≤p x) (hm0 : ∀ x, 0≤m x)
    (hps : ∀ x, Real.sin x≤0 → p x=0)
    (hms : ∀ x, 0≤Real.sin x → m x=0)
    (v : Fin k → ℂ × (Fin N → ℂ)) :
    iteratedFDeriv ℂ k (fun z : ℂ × (Fin N → ℂ) => (preferredRegularKernel z.1 z.2).det)
      (s,preferredSourceCoordinate τ p m s θ) v =
      ∑ marks ∈ preferredKernelJetSupport N k,
        preferredKernelJetCoefficient s (preferredSourceCoordinate τ p m s θ) v marks *
          preferredMarkedMinor (preferredRegularKernel s (preferredSourceCoordinate τ p m s θ)) marks :=
  preferred_regular_kernel_grouped_marked_expansion s _
    ((preferred_source_regular_kernel_analyticAt s τ p m θ δ hδ hδπ hS hSi hSδ hθ
      hτ hp0 hm0 hps hms).contDiffAt) v

end
end IsingBulk.Preferred22
