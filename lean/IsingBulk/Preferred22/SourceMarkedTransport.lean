import IsingBulk.Preferred22.MarkedTransportRecursion
import IsingBulk.Preferred22.RegularKernelAnalytic

/-! Primitive physical geometry discharges the kernel and initial scalar
calculus premises in the marked transport recursion. These are genuine
positive-epsilon source statements, with all real cutoff derivatives retained. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false

theorem preferredSourceUQ_analyticAt_of_joint (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2) (s,q) := by
  apply (preferredParameterQJet_analyticAt 0 (s,q) hU).congr
  filter_upwards [hU.eventually_analyticAt] with z hz
  simpa only [iteratedDeriv_zero,preferredSourceUQ] using
    preferredParameterQJet_eq_iteratedDeriv 0 z.1 z.2 hz

theorem preferredRegularOneBody_analyticAt (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q))
    (hB : AnalyticAt ℂ preferredMovingBranch s)
    (hphase : ‖Complex.exp (-Complex.I*preferredRegularPhase s q)‖<1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredRegularOneBody z.1 z.2) (s,q) := by
  have hu := preferredSourceUQ_analyticAt_of_joint s q hU
  have hb : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingBranch z.1) (s,q) :=
    AnalyticAt.comp (f:=fun z : ℂ × ℂ => z.1) (g:=preferredMovingBranch) hB analyticAt_fst
  have hph : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2) (s,q) :=
    (analyticAt_snd.sub hU).add hb
  have hd : Complex.sinh (Complex.I*preferredRegularPhase s q)≠0 := by
    have hh := phase_pair_sinh_ne hphase hphase
    have he : Complex.I*(preferredRegularPhase s q+preferredRegularPhase s q)/2=
        Complex.I*preferredRegularPhase s q := by ring
    rw [he] at hh
    exact hh
  exact hu.fun_div (Complex.analyticAt_sinh.comp (analyticAt_const.mul hph)) hd

/-- The actual regular kernel and actual unmarked scalar coefficient have
both the complex parameter and every real angular derivative at each whole
one-sided balanced source point. No smoothness premise for these factors
survives in the statement. -/
theorem preferred_source_marked_factors_differentiable {N : ℕ}
    (s : ℂ) (τ δ : ℝ) (η p m r : ℝ → ℝ) (θ : Fin N → ℝ)
    (hη : Differentiable ℝ η) (hp : Differentiable ℝ p)
    (hm : Differentiable ℝ m) (hr : Differentiable ℝ r)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hτ : 0≤τ) (hp0 : ∀ x, 0≤p x) (hm0 : ∀ x, 0≤m x)
    (hps : ∀ x, Real.sin x≤0 → p x=0) (hms : ∀ x, 0≤Real.sin x → m x=0) :
    (DifferentiableAt ℂ (fun t => preferredSourceRegularKernel τ p m t θ) s ∧
      ∀ i, DifferentiableAt ℝ
        (fun x => preferredSourceRegularKernel τ p m s (Function.update θ i x)) (θ i)) ∧
    (DifferentiableAt ℂ (fun t => preferredRegularSeedCoefficient τ η p m r t θ) s ∧
      ∀ i, DifferentiableAt ℝ
        (fun x => preferredRegularSeedCoefficient τ η p m r s (Function.update θ i x)) (θ i)) := by
  classical
  have hW (i : Fin N) : 0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im := by
    rw [←complexW_homotopyRoot_eq]
    exact homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1) p m θ hp0 hm0 hps hms i
  have hχs : DifferentiableAt ℂ (fun t => preferredSourceCoordinate τ p m t θ) s :=
    differentiableAt_pi.mpr (fun i =>
      (preferredSourceCoordinate_parameter_hasDerivAt τ δ p m s θ i hδ hδπ hS hSi hSδ
        (hθ i) (hW i)).differentiableAt)
  have hχθ (j : Fin N) : DifferentiableAt ℝ
      (fun x => preferredSourceCoordinate τ p m s (Function.update θ j x)) (θ j) :=
    differentiableAt_pi.mpr (fun i =>
      (preferredSourceCoordinate_hasDerivAt τ δ p m hp hm s θ i j hδ hδπ hS hSδ
        (hθ i) (hW i)).differentiableAt)
  have hKa := preferred_source_regular_kernel_analyticAt s τ p m θ δ hδ hδπ hS hSi hSδ hθ
    hτ hp0 hm0 hps hms
  have hKs : DifferentiableAt ℂ (fun t => preferredSourceRegularKernel τ p m t θ) s :=
    DifferentiableAt.comp (f:=fun t : ℂ => (t,preferredSourceCoordinate τ p m t θ))
      (g:=fun z : ℂ × (Fin N → ℂ) => preferredRegularKernel z.1 z.2)
      s hKa.differentiableAt (differentiableAt_id.prodMk hχs)
  have hKθ (j : Fin N) : DifferentiableAt ℝ
      (fun x => preferredSourceRegularKernel τ p m s (Function.update θ j x)) (θ j) := by
    have ho : DifferentiableAt ℝ
        (fun z : ℂ × (Fin N → ℂ) => preferredRegularKernel z.1 z.2)
        (s,preferredSourceCoordinate τ p m s (Function.update θ j (θ j))) := by
      simpa only [Function.update_eq_self] using hKa.differentiableAt.restrictScalars ℝ
    exact DifferentiableAt.comp
      (f:=fun x : ℝ => (s,preferredSourceCoordinate τ p m s (Function.update θ j x)))
      (g:=fun z : ℂ × (Fin N → ℂ) => preferredRegularKernel z.1 z.2)
      (θ j) ho ((differentiableAt_const s).prodMk (hχθ j))
  have hbody (i : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × ℂ => preferredRegularOneBody z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ i) := by
    apply preferredRegularOneBody_analyticAt
    · exact preferred_global_one_sided_joint_analytic s (deformedAngles τ p m θ i) δ
        hδ hδπ hS hSi hSδ (by simpa only [deformedAngles_re] using (hθ i).1)
        (by simpa only [deformedAngles_re] using (hθ i).2) (hW i)
    · exact preferredMovingBranch_analyticAt_upper s hSi
    · rw [preferred_source_regular_phase_eq s τ p m θ δ hδ hδπ hS hSδ hθ hW i]
      rw [preferredSourcePhase,preferredArccos_physical_upper _ (hW i)]
      exact physicalRoot_inside (Or.inl (hW i).ne')
  have hbodyS (i : Fin N) : DifferentiableAt ℂ
      (fun t => preferredRegularOneBody t (preferredSourceCoordinate τ p m t θ i)) s :=
    DifferentiableAt.comp (f:=fun t : ℂ => (t,preferredSourceCoordinate τ p m t θ i))
      (g:=fun z : ℂ × ℂ => preferredRegularOneBody z.1 z.2) s (hbody i).differentiableAt
      (differentiableAt_id.prodMk (differentiableAt_pi.mp hχs i))
  have hbodyθ (i j : Fin N) : DifferentiableAt ℝ
      (fun x => preferredRegularOneBody s (preferredSourceCoordinate τ p m s (Function.update θ j x) i))
      (θ j) := by
    have ho : DifferentiableAt ℝ (fun z : ℂ × ℂ => preferredRegularOneBody z.1 z.2)
        (s,preferredSourceCoordinate τ p m s (Function.update θ j (θ j)) i) := by
      simpa only [Function.update_eq_self] using (hbody i).differentiableAt.restrictScalars ℝ
    exact DifferentiableAt.comp
      (f:=fun x : ℝ => (s,preferredSourceCoordinate τ p m s (Function.update θ j x) i))
      (g:=fun z : ℂ × ℂ => preferredRegularOneBody z.1 z.2)
      (θ j) ho ((differentiableAt_const s).prodMk (differentiableAt_pi.mp (hχθ j) i))
  refine ⟨⟨hKs,hKθ⟩,?_,?_⟩
  · exact ((differentiableAt_const _).mul (DifferentiableAt.fun_finsetProd
      (fun i _ => hbodyS i))).div_const _
  · intro j
    have hw : DifferentiableAt ℝ (fun x => preferredCellWeight .right η p m r (Function.update θ j x)) (θ j) := by
      have hweight : Differentiable ℝ (fun v : Fin N → ℝ => preferredCellWeight .right η p m r v) := by
        unfold preferredCellWeight preferredLowerWeight preferredRightWeight lowerWeight occupancy
        fun_prop
      apply hweight.differentiableAt.comp (θ j)
      apply differentiableAt_pi.mpr
      intro i
      by_cases hij : i=j
      · subst i
        simp only [Function.update_self]
        exact differentiableAt_id
      · simpa only [Function.update_of_ne hij] using (differentiableAt_const (𝕜:=ℝ) (θ i) (x:=θ j))
    have hwc := Complex.differentiable_ofReal.differentiableAt.comp (θ j) hw
    exact (hwc.mul (DifferentiableAt.fun_finsetProd (fun i _ => hbodyθ i j))).div_const _

/-- The first actual regular scalar descendant has the source-specific
signed-minor expansion with all factor-calculus premises proved from the
physical contour and the original differentiable real cutoffs. -/
theorem preferred_first_source_marked_expansion {N : ℕ}
    (s : ℂ) (τ δ : ℝ) (η p m r : ℝ → ℝ) (θ : Fin N → ℝ)
    (hη : Differentiable ℝ η) (hp : Differentiable ℝ p)
    (hm : Differentiable ℝ m) (hr : Differentiable ℝ r)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hτ : 0≤τ) (hp0 : ∀ x, 0≤p x) (hm0 : ∀ x, 0≤m x)
    (hps : ∀ x, Real.sin x≤0 → p x=0) (hms : ∀ x, 0≤Real.sin x → m x=0) :
    preferredRegularTransportedScalar τ η p m r 1 s θ =
      preferredRegularTransportStep τ p m (preferredRegularSeedCoefficient τ η p m r) s θ *
        preferredMarkedMinor (preferredSourceRegularKernel τ p m s θ) [] +
      ∑ a : Fin N × Fin N,
        (preferredRegularSeedCoefficient τ η p m r s θ*preferredKernelMaterialEntry τ p m s θ a) *
          preferredMarkedMinor (preferredSourceRegularKernel τ p m s θ) [a] := by
  obtain ⟨⟨hKs,hKθ⟩,hAs,hAθ⟩ := preferred_source_marked_factors_differentiable s τ δ η p m r θ
    hη hp hm hr hδ hδπ hS hSi hSδ hθ hτ hp0 hm0 hps hms
  have he : preferredRegularSeed (N:=N) τ η p m r =
      fun t x => preferredRegularSeedCoefficient τ η p m r t x *
        preferredMarkedMinor (preferredSourceRegularKernel τ p m t x) [] := by
    funext t x
    exact preferredRegularSeed_eq_empty_minor τ η p m r t x
  change preferredRegularTransportStep τ p m (preferredRegularSeed τ η p m r) s θ = _
  rw [he]
  exact preferredRegularTransportStep_marked τ p m _ s θ [] hAs hAθ hKs hKθ

end
end IsingBulk.Preferred22
