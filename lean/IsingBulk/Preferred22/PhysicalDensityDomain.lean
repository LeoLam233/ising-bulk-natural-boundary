import IsingBulk.Preferred22.PhysicalDensityRegularity
import IsingBulk.Preferred22.PhysicalTransport

/-! A concrete open regularity domain for the actual physical transport.
Its membership is checked from the proved inverse-coordinate curvature and
actual source denominators. It assumes no descendant density regularity. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- The actual open physical regularity locus. The analytic predicates
refer to the explicit source functions, rather than to unspecified models. -/
def preferredPhysicalRegularDomain {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) :
    Set (ℂ × (Fin N → ℝ)) :=
  {z | 0<(temperatureTrace z.1).im ∧
    (∀ i, 0<(temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)).im) ∧
    (preferredContourMatrix τ p m z.2).det≠0 ∧
    AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredResidualCollective x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2) ∧
    ∀ i, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2 i)}

theorem preferredPhysicalRegularDomain_isOpen {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    IsOpen (preferredPhysicalRegularDomain (N := N) τ p m) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  rcases hz with ⟨hSi,hW,hM,hB,hU⟩
  have hs : z.1≠0 := by intro he; rw [he] at hSi; simp [temperatureTrace] at hSi
  have htrace : AnalyticAt ℂ temperatureTrace z.1 := analyticAt_id.add (analyticAt_id.inv hs)
  have ht : ContinuousAt (fun x : ℂ × (Fin N → ℝ) => temperatureTrace x.1) z :=
    htrace.continuousAt.comp continuousAt_fst
  have hχ := (preferredSourceCoordinate_contDiffAt τ p m hp hm z.1 z.2 hSi hW).continuousAt
  have hWc (i : Fin N) : ContinuousAt (fun x : ℂ × (Fin N → ℝ) =>
      (temperatureTrace x.1-Complex.cos (deformedAngles τ p m x.2 i)).im) z := by
    have hw : Continuous (fun x : ℂ × (Fin N → ℝ) => deformedAngles τ p m x.2 i) := by
      unfold deformedAngles balancedShift occupancy
      fun_prop
    exact Complex.continuous_im.continuousAt.comp
      (ht.sub (Complex.continuous_cos.continuousAt.comp hw.continuousAt))
  have hWnear : ∀ᶠ x : ℂ × (Fin N → ℝ) in 𝓝 z,
      ∀ i, 0<(temperatureTrace x.1-Complex.cos (deformedAngles τ p m x.2 i)).im := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuousAt_const : ContinuousAt (fun _ : ℂ × (Fin N → ℝ) => (0:ℝ)) z).eventually_lt
      (hWc i) (hW i)
  have hMc : ContinuousAt (fun x : ℂ × (Fin N → ℝ) => (preferredContourMatrix τ p m x.2).det) z :=
    ((preferredContourMatrix_contDiff τ p m hp hm).continuous.matrix_det.comp continuous_snd).continuousAt
  have hBc : ContinuousAt (fun x : ℂ × (Fin N → ℝ) =>
      (x.1,preferredSourceCoordinate τ p m x.1 x.2)) z := continuousAt_fst.prodMk hχ
  have hUnear : ∀ᶠ x : ℂ × (Fin N → ℝ) in 𝓝 z,
      ∀ i, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2)
        (x.1,preferredSourceCoordinate τ p m x.1 x.2 i) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuousAt_fst.prodMk (continuousAt_pi.mp hχ i)).tendsto.eventually
      (hU i).eventually_analyticAt
  exact ((continuousAt_const : ContinuousAt (fun _ : ℂ × (Fin N → ℝ) => (0:ℝ)) z).eventually_lt
    (Complex.continuous_im.continuousAt.comp ht) hSi).and
    (hWnear.and ((hMc.eventually_ne hM).and
      ((hBc.tendsto.eventually hB.eventually_analyticAt).and hUnear)))

/-- Membership in the concrete regularity locus follows from genuine
convex-domain curvature and the two literal source denominators. -/
theorem preferredPhysicalRegularDomain_of_curvature {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i,0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ q∈D,AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,q))
    (hcurv : ∀ q∈D,c≤(deriv (preferredSourceUQ s) q).re)
    (hq : ∀ i,preferredSourceCoordinate τ p m s θ i∈D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i))≠0)
    (hM : (preferredContourMatrix τ p m θ).det≠0) :
    (s,θ)∈preferredPhysicalRegularDomain τ p m :=
  ⟨hSi,hW,hM,preferredResidualCollective_analyticAt_of_curvature s
    (preferredSourceCoordinate τ p m s θ) D c hc hD hU
    (preferredMovingBranch_analyticAt_upper s hSi) hcurv hq hR,fun i => hU _ (hq i)⟩

/-- The actual angular representative is mixed smooth on the entire
concrete open locus, including every partial particle collision. -/
theorem preferredSourceAngularField_mixed_regularDomain {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (i : Fin N) :
    PreferredMixedSmoothOn (fun z => preferredSourceAngularField .right τ p m z.1 z.2 i)
      (preferredPhysicalRegularDomain τ p m) := by
  intro z hz
  rcases hz with ⟨hSi,hW,hM,hB,hU⟩
  have hχ := preferredSourceCoordinate_contDiffAt τ p m hp hm z.1 z.2 hSi hW
  have hχs := preferredSourceCoordinate_parameter_analyticAt τ p m z.1 z.2 hSi hW
  have hBc : ContDiffAt ℝ ∞ (fun x : ℂ × (Fin N → ℝ) =>
      preferredResidualCollective x.1 (preferredSourceCoordinate τ p m x.1 x.2)) z :=
    ContDiffAt.comp (f := fun x : ℂ × (Fin N → ℝ) => (x.1,preferredSourceCoordinate τ p m x.1 x.2))
      (g := fun x : ℂ × (Fin N → ℂ) => preferredResidualCollective x.1 x.2) z
      (hB.contDiffAt.restrict_scalars ℝ) (contDiffAt_fst.prodMk hχ)
  have hBs : AnalyticAt ℂ (fun t : ℂ => preferredResidualCollective t (preferredSourceCoordinate τ p m t z.2)) z.1 :=
    AnalyticAt.comp (f := fun t : ℂ => (t,preferredSourceCoordinate τ p m t z.2))
      (g := fun x : ℂ × (Fin N → ℂ) => preferredResidualCollective x.1 x.2) hB
      (analyticAt_id.prod hχs)
  obtain ⟨hvc,huc⟩ := preferredSourceInverseDerivatives_contDiffAt τ p m hp hm z.1 z.2 hSi hW hU
  obtain ⟨hvs,hus⟩ := preferredSourceInverseDerivatives_parameter_analyticAt τ p m z.1 z.2 hSi hW hU
  have hMinv : ContDiffAt ℝ ∞ (fun x : ℂ × (Fin N → ℝ) => (preferredContourMatrix τ p m x.2)⁻¹) z :=
    ContDiffAt.comp (f := fun x : ℂ × (Fin N → ℝ) => x.2)
      (g := fun θ : Fin N → ℝ => (preferredContourMatrix τ p m θ)⁻¹) z
      (preferredContourMatrix_inverse_contDiffAt τ p m hp hm z.2 hM) contDiffAt_snd
  constructor
  · simp only [preferredSourceAngularField,preferredAngularRepresentative,preferredResidualField,Matrix.mulVec,dotProduct]
    exact (ContDiffAt.sum (fun j _ =>
      (contDiffAt_pi.mp (contDiffAt_pi.mp hMinv i) j).mul
      ((contDiffAt_pi.mp huc j).add ((contDiffAt_pi.mp hvc j).mul (contDiffAt_pi.mp hBc j))))).neg
  · have hh : AnalyticAt ℂ (fun t : ℂ => preferredSourceAngularField .right τ p m t z.2 i) z.1 := by
      simp only [preferredSourceAngularField,preferredAngularRepresentative,preferredResidualField,Matrix.mulVec,dotProduct]
      exact (Finset.analyticAt_fun_sum Finset.univ (fun j _ => analyticAt_const.mul
        ((analyticAt_pi_iff.mp hus j).add ((analyticAt_pi_iff.mp hvs j).mul
          (analyticAt_pi_iff.mp hBs j))))).neg
    exact hh.differentiableAt

/-- Every actual physical descendant has proved mixed smoothness on the
same open source set. There is no all-order regularity premise. -/
theorem preferredTransportedDensity_mixed_regularDomain {N : ℕ} (hN : 0<N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r) (j : ℕ) :
    PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) => preferredTransportedDensity .right τ η p m r j z.1 z.2)
      (preferredPhysicalRegularDomain τ p m) := by
  apply preferredTransportedDensity_mixed_of_base .right τ η p m r _
    (preferredPhysicalRegularDomain_isOpen τ p m hp hm)
    (preferredSourceAngularField_mixed_regularDomain τ p m hp hm)
  intro z hz
  have hs : z.1≠0 := by intro he; have hh := hz.1; rw [he] at hh; simp [temperatureTrace] at hh
  have hw (i : Fin N) : OffRealSegment (temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)) :=
    Or.inl (hz.2.1 i).ne'
  exact ⟨preferredPhysicalSeed_contDiffAt hN .right τ η p m r hη hp hm hr z.1 z.2 hs hw,
    (preferredPhysicalSeed_parameter_analyticAt hN .right τ η p m r z.1 z.2 hs hw).differentiableAt⟩

/-- Primitive geometric conditions give genuine all-order physical density
regularity, for the literal source and real cutoffs. -/
theorem preferredTransportedDensity_regular_at_of_curvature {N : ℕ} (hN : 0<N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r) (s : ℂ) (θ : Fin N → ℝ)
    (hSi : 0<(temperatureTrace s).im)
    (hW : ∀ i,0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ q∈D,AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,q))
    (hcurv : ∀ q∈D,c≤(deriv (preferredSourceUQ s) q).re)
    (hq : ∀ i,preferredSourceCoordinate τ p m s θ i∈D)
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i))≠0)
    (hM : (preferredContourMatrix τ p m θ).det≠0) (j : ℕ) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => preferredTransportedDensity .right τ η p m r j z.1 z.2) (s,θ) ∧
      DifferentiableAt ℂ (fun t : ℂ => preferredTransportedDensity .right τ η p m r j t θ) s :=
  preferredTransportedDensity_mixed_regularDomain hN τ η p m r hη hp hm hr j (s,θ)
    (preferredPhysicalRegularDomain_of_curvature τ p m s θ hSi hW D c hc hD hU hcurv hq hR hM)

end
end IsingBulk.Preferred22
