import IsingBulk.Preferred22.PhysicalDensityRegularity
import IsingBulk.Preferred22.TransportSupport
import IsingBulk.Preferred22.PhysicalTransport

/-! The actual open physical regularity domain for each named source cell.
The anchored specialization below uses the literal rational anchor field;
no collective full-equality denominator is introduced for that cell. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- The actual open physical regularity locus. The analytic predicates
refer to the explicit source functions, rather than to unspecified models. -/
def preferredCellRegularDomain {N : ℕ} (cell : PreferredTransportCell N) (τ : ℝ) (p m : ℝ → ℝ) :
    Set (ℂ × (Fin N → ℝ)) :=
  {z | 0<(temperatureTrace z.1).im ∧
    (∀ i, 0<(temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)).im) ∧
    (preferredContourMatrix τ p m z.2).det≠0 ∧
    AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredResidualField cell x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2) ∧
    ∀ i, AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2 i)}

theorem preferredCellRegularDomain_isOpen {N : ℕ} (cell : PreferredTransportCell N) (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) :
    IsOpen (preferredCellRegularDomain cell τ p m) := by
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

/-- The actual angular representative is mixed smooth on the entire
concrete open locus, including every partial particle collision. -/
theorem preferredSourceAngularField_mixed_cellDomain {N : ℕ} (cell : PreferredTransportCell N)
    (τ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (i : Fin N) :
    PreferredMixedSmoothOn (fun z => preferredSourceAngularField cell τ p m z.1 z.2 i)
      (preferredCellRegularDomain cell τ p m) := by
  intro z hz
  rcases hz with ⟨hSi,hW,hM,hB,hU⟩
  have hχ := preferredSourceCoordinate_contDiffAt τ p m hp hm z.1 z.2 hSi hW
  have hχs := preferredSourceCoordinate_parameter_analyticAt τ p m z.1 z.2 hSi hW
  have hBc : ContDiffAt ℝ ∞ (fun x : ℂ × (Fin N → ℝ) =>
      preferredResidualField cell x.1 (preferredSourceCoordinate τ p m x.1 x.2)) z :=
    ContDiffAt.comp (f := fun x : ℂ × (Fin N → ℝ) => (x.1,preferredSourceCoordinate τ p m x.1 x.2))
      (g := fun x : ℂ × (Fin N → ℂ) => preferredResidualField cell x.1 x.2) z
      (hB.contDiffAt.restrict_scalars ℝ) (contDiffAt_fst.prodMk hχ)
  have hBs : AnalyticAt ℂ (fun t : ℂ => preferredResidualField cell t (preferredSourceCoordinate τ p m t z.2)) z.1 :=
    AnalyticAt.comp (f := fun t : ℂ => (t,preferredSourceCoordinate τ p m t z.2))
      (g := fun x : ℂ × (Fin N → ℂ) => preferredResidualField cell x.1 x.2) hB
      (analyticAt_id.prod hχs)
  obtain ⟨hvc,huc⟩ := preferredSourceInverseDerivatives_contDiffAt τ p m hp hm z.1 z.2 hSi hW hU
  obtain ⟨hvs,hus⟩ := preferredSourceInverseDerivatives_parameter_analyticAt τ p m z.1 z.2 hSi hW hU
  have hMinv : ContDiffAt ℝ ∞ (fun x : ℂ × (Fin N → ℝ) => (preferredContourMatrix τ p m x.2)⁻¹) z :=
    ContDiffAt.comp (f := fun x : ℂ × (Fin N → ℝ) => x.2)
      (g := fun θ : Fin N → ℝ => (preferredContourMatrix τ p m θ)⁻¹) z
      (preferredContourMatrix_inverse_contDiffAt τ p m hp hm z.2 hM) contDiffAt_snd
  constructor
  · simp only [preferredSourceAngularField,preferredAngularRepresentative,Matrix.mulVec,dotProduct]
    exact (ContDiffAt.sum (fun j _ =>
      (contDiffAt_pi.mp (contDiffAt_pi.mp hMinv i) j).mul
      ((contDiffAt_pi.mp huc j).add ((contDiffAt_pi.mp hvc j).mul (contDiffAt_pi.mp hBc j))))).neg
  · have hh : AnalyticAt ℂ (fun t : ℂ => preferredSourceAngularField cell τ p m t z.2 i) z.1 := by
      simp only [preferredSourceAngularField,preferredAngularRepresentative,Matrix.mulVec,dotProduct]
      exact (Finset.analyticAt_fun_sum Finset.univ (fun j _ => analyticAt_const.mul
        ((analyticAt_pi_iff.mp hus j).add ((analyticAt_pi_iff.mp hvs j).mul
          (analyticAt_pi_iff.mp hBs j))))).neg
    exact hh.differentiableAt

/-- Every actual physical descendant has proved mixed smoothness on the
same open source set. There is no all-order regularity premise. -/
theorem preferredTransportedDensity_mixed_cellDomain {N : ℕ} (cell : PreferredTransportCell N) (hN : 0<N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r) (j : ℕ) :
    PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) => preferredTransportedDensity cell τ η p m r j z.1 z.2)
      (preferredCellRegularDomain cell τ p m) := by
  apply preferredTransportedDensity_mixed_of_base cell τ η p m r _
    (preferredCellRegularDomain_isOpen cell τ p m hp hm)
    (preferredSourceAngularField_mixed_cellDomain cell τ p m hp hm)
  intro z hz
  have hs : z.1≠0 := by intro he; have hh := hz.1; rw [he] at hh; simp [temperatureTrace] at hh
  have hw (i : Fin N) : OffRealSegment (temperatureTrace z.1-Complex.cos (deformedAngles τ p m z.2 i)) :=
    Or.inl (hz.2.1 i).ne'
  exact ⟨preferredPhysicalSeed_contDiffAt hN cell τ η p m r hη hp hm hr z.1 z.2 hs hw,
    (preferredPhysicalSeed_parameter_analyticAt hN cell τ η p m r z.1 z.2 hs hw).differentiableAt⟩



/-- The literal named-anchor residual is jointly analytic wherever the
actual inverse is analytic and its single named Uq denominator is nonzero. -/
theorem preferredResidualAnchor_analyticAt {N : ℕ} (a : Fin N) (s : ℂ) (q : Fin N → ℂ)
    (hU : ∀ i,AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,q i))
    (ha : preferredSourceUQ s (q a)≠0) :
    AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredResidualAnchor x.1 x.2 a) (s,q) := by
  have hcoord (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.2 i) (s,q) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt (s,q)
  have hdot (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredSourceUDot x.1 (x.2 i)) (s,q) :=
    AnalyticAt.comp (f := fun x : ℂ × (Fin N → ℂ) => (x.1,x.2 i))
      (g := fun x : ℂ × ℂ => preferredSourceUDot x.1 x.2)
      (preferredSourceUDot_analyticAt_of_joint s (q i) (hU i)) (analyticAt_fst.prod (hcoord i))
  have huq : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredSourceUQ x.1 (x.2 a)) (s,q) :=
    AnalyticAt.comp (f := fun x : ℂ × (Fin N → ℂ) => (x.1,x.2 a))
      (g := fun x : ℂ × ℂ => preferredSourceUQ x.1 x.2)
      (preferredSourceUQ_analyticAt_of_joint s (q a) (hU a)) (analyticAt_fst.prod (hcoord a))
  apply analyticAt_pi_iff.mpr
  intro i
  unfold preferredResidualAnchor anchorField
  split_ifs
  · exact ((Finset.univ.analyticAt_fun_sum (fun k _ => hdot k)).neg).div huq ha
  · exact analyticAt_const

/-- Every actual positive-epsilon one-sided configuration belongs to the
anchor's concrete open domain, even at total equality. -/
theorem preferredCellRegularDomain_anchor_of_oneSided {N : ℕ}
    (a : Fin N) (τ δ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i,θ i∈Icc (-Real.pi-δ) δ)
    (hW : ∀ i,0<(temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)).im)
    (hM : (preferredContourMatrix τ p m θ).det≠0) :
    (s,θ)∈preferredCellRegularDomain (.anchor a) τ p m := by
  have hwre (i : Fin N) : (deformedAngles τ p m θ i).re=θ i := by
    simp [deformedAngles,Complex.mul_re]
  have hU (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2)
      (s,preferredSourceCoordinate τ p m s θ i) :=
    preferred_global_one_sided_joint_analytic s (deformedAngles τ p m θ i) δ hδ hδπ hS hSi hSδ
      (by rw [hwre]; exact (hθ i).1) (by rw [hwre]; exact (hθ i).2) (hW i)
  have ha : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ a)≠0 :=
    (preferred_global_one_sided_q_regular s (deformedAngles τ p m θ a) δ hδ hδπ hS hSδ
      (by rw [hwre]; exact (hθ a).1) (by rw [hwre]; exact (hθ a).2) (hW a)).2
  exact ⟨hSi,hW,hM,preferredResidualAnchor_analyticAt a s _ hU ha,hU⟩

/-- Upper population exclusion kills every literal cell, including each
named anchor, on the same genuine open neighborhood. -/
theorem preferredTransportedDensity_cell_zero_of_upper_particle {N : ℕ}
    (cell : PreferredTransportCell N) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N)
    (hp : 1/2<B.p (θ i)) :
    preferredTransportedDensity cell τ preferredPopulationCutoff B.p B.m rcut j s θ=0 := by
  let U : Set (Fin N → ℝ) := {x | (1/2:ℝ)<B.p (x i)}
  have hU : IsOpen U := isOpen_lt continuous_const (B.smooth.continuous.comp (continuous_apply i))
  apply preferredTransportedDensity_zero_on_open cell τ preferredPopulationCutoff B.p B.m rcut U hU _ j s θ hp
  intro t x hx
  have hP : 1/2≤occupancy B.p x := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
      (fun v _ => B.lower_bound (x v)) (Finset.mem_univ i)
    exact hx.le.trans hh
  have he := preferredPopulationCutoff_one hP
  simp only [preferredPhysicalSeed,preferredCellWeight,preferredLowerWeight,lowerWeight,he,
    sub_self,zero_mul,zero_div,Complex.ofReal_zero]

end
end IsingBulk.Preferred22
