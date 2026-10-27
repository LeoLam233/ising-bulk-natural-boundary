import IsingBulk.Preferred22.AnchorPhase
import IsingBulk.Preferred22.CollectiveAnalytic

/-! Uniform compact-left regularity from the actual physical reference
curve. The source phase is continued by its physical disk root, and only
then identified with the upper-W outward contour. All compactness choices
precede the particle number and the derivative order. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def preferredLeftReferenceCoordinate (d : PreferredBranchData) (θ : ℝ) : ℂ :=
  preferredPhysicalPhase (temperatureTrace (preferredSelectedPoint d)-Complex.cos (θ:ℂ))+
    (θ:ℂ)-preferredMovingBranch (preferredSelectedPoint d)

theorem preferred_left_reference_trace_gap (d : PreferredBranchData) {δ η θ : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hgap : d.b+η<Real.pi-δ)
    (hθ : θ∈Icc (-Real.pi-δ) (-d.b-η)) :
    1<(temperatureTrace (preferredSelectedPoint d)-Complex.cos (θ:ℂ)).re := by
  have hc : Real.cos θ≤Real.cos (d.b+η) := by
    by_cases hlo : -Real.pi≤θ
    · have h := Real.cos_le_cos_of_nonneg_of_le_pi
        (by linarith [d.b_pos] : 0≤d.b+η) (by linarith : -θ≤Real.pi)
        (by linarith [hθ.2] : d.b+η≤ -θ)
      simpa only [Real.cos_neg] using h
    · have h := Real.cos_le_cos_of_nonneg_of_le_pi
        (by linarith [d.b_pos] : 0≤d.b+η) (by linarith : θ+2*Real.pi≤Real.pi)
        (by linarith [hθ.1] : d.b+η≤θ+2*Real.pi)
      simpa only [Real.cos_add_two_pi] using h
  have hstrict : Real.cos (d.b+η)<Real.cos d.b :=
    Real.cos_lt_cos_of_nonneg_of_le_pi d.b_pos.le (by linarith) (by linarith)
  rw [temperatureTrace_preferredSelectedPoint]
  simp only [Complex.sub_re,←Complex.ofReal_cos,Complex.ofReal_re]
  linarith

theorem preferredLeftReferenceCoordinate_continuousOn (d : PreferredBranchData)
    {δ η : ℝ} (hδ : 0<δ) (hη : 0<η) (hgap : d.b+η<Real.pi-δ) :
    ContinuousOn (preferredLeftReferenceCoordinate d) (Icc (-Real.pi-δ) (-d.b-η)) := by
  intro θ hθ
  have hW := preferred_left_reference_trace_gap d hδ hη hgap hθ
  have hc : ContinuousAt (fun x : ℝ => temperatureTrace (preferredSelectedPoint d)-Complex.cos (x:ℂ)) θ := by
    fun_prop
  have hφ : ContinuousAt (fun x : ℝ => preferredPhysicalPhase
      (temperatureTrace (preferredSelectedPoint d)-Complex.cos (x:ℂ))) θ :=
    ContinuousAt.comp (f := fun x : ℝ => temperatureTrace (preferredSelectedPoint d)-Complex.cos (x:ℂ))
      (g := preferredPhysicalPhase) (preferredPhysicalPhase_analyticAt_right hW).continuousAt hc
  have hh : ContinuousAt (preferredLeftReferenceCoordinate d) θ := by
    convert! (hφ.add Complex.continuous_ofReal.continuousAt).sub continuousAt_const using 1
  exact hh.continuousWithinAt

/-- The fixed left point conditions contain only explicit analytic
functions and their true nonzero denominators. -/
def PreferredLeftRegularPoint (s q : ℂ) : Prop :=
  AnalyticAt ℂ preferredMovingBranch s ∧
  AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) ∧
  preferredSourceUQ s q≠0 ∧
  Complex.cos ((q+preferredMovingBranch s)/2)≠0 ∧
  Complex.sin (preferredRegularPhase s q)-Complex.sin (preferredMovingInverse s q)≠0 ∧
  (preferredRegularPhase s q).im<0

theorem preferredLeftRegularPoint_isOpen :
    IsOpen {z : ℂ × ℂ | PreferredLeftRegularPoint z.1 z.2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  rcases hz with ⟨hB,hU,hq,hc,hg,hφ⟩
  have hBa : AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingBranch x.1) z :=
    AnalyticAt.comp (f := fun x : ℂ × ℂ => x.1) (g := preferredMovingBranch) hB analyticAt_fst
  have hφa := preferredRegularPhase_analyticAt z.1 z.2 hU hB
  have hqa := preferredSourceUQ_analyticAt_of_joint z.1 z.2 hU
  have hca : ContinuousAt (fun x : ℂ × ℂ => Complex.cos ((x.2+preferredMovingBranch x.1)/2)) z :=
    (Complex.analyticAt_cos.comp ((analyticAt_snd.add hBa).div_const (c := (2:ℂ)))).continuousAt
  have hga : ContinuousAt (fun x : ℂ × ℂ => Complex.sin (preferredRegularPhase x.1 x.2)-
      Complex.sin (preferredMovingInverse x.1 x.2)) z :=
    ((Complex.analyticAt_sin.comp hφa).sub (Complex.analyticAt_sin.comp hU)).continuousAt
  have hBev : ∀ᶠ x : ℂ × ℂ in 𝓝 z,AnalyticAt ℂ preferredMovingBranch x.1 :=
    continuousAt_fst.tendsto.eventually hB.eventually_analyticAt
  filter_upwards [hBev,hU.eventually_analyticAt,hqa.continuousAt.eventually_ne hq,
    hca.eventually_ne hc,hga.eventually_ne hg,
    (Complex.continuous_im.continuousAt.comp hφa.continuousAt).eventually_lt continuousAt_const hφ]
    with x hxB hxU hxq hxc hxg hxφ
  exact ⟨hxB,hxU,hxq,hxc,hxg,hxφ⟩

theorem preferred_left_reference_regular (d : PreferredBranchData) {δ η θ : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hgap : d.b+η<Real.pi-δ)
    (hθ : θ∈Icc (-Real.pi-δ) (-d.b-η)) :
    PreferredLeftRegularPoint (preferredSelectedPoint d) (preferredLeftReferenceCoordinate d θ) := by
  let s := preferredSelectedPoint d
  let W := temperatureTrace s-Complex.cos (θ:ℂ)
  let φ := preferredPhysicalPhase W
  let q := preferredLeftReferenceCoordinate d θ
  have hS : 0<(temperatureTrace s).re := by
    rw [temperatureTrace_preferredSelectedPoint]
    exact (preferred_reference_trace_range d).1
  have hSi : (temperatureTrace s).im=0 := by simp [s,temperatureTrace_preferredSelectedPoint]
  have hW : 1<W.re := preferred_left_reference_trace_gap d hδ hη hgap hθ
  have hθlo : -2*Real.pi<θ := by linarith [hθ.1,d.b_pos]
  have hθhi : θ<0 := by linarith [hθ.2,d.b_pos]
  have hB := preferredMovingBranch_analyticAt_reference d
  obtain ⟨hInv,hU,hUq⟩ := preferred_compact_left_inverse_reference s θ hS hSi hW hθlo hθhi hB
  change preferredMovingInverse s q=(θ:ℂ) at hInv
  change AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) at hU
  change preferredSourceUQ s q≠0 at hUq
  have hφ : preferredRegularPhase s q=φ := by
    unfold preferredRegularPhase
    rw [hInv]
    dsimp [q,preferredLeftReferenceCoordinate,φ,W,s]
    ring
  have hdisp : Complex.cos (θ:ℂ)+Complex.cos φ=temperatureTrace s := by
    rw [show Complex.cos φ=W from preferredPhysicalPhase_cos W]
    dsimp [W]
    ring
  have hc : Complex.cos ((q+preferredMovingBranch s)/2)≠0 := by
    have he : q+preferredMovingBranch s=(θ:ℂ)+φ := by
      dsimp [q,preferredLeftReferenceCoordinate,φ,W,s]
      ring
    rw [he]
    intro hz
    have hh := Complex.cos_add_cos (θ:ℂ) φ
    rw [hz,mul_zero,zero_mul,hdisp] at hh
    rw [hh,Complex.zero_re] at hS
    exact (lt_irrefl 0) hS
  have hU₁ : DifferentiableAt ℂ (preferredMovingInverse s) q :=
    (AnalyticAt.comp (f := fun z : ℂ => (s,z))
      (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hU
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hg : Complex.sin (preferredRegularPhase s q)-Complex.sin (preferredMovingInverse s q)≠0 := by
    intro hz
    have hh := preferredRegular_inverse_derivative_identity s q hc hU₁
    rw [hz,mul_zero,hφ] at hh
    exact (preferredPhysicalPhase_sin_ne_zero hW) hh.symm
  refine ⟨hB,hU,hUq,hc,hg,?_⟩
  rw [hφ]
  exact preferredPhysicalPhase_im_neg (Or.inr (hW.trans_le (le_abs_self _)))

/-- A compact source curve has one fixed scalar product tube. This lemma
retains the actual set and does not replace it by a convex hull. -/
theorem preferred_compact_scalar_tube (s₀ : ℂ) (K : Set ℂ) (hK : IsCompact K)
    (G : Set (ℂ × ℂ)) (hG : IsOpen G) (hbase : ∀ q∈K,(s₀,q)∈G) :
    ∃ D : Set ℂ,∃ ρ : ℝ,0<ρ ∧ IsCompact D ∧ K⊆interior D ∧
      ∀ s q : ℂ,‖s-s₀‖<ρ → q∈D → (s,q)∈G := by
  let L : Set (ℂ × ℂ) := {s₀} ×ˢ K
  have hL : IsCompact L := isCompact_singleton.prod hK
  have hLG : L⊆G := by
    intro z hz
    have hs : z.1=s₀ := hz.1
    rw [←Prod.eta z,hs]
    exact hbase _ hz.2
  obtain ⟨δ,hδ,htube⟩ := hL.exists_thickening_subset_open hG hLG
  let ρ := δ/4
  let D := Metric.cthickening ρ K
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  refine ⟨D,ρ,hρ,hK.cthickening,?_,?_⟩
  · exact (Metric.self_subset_thickening hρ K).trans (Metric.thickening_subset_interior_cthickening ρ K)
  · intro s q hs hq
    have hq' : q∈Metric.thickening (δ/2) K :=
      Metric.cthickening_subset_thickening' (half_pos hδ) (by dsimp [ρ]; linarith) K hq
    obtain ⟨q₀,hq₀,hdq⟩ := Metric.mem_thickening_iff.mp hq'
    apply htube
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(s₀,q₀),⟨rfl,hq₀⟩,?_⟩
    have hds : dist s s₀<δ := by rw [dist_eq_norm]; exact hs.trans (by dsimp [ρ]; linarith)
    simpa only [Prod.dist_eq,max_lt_iff] using And.intro hds (hdq.trans (by linarith))

/-- Uniform actual left inverse and one-body domain, including a positive
compact gap from Uq=0 and from the product-phase unit circle. -/
theorem preferred_compact_left_domain (d : PreferredBranchData) {δ η : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hgap : d.b+η<Real.pi-δ) :
    ∃ D : Set ℂ,∃ ρ : ℝ,0<ρ ∧ IsCompact D ∧
      (∀ θ∈Icc (-Real.pi-δ) (-d.b-η),preferredLeftReferenceCoordinate d θ∈interior D) ∧
      ∀ s q : ℂ,‖s-preferredSelectedPoint d‖<ρ → q∈D → PreferredLeftRegularPoint s q := by
  let K := preferredLeftReferenceCoordinate d '' Icc (-Real.pi-δ) (-d.b-η)
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (preferredLeftReferenceCoordinate_continuousOn d hδ hη hgap)
  obtain ⟨D,ρ,hρ,hD,hKD,hgood⟩ := preferred_compact_scalar_tube (preferredSelectedPoint d) K hK
    {z : ℂ × ℂ | PreferredLeftRegularPoint z.1 z.2} preferredLeftRegularPoint_isOpen (by
      rintro q ⟨θ,hθ,rfl⟩
      exact preferred_left_reference_regular d hδ hη hgap hθ)
  exact ⟨D,ρ,hρ,hD,fun θ hθ => hKD ⟨θ,hθ,rfl⟩,hgood⟩

def preferredPhysicalBumpCoordinate (d : PreferredBranchData) (p m : ℝ → ℝ)
    (ε τ σ υ θ : ℝ) : ℂ :=
  preferredPhysicalPhase (preferredRadialTrace d ε-Complex.cos (preferredBumpAngle m p τ σ υ θ))+
    preferredBumpAngle m p τ σ υ θ-preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha ε)

theorem preferredPhysicalBumpCoordinate_zero (d : PreferredBranchData) (p m : ℝ → ℝ)
    (σ υ θ : ℝ) :
    preferredPhysicalBumpCoordinate d p m 0 0 σ υ θ=preferredLeftReferenceCoordinate d θ := by
  unfold preferredPhysicalBumpCoordinate preferredLeftReferenceCoordinate
  simp only [preferredBumpAngle,Complex.ofReal_zero,mul_zero,zero_mul,sub_zero]
  rfl

theorem preferredPhysicalBumpCoordinate_eq (d : PreferredBranchData) (p m : ℝ → ℝ)
    (ε τ σ υ θ : ℝ)
    (hW : 0<(preferredRadialTrace d ε-Complex.cos (preferredBumpAngle m p τ σ υ θ)).im) :
    preferredPhysicalBumpCoordinate d p m ε τ σ υ θ=preferredBumpCoordinate d p m ε τ σ υ θ := by
  unfold preferredPhysicalBumpCoordinate preferredBumpCoordinate
  rw [preferredPhysicalPhase_eq_arccos_upper hW]

theorem preferred_physical_left_coordinate_image (d : PreferredBranchData) (p m : ℝ → ℝ)
    (hp : Continuous p) (hm : Continuous m) {δ η : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hgap : d.b+η<Real.pi-δ)
    (D : Set ℂ)
    (hD : ∀ θ∈Icc (-Real.pi-δ) (-d.b-η),preferredLeftReferenceCoordinate d θ∈interior D) :
    ∃ r : ℝ,0<r ∧ ∀ ε τ σ υ θ : ℝ,
      |ε|<r → |τ|<r → σ∈Icc 0 1 → υ∈Icc 0 1 → θ∈Icc (-Real.pi-δ) (-d.b-η) →
      preferredPhysicalBumpCoordinate d p m ε τ σ υ θ∈interior D := by
  let K : Set (ℝ × ℝ × ℝ) := Icc (-Real.pi-δ) (-d.b-η) ×ˢ (Icc 0 1 ×ˢ Icc 0 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  let F : (ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℂ := fun x y =>
    preferredPhysicalBumpCoordinate d p m x.1 x.2 y.2.1 y.2.2 y.1
  have hbase (y : ℝ × ℝ × ℝ) (hy : y∈K) : F (0,0) y∈interior D := by
    simpa only [F,preferredPhysicalBumpCoordinate_zero] using hD y.1 hy.1
  have hcont (y : ℝ × ℝ × ℝ) (hy : y∈K) :
      ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => F z.1 z.2) ((0,0),y) := by
    have hw : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
        preferredBumpAngle m p z.1.2 z.2.2.1 z.2.2.2 z.2.1) := by
      unfold preferredBumpAngle
      fun_prop
    have ht : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => preferredRadialTrace d z.1.1) ((0,0),y) :=
      by
        unfold preferredRadialTrace IsingBulk.Branch.radialParameter
        fun_prop (disch := simp [Complex.exp_ne_zero])
    have hWc := ht.sub (Complex.continuous_cos.comp hw).continuousAt
    have hW := preferred_left_reference_trace_gap d hδ hη hgap hy.1
    have hpφ := (preferredPhysicalPhase_analyticAt_right hW).continuousAt
    have harg : preferredRadialTrace d 0-Complex.cos (preferredBumpAngle m p 0 y.2.1 y.2.2 y.1)=
        temperatureTrace (preferredSelectedPoint d)-Complex.cos (y.1:ℂ) := by
      simp [preferredRadialTrace,preferredBumpAngle,preferredSelectedPoint,temperatureTrace]
    have hφ : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
        preferredPhysicalPhase (preferredRadialTrace d z.1.1-
          Complex.cos (preferredBumpAngle m p z.1.2 z.2.2.1 z.2.2.2 z.2.1))) ((0,0),y) :=
      ContinuousAt.comp_of_eq
        (f := fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => preferredRadialTrace d z.1.1-
          Complex.cos (preferredBumpAngle m p z.1.2 z.2.2.1 z.2.2.2 z.2.1))
        (g := preferredPhysicalPhase) hpφ hWc harg
    have hp : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
        IsingBulk.Branch.radialParameter d.alpha z.1.1) ((0,0),y) := by
      unfold IsingBulk.Branch.radialParameter
      fun_prop
    have hb : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
        preferredMovingBranch (IsingBulk.Branch.radialParameter d.alpha z.1.1)) ((0,0),y) :=
      ContinuousAt.comp_of_eq
        (f := fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => IsingBulk.Branch.radialParameter d.alpha z.1.1)
        (g := preferredMovingBranch) (preferredMovingBranch_analyticAt_reference d).continuousAt hp (by rfl)
    exact (hφ.add hw.continuousAt).sub hb
  have hevent : ∀ᶠ x in 𝓝 ((0,0):ℝ × ℝ),∀ y∈K,F x y∈interior D := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    exact (hcont y hy).preimage_mem_nhds (isOpen_interior.mem_nhds (hbase y hy))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r,hr,?_⟩
  intro ε τ σ υ θ hε hτ hσ hυ hθ
  have hd : dist (ε,τ) ((0,0):ℝ × ℝ)<r := by
    simpa only [Prod.dist_eq,Real.dist_eq,sub_zero,max_lt_iff] using And.intro hε hτ
  have hh := hball hd (θ,σ,υ) ⟨hθ,hσ,hυ⟩
  change F (ε,τ) (θ,σ,υ)∈interior D
  exact hh

/-- The actual compact-left scalar image has a uniform complex interior
margin, chosen before both occupancies and both physical small parameters. -/
theorem preferred_physical_left_coordinate_image_margin (d : PreferredBranchData) (p m : ℝ → ℝ)
    (hp : Continuous p) (hm : Continuous m) {δ η : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hgap : d.b+η<Real.pi-δ)
    (D : Set ℂ)
    (hD : ∀ θ∈Icc (-Real.pi-δ) (-d.b-η),preferredLeftReferenceCoordinate d θ∈interior D) :
    ∃ κ r : ℝ,0<κ ∧ 0<r ∧ ∀ ε τ σ υ θ : ℝ,
      |ε|<r → |τ|<r → σ∈Icc 0 1 → υ∈Icc 0 1 → θ∈Icc (-Real.pi-δ) (-d.b-η) →
      Metric.closedBall (preferredPhysicalBumpCoordinate d p m ε τ σ υ θ) κ⊆D := by
  let K := preferredLeftReferenceCoordinate d '' Icc (-Real.pi-δ) (-d.b-η)
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (preferredLeftReferenceCoordinate_continuousOn d hδ hη hgap)
  have hKD : K⊆interior D := by rintro q ⟨θ,hθ,rfl⟩; exact hD θ hθ
  obtain ⟨γ,hγ,hthick⟩ := hK.exists_thickening_subset_open isOpen_interior hKD
  let κ := γ/4
  have hκ : 0<κ := by dsimp [κ]; positivity
  let E := Metric.cthickening κ K
  have hE : ∀ θ∈Icc (-Real.pi-δ) (-d.b-η),preferredLeftReferenceCoordinate d θ∈interior E := by
    intro θ hθ
    exact (Metric.thickening_subset_interior_cthickening κ K)
      (Metric.self_subset_thickening hκ K ⟨θ,hθ,rfl⟩)
  obtain ⟨r,hr,himage⟩ := preferred_physical_left_coordinate_image d p m hp hm hδ hη hgap E hE
  refine ⟨κ,r,hκ,hr,?_⟩
  intro ε τ σ υ θ hε hτ hσ hυ hθ z hz
  have hq : preferredPhysicalBumpCoordinate d p m ε τ σ υ θ∈E :=
    interior_subset (himage ε τ σ υ θ hε hτ hσ hυ hθ)
  have hq' : preferredPhysicalBumpCoordinate d p m ε τ σ υ θ∈Metric.thickening (γ/2) K :=
    Metric.cthickening_subset_thickening' (half_pos hγ) (by dsimp [κ]; linarith) K hq
  obtain ⟨a,ha,hqa⟩ := Metric.mem_thickening_iff.mp hq'
  have hza : dist z a<γ := by
    have hzq : dist z (preferredPhysicalBumpCoordinate d p m ε τ σ υ θ)≤κ := hz
    have hh := dist_triangle z (preferredPhysicalBumpCoordinate d p m ε τ σ υ θ) a
    dsimp [κ] at hzq
    linarith
  exact interior_subset (hthick (Metric.mem_thickening_iff.mpr ⟨a,ha,hza⟩))

end
end IsingBulk.Preferred22
