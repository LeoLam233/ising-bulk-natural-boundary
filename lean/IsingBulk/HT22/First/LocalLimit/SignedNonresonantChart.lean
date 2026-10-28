import IsingBulk.HT22.Physical.ComplexAnalytic
import IsingBulk.Preferred22.Coordinates
import IsingBulk.HT22.First.LocalLimit.NonresonantChart

/-! Signed regular equality charts without an unsigned resonance premise.
The center angle is arbitrary, including zero. The analytic extension uses
the upper physical sheet, with a pointwise identity on every genuine upper
contour point. -/
namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Branch
open IsingBulk.Preferred22 IsingBulk.Tail
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

def signedPhaseRoot {N : ℕ} (p : ℂ × (Fin N → ℂ)) (i : Fin N) : ℂ :=
  phaseRoot (temperatureTrace p.1-Complex.cos (p.2 i))

def signedPhaseDensity (negative : Bool) {N : ℕ} (p : ℂ × (Fin N → ℂ)) : ℂ :=
  let z := signedPhaseRoot p
  let y := fun i => Physical.complexAngle (p.2 i)
  ((1+Physical.constraintSign negative*∏ i,z i)/
    (1-Physical.constraintSign negative*∏ i,z i)) *
      (∏ i,Physical.oneBody (z i)) * canceledPairProduct z y

theorem signedPhaseDensity_eq_physical (negative : Bool) {N : ℕ}
    (t : ℂ) (w : Fin N → ℂ)
    (hW : ∀ i,0<(temperatureTrace t-Complex.cos (w i)).im) :
    signedPhaseDensity negative (t,w)=Physical.complexSignedDensity negative (t,w) := by
  have hz (i : Fin N) : signedPhaseRoot (t,w) i=Physical.complexRoot t (w i) := by
    apply Regular.phaseRoot_eq_interior_root_of_upper
    · exact physicalRoot_quadratic _
    · exact physicalRoot_inside (Or.inl (hW i).ne')
    · exact hW i
  have he : signedPhaseRoot (t,w)=(fun i => Physical.complexRoot t (w i)) := funext hz
  simp only [signedPhaseDensity,Physical.complexSignedDensity,he]

theorem signedPhaseDensity_eq_angular (negative : Bool) {N : ℕ}
    (t : ℂ) (w : Fin N → ℝ) (ht : 0<(temperatureTrace t).im) :
    signedPhaseDensity negative (t,fun i => (w i:ℂ))=Physical.signedAngularDensity negative t w := by
  rw [signedPhaseDensity_eq_physical negative t _ (fun i => by
    simpa only [←Complex.ofReal_cos,sub_im,ofReal_im,sub_zero] using ht)]
  exact Physical.complexSignedDensity_real negative t w

theorem signedPhaseRoot_center {N : ℕ} (θ μ β : ℝ)
    (hβ : 0<β) (hβπ : β<Real.pi)
    (hrel : 2*Real.cos θ-Real.cos μ=Real.cos β) (i : Fin N) :
    signedPhaseRoot (exp ((θ:ℂ)*I),fun _ => (μ:ℂ)) i=exp (-(β:ℂ)*I) := by
  have he : temperatureTrace (exp ((θ:ℂ)*I))-Complex.cos (μ:ℂ)=(Real.cos β:ℂ) := by
    rw [temperatureTrace,IsingBulk.PrimeFamily.exp_angle_add_inv,←Complex.ofReal_cos]
    exact_mod_cast hrel
  rw [signedPhaseRoot,he,phaseRoot,lowerArccos_cos β hβ (by linarith)]
  congr 1
  ring

theorem signedPhaseRoot_analyticAt_center {N : ℕ} (θ μ β : ℝ)
    (hβ : 0<β) (hβπ : β<Real.pi)
    (hrel : 2*Real.cos θ-Real.cos μ=Real.cos β) (i : Fin N) :
    AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => signedPhaseRoot p i)
      (exp ((θ:ℂ)*I),fun _ => (μ:ℂ)) := by
  let c : ℂ × (Fin N → ℂ) := (exp ((θ:ℂ)*I),fun _ => (μ:ℂ))
  have dq : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => p.2 i) c :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dS : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => temperatureTrace p.1) c :=
    analyticAt_fst.add (analyticAt_fst.inv (exp_ne_zero _))
  have he : temperatureTrace c.1-Complex.cos (c.2 i)=(Real.cos β:ℂ) := by
    dsimp [c]
    rw [temperatureTrace,IsingBulk.PrimeFamily.exp_angle_add_inv,←Complex.ofReal_cos]
    exact_mod_cast hrel
  exact (analyticAt_const.mul ((Regular.lowerArccos_analytic_cos_of_lt_pi β hβ hβπ).comp_of_eq
    (dS.sub (Complex.analyticAt_cos.comp dq)) he)).cexp

theorem signedPhaseDensity_analyticAt_center (negative : Bool) (N : ℕ) (θ μ β : ℝ)
    (hβ : 0<β) (hβπ : β<Real.pi)
    (hrel : 2*Real.cos θ-Real.cos μ=Real.cos β)
    (hgap : 1-Physical.constraintSign negative*(exp (-(β:ℂ)*I))^N≠0) :
    AnalyticAt ℂ (@signedPhaseDensity negative N)
      (exp ((θ:ℂ)*I),fun _ => (μ:ℂ)) := by
  let c : ℂ × (Fin N → ℂ) := (exp ((θ:ℂ)*I),fun _ => (μ:ℂ))
  have dz (i : Fin N) := signedPhaseRoot_analyticAt_center θ μ β hβ hβπ hrel i
  have dy (i : Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => Physical.complexAngle (p.2 i)) c := by
    have dq : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => p.2 i) c :=
      (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
    exact (analyticAt_const.mul dq).cexp
  have hp (i j : Fin N) : 1-signedPhaseRoot c i*signedPhaseRoot c j≠0 := by
    dsimp only [c]
    rw [signedPhaseRoot_center θ μ β hβ hβπ hrel,signedPhaseRoot_center θ μ β hβ hβπ hrel,←pow_two]
    exact one_sub_negative_angle_sq_ne_zero (Real.sin_pos_of_pos_of_lt_pi hβ hβπ).ne'
  have hZ : 1-Physical.constraintSign negative*∏ i,signedPhaseRoot c i≠0 := by
    simpa only [c,signedPhaseRoot_center θ μ β hβ hβπ hrel,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin] using hgap
  have dZ := Finset.univ.analyticAt_fun_prod (fun i _ => dz i)
  have dbody : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => ∏ i,Physical.oneBody (signedPhaseRoot p i)) c := by
    simp_rw [Physical.oneBody_eq_rational]
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dz i)).div (analyticAt_const.sub ((dz i).pow 2))
      (by simpa only [pow_two] using hp i i)
  have dpair (i j : Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
      canceledPair (Physical.complexAngle (p.2 i)) (Physical.complexAngle (p.2 j))
        (signedPhaseRoot p i) (signedPhaseRoot p j)) c := by
    exact (((((dy i).sub (dy j)).pow 2).neg.mul (dz i)).mul (dz j)).div
      (((dy i).mul (dy j)).mul ((analyticAt_const.sub ((dz i).mul (dz j))).pow 2))
      (mul_ne_zero (mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)) (pow_ne_zero 2 (hp i j)))
  have dpairs : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
      canceledPairProduct (signedPhaseRoot p) (fun i => Physical.complexAngle (p.2 i))) c := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (Finset.univ.filter (fun j => i<j)).analyticAt_fun_prod
    intro j _
    exact dpair i j
  exact (((analyticAt_const.add (analyticAt_const.mul dZ)).div
    (analyticAt_const.sub (analyticAt_const.mul dZ)) hZ).mul dbody).mul dpairs


/-- Actual right-arc geometry supplies the regular phase even when the
common angular mean is zero. -/
theorem right_mean_regular_phase (d : PreferredBranchData)
    {ρ δR μ : ℝ} (hρ : 0<ρ) (hδR : δR<d.b)
    (hμ : μ∈Icc (-d.b+ρ) δR) :
    ∃ β : ℝ, 0<β ∧ β<Real.pi ∧ 2*Real.cos d.alpha-Real.cos μ=Real.cos β := by
  obtain ⟨hlo,hhi⟩ := preferred_right_reference_margin d hρ hδR hμ
  refine ⟨Real.arccos (1+Real.cos d.b-Real.cos μ),Real.arccos_pos.mpr hhi,
    Real.arccos_lt_pi.mpr hlo,?_⟩
  rw [Real.cos_arccos hlo.le hhi.le,d.angle_relation]
  ring

/-- A fixed complex angular parametrization includes both real shape charts
and balanced deformed contours. No resonance or positive-center hypothesis
is imposed. -/
theorem signed_local_integral_analyticAt {n N : ℕ} (negative : Bool) (θ μ β : ℝ)
    (hβ : 0<β) (hβπ : β<Real.pi)
    (hrel : 2*Real.cos θ-Real.cos μ=Real.cos β)
    (hgap : 1-Physical.constraintSign negative*(exp (-(β:ℂ)*I))^N≠0)
    (ψ : (Fin n → ℝ) → (Fin N → ℂ)) (hψ : Continuous ψ)
    (hψ0 : ψ 0=fun _ => (μ:ℂ)) :
    ∃ R : ℝ, 0<R ∧ ∀ χ : (Fin n → ℝ) → ℂ, Continuous χ →
      (∀ x,χ x≠0 → ‖x‖<R) →
      AnalyticAt ℂ (fun s => ∫ x,χ x*signedPhaseDensity negative (s,ψ x))
        (exp ((θ:ℂ)*I)) := by
  let s₀ := exp ((θ:ℂ)*I)
  let g := fun p : ℂ × (Fin n → ℝ) => (p.1,ψ p.2)
  have hg : Continuous g := continuous_fst.prodMk (hψ.comp continuous_snd)
  have hzero : g (s₀,0)=(s₀,fun _ => (μ:ℂ)) := by simp only [g,hψ0]
  have ht := hg.tendsto (s₀,0)
  rw [hzero] at ht
  have hev := ht.eventually (signedPhaseDensity_analyticAt_center negative N θ μ β hβ hβπ hrel hgap).eventually_analyticAt
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hev
  let R := r/2
  have hR : 0<R := half_pos hr
  have hRr : R<r := half_lt_self hr
  refine ⟨R,hR,?_⟩
  intro χ hχ hχs
  let K := Metric.closedBall (0:Fin n → ℝ) R
  have hF (s : ℂ) (hs : s∈ball s₀ R) (x : Fin n → ℝ) (hx : x∈K) :
      AnalyticAt ℂ (signedPhaseDensity negative) (s,ψ x) := by
    apply hball (a:=(s,x))
    rw [mem_ball,dist_eq_norm]
    change max ‖s-s₀‖ ‖x-0‖<r
    rw [sub_zero,max_lt_iff]
    refine ⟨?_,?_⟩
    · exact (by simpa only [mem_ball,dist_eq_norm] using hs : ‖s-s₀‖<R).trans hRr
    · exact (by simpa only [K,mem_closedBall,dist_zero_right] using hx : ‖x‖≤R).trans_lt hRr
  have h := compact_analytic_shape_integral_analyticAt (μ := (volume : Measure (Fin n → ℝ)))
    (isCompact_closedBall (0:Fin n → ℝ) R) isOpen_ball (signedPhaseDensity negative)
    ψ hψ χ hχ hF (mem_ball_self hR)
  have hzeroχ (x : Fin n → ℝ) (hx : x∉K) : χ x=0 := by
    by_contra hh
    apply hx
    exact mem_closedBall_zero_iff.mpr (hχs x hh).le
  have heq : (fun s => ∫ x : Fin n → ℝ in K,χ x*signedPhaseDensity negative (s,ψ x))=
      (fun s => ∫ x : Fin n → ℝ,χ x*signedPhaseDensity negative (s,ψ x)) := by
    funext s
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzeroχ x hx,zero_mul])
  rw [heq] at h
  exact h

theorem signed_weighted_integral_eq_phase {n N : ℕ} (negative : Bool)
    (χ : (Fin n → ℝ) → ℂ) (ψ : (Fin n → ℝ) → (Fin N → ℂ)) (s : ℂ)
    (hW : ∀ x,χ x≠0 → ∀ i,0<(temperatureTrace s-Complex.cos (ψ x i)).im) :
    (∫ x,χ x*Physical.complexSignedDensity negative (s,ψ x))=
      ∫ x,χ x*signedPhaseDensity negative (s,ψ x) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : χ x=0
    · simp only [hx,zero_mul]
    · rw [signedPhaseDensity_eq_physical negative s (ψ x) (hW x hx)]

theorem signed_weighted_integral_deriv_eq_phase {n N : ℕ} (negative : Bool)
    (χ : (Fin n → ℝ) → ℂ) (ψ : (Fin n → ℝ) → (Fin N → ℂ)) (s : ℂ)
    (hW : ∀ᶠ t in 𝓝 s, ∀ x,χ x≠0 → ∀ i,0<(temperatureTrace t-Complex.cos (ψ x i)).im)
    (j : ℕ) :
    (deriv^[j] (fun t => ∫ x,χ x*Physical.complexSignedDensity negative (t,ψ x))) s =
      (deriv^[j] (fun t => ∫ x,χ x*signedPhaseDensity negative (t,ψ x))) s := by
  have he : (fun t => ∫ x,χ x*Physical.complexSignedDensity negative (t,ψ x)) =ᶠ[𝓝 s]
      (fun t => ∫ x,χ x*signedPhaseDensity negative (t,ψ x)) := by
    filter_upwards [hW] with t ht
    exact signed_weighted_integral_eq_phase negative χ ψ t ht
  simpa only [iteratedDeriv_eq_iterate] using he.iteratedDeriv_eq j


/-- Bounded derivatives of the literal signed physical angular integral.
Only actual geometric regularity and the signed product gap are hypotheses. -/
theorem signed_local_angular_derivatives_bounded {n N : ℕ} (negative : Bool) (θ μ β : ℝ)
    (hθ : 0<Real.sin θ) (hβ : 0<β) (hβπ : β<Real.pi)
    (hrel : 2*Real.cos θ-Real.cos μ=Real.cos β)
    (hgap : 1-Physical.constraintSign negative*(exp (-(β:ℂ)*I))^N≠0)
    (ψ : (Fin n → ℝ) → (Fin N → ℝ)) (hψ : Continuous ψ)
    (hψ0 : ψ 0=fun _ => μ) :
    ∃ R : ℝ, 0<R ∧ ∀ χ : (Fin n → ℝ) → ℂ, Continuous χ →
      (∀ x,χ x≠0 → ‖x‖<R) → ∀ j : ℕ,
      ∃ C ε₀ : ℝ, 0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖(deriv^[j] (fun t => ∫ x,χ x*Physical.signedAngularDensity negative t (ψ x)))
          (radialParameter θ ε)‖≤C := by
  let ψc := fun x i => ((ψ x i:ℝ):ℂ)
  have hψc : Continuous ψc := continuous_pi fun i =>
    Complex.continuous_ofReal.comp ((continuous_apply i).comp hψ)
  have hψc0 : ψc 0=fun _ => (μ:ℂ) := by simp only [ψc,hψ0]
  obtain ⟨R,hR,hI⟩ := signed_local_integral_analyticAt negative θ μ β hβ hβπ hrel hgap ψc hψc hψc0
  refine ⟨R,hR,?_⟩
  intro χ hχ hχs j
  let F := fun t => ∫ x,χ x*signedPhaseDensity negative (t,ψc x)
  have hf : AnalyticAt ℂ F (exp ((θ:ℂ)*I)) := hI χ hχ hχs
  have hd : ∀ k : ℕ, AnalyticAt ℂ (deriv^[k] F) (exp ((θ:ℂ)*I)) := by
    intro k
    induction k with
    | zero => exact hf
    | succ k ih => rw [Function.iterate_succ_apply'];exact ih.deriv
  have hrad : Tendsto (radialParameter θ) (𝓝[>] 0) (𝓝 (exp ((θ:ℂ)*I))) := by
    have hcont : Continuous (radialParameter θ) := by unfold radialParameter;fun_prop
    simpa [radialParameter] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hr := (hd j).continuousAt.tendsto.comp hrad
  let C := ‖(deriv^[j] F) (exp ((θ:ℂ)*I))‖+1
  have hC : 0<C := by dsimp [C];positivity
  have hev := hr.norm.eventually (Iio_mem_nhds (show
    ‖(deriv^[j] F) (exp ((θ:ℂ)*I))‖<C by dsimp [C];linarith))
  obtain ⟨ε₀,hε₀,hbnd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro ε he he0
  let s := radialParameter θ ε
  have hi : 0<(temperatureTrace s).im := radial_source_upper hθ he
  have hs0 : s≠0 := by
    apply norm_ne_zero_iff.mp
    have hh := radialParameter_norm (θ:=θ) he.le
    dsimp [s]
    rw [hh]
    positivity
  have hSc : ContinuousAt temperatureTrace s := continuousAt_id.add (continuousAt_id.inv₀ hs0)
  have hupper : ∀ᶠ z : ℂ in 𝓝 s,0<(temperatureTrace z).im :=
    (continuous_im.continuousAt.comp hSc).eventually (Ioi_mem_nhds hi)
  have heq : (fun t => ∫ x,χ x*Physical.signedAngularDensity negative t (ψ x)) =ᶠ[𝓝 s] F := by
    filter_upwards [hupper] with t ht
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [F,ψc]
      rw [signedPhaseDensity_eq_angular negative t (ψ x) ht]
  have hdEq := heq.iteratedDeriv_eq j
  simp only [iteratedDeriv_eq_iterate] at hdEq
  rw [hdEq]
  exact (hbnd ⟨he,he0⟩).le

end
end IsingBulk.HT22.LocalLimit
