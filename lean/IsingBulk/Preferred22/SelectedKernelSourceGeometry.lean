import IsingBulk.Preferred22.SelectedKernelGeometry

/-! Uniform source margins on the full real angular contour. Both
occupancy fractions are quantified independently before particle number;
the same-plateau pair gap is proved from the actual smooth bump support. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1200000

theorem preferred_selected_opposite_endpoint_gap (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ H ρ : ℝ, 0<H ∧ 0<ρ ∧ ∀ ε τ σ υ θ : ℝ,
      |ε|<ρ → |τ|<ρ → σ∈Icc 0 1 → υ∈Icc 0 1 → θ∈Icc (-Real.pi) Real.pi →
      H≤‖preferredRadialTrace d ε-Complex.cos (preferredBumpAngle B.m B.p τ σ υ θ)+1‖ := by
  let H := (1+Real.cos d.b)/2
  have hbase : 0<1+Real.cos d.b := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi d.b_pos.le (le_refl Real.pi) d.b_lt
    rw [Real.cos_pi] at h
    linarith
  have hH : 0<H := by dsimp only [H]; positivity
  let K : Set (ℝ × ℝ × ℝ) := Icc (-Real.pi) Real.pi ×ˢ (Icc 0 1 ×ˢ Icc 0 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  let F : (ℝ × ℝ) → (ℝ × ℝ × ℝ) → ℝ := fun x y =>
    ‖preferredRadialTrace d x.1-Complex.cos (preferredBumpAngle B.m B.p x.2 y.2.1 y.2.2 y.1)+1‖
  have hcont (y : ℝ × ℝ × ℝ) :
      ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => F z.1 z.2) ((0,0),y) := by
    have hp : Continuous B.p := B.smooth.continuous
    have hm : Continuous B.m := hp.comp continuous_neg
    unfold F preferredBumpAngle preferredRadialTrace IsingBulk.Branch.radialParameter
    fun_prop (disch := simp)
  have hevent : ∀ᶠ x in 𝓝 ((0,0):ℝ × ℝ),∀ y∈K,H<F x y := by
    apply hK.eventually_forall_of_forall_eventually
    intro y _
    have hz : F (0,0) y=|2+Real.cos d.b-Real.cos y.1| := by
      simp only [F,preferredBumpAngle,mul_zero,zero_mul,Complex.ofReal_zero,sub_zero,
        preferredRadialTrace_zero,←Complex.ofReal_cos]
      have he : (1:ℂ)+(Real.cos d.b:ℂ)-(Real.cos y.1:ℂ)+1=
          ((2+Real.cos d.b-Real.cos y.1:ℝ):ℂ) := by push_cast; ring
      simp only [Complex.ofReal_add,Complex.ofReal_one]
      rw [he,Complex.norm_real,Real.norm_eq_abs]
    have hb : H<F (0,0) y := by
      rw [hz]
      have hm := le_abs_self (2+Real.cos d.b-Real.cos y.1)
      have hc := Real.cos_le_one y.1
      dsimp only [H]
      linarith
    exact continuousAt_const.eventually_lt (hcont y) hb
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨H,ρ,hH,hρ,?_⟩
  intro ε τ σ υ θ hε hτ hσ hυ hθ
  have hdist : dist (ε,τ) ((0,0):ℝ × ℝ)<ρ := by
    change dist (ε,τ) (0:ℝ × ℝ)<ρ
    simpa only [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using And.intro hε hτ
  exact (hball hdist (θ,σ,υ) ⟨hθ,hσ,hυ⟩).le

lemma preferred_plateau_principal_positive {d : PreferredBranchData}
    (B : PreferredCoareaBump d) {θ : ℝ} (hθ : θ∈Icc (-Real.pi) Real.pi)
    (hp : B.p θ=1) : θ∈Ioo 0 Real.pi := by
  have hs : 0<Real.sin θ := by
    by_contra! hs
    have hz := B.p_zero_of_sin_nonpos hs
    rw [hp] at hz
    norm_num at hz
  refine ⟨?_,?_⟩
  · by_contra! ht
    exact (not_lt_of_ge (Real.sin_nonpos_of_nonpos_of_neg_pi_le ht hθ.1)) hs
  · have ht : θ≠Real.pi := by intro he; rw [he,Real.sin_pi] at hs; exact lt_irrefl _ hs
    exact lt_of_le_of_ne hθ.2 ht

def preferredSamePlateauPairs (d : PreferredBranchData) (B : PreferredCoareaBump d) : Set (ℝ × ℝ) :=
  (Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi) ∩
    {x | (B.p x.1=1 ∧ B.p x.2=1) ∨ (B.m x.1=1 ∧ B.m x.2=1)}

lemma preferred_same_plateau_compact (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    IsCompact (preferredSamePlateauPairs d B) := by
  apply (isCompact_Icc.prod isCompact_Icc).inter_right
  have hp : Continuous B.p := B.smooth.continuous
  have hm : Continuous B.m := hp.comp continuous_neg
  exact ((isClosed_eq (hp.comp continuous_fst) continuous_const).inter
    (isClosed_eq (hp.comp continuous_snd) continuous_const)).union
    ((isClosed_eq (hm.comp continuous_fst) continuous_const).inter
      (isClosed_eq (hm.comp continuous_snd) continuous_const))

lemma preferred_same_plateau_reference_gap {d : PreferredBranchData}
    (B : PreferredCoareaBump d) {θ ψ : ℝ}
    (hθψ : (θ,ψ)∈preferredSamePlateauPairs d B) :
    0<‖1-Complex.exp (Complex.I*(θ:ℂ))*Complex.exp (Complex.I*(ψ:ℂ))‖ := by
  have hs : Real.sin ((θ+ψ)/2)≠0 := by
    rcases hθψ.2 with hp|hm
    · have hθ := preferred_plateau_principal_positive B hθψ.1.1 hp.1
      have hψ := preferred_plateau_principal_positive B hθψ.1.2 hp.2
      exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1,hψ.1])
        (by linarith [hθ.2,hψ.2])).ne'
    · have hθ := preferred_plateau_principal_positive B
        (show -θ∈Icc (-Real.pi) Real.pi by constructor <;> linarith [hθψ.1.1.1,hθψ.1.1.2]) hm.1
      have hψ := preferred_plateau_principal_positive B
        (show -ψ∈Icc (-Real.pi) Real.pi by constructor <;> linarith [hθψ.1.2.1,hθψ.1.2.2]) hm.2
      have hh := Real.sin_pos_of_pos_of_lt_pi
        (show 0< -((θ+ψ)/2) by linarith [hθ.1,hψ.1])
        (show -((θ+ψ)/2)<Real.pi by linarith [hθ.2,hψ.2])
      rw [Real.sin_neg] at hh
      linarith
  have he : Complex.exp (Complex.I*(θ:ℂ))*Complex.exp (Complex.I*(ψ:ℂ))=
      Complex.exp (Complex.I*((θ+ψ:ℝ):ℂ)) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he,norm_sub_rev,Complex.norm_exp_I_mul_ofReal_sub_one]
  exact norm_pos_iff.mpr (mul_ne_zero (by norm_num) hs)

/-- The angular denominator used for same-branch cancellation is uniformly
separated on both actual plateaux and for all normalized occupancies. -/
theorem preferred_selected_same_plateau_angular_gap (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ L ρ : ℝ,0<L ∧ 0<ρ ∧ ∀ τ σ υ θ ψ : ℝ,
      |τ|<ρ → σ∈Icc 0 1 → υ∈Icc 0 1 →
      (θ,ψ)∈preferredSamePlateauPairs d B →
      L≤‖1-Complex.exp (Complex.I*preferredBumpAngle B.m B.p τ σ υ θ)*
        Complex.exp (Complex.I*preferredBumpAngle B.m B.p τ σ υ ψ)‖ := by
  let K := preferredSamePlateauPairs d B
  have hK := preferred_same_plateau_compact d B
  have hbp : B.p d.b=1 := B.plateau d.b ⟨by linarith [B.delta_b,d.b_pos],B.branch_plateau.le⟩
  have hKb : (d.b,d.b)∈K :=
    ⟨⟨⟨by linarith [d.b_pos,Real.pi_pos],d.b_lt.le⟩,
       ⟨by linarith [d.b_pos,Real.pi_pos],d.b_lt.le⟩⟩,Or.inl ⟨hbp,hbp⟩⟩
  let f : ℝ × ℝ → ℝ := fun x => ‖1-Complex.exp (Complex.I*(x.1:ℂ))*
    Complex.exp (Complex.I*(x.2:ℂ))‖
  have hf : Continuous f := by unfold f; fun_prop
  obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn ⟨(d.b,d.b),hKb⟩ hf.continuousOn
  have hfx : 0<f x := preferred_same_plateau_reference_gap B hx
  let L := f x/2
  let K' : Set ((ℝ × ℝ) × (ℝ × ℝ)) := K ×ˢ (Icc 0 1 ×ˢ Icc 0 1)
  have hK' : IsCompact K' := hK.prod (isCompact_Icc.prod isCompact_Icc)
  let F : ℝ → ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ := fun τ y =>
    ‖1-Complex.exp (Complex.I*preferredBumpAngle B.m B.p τ y.2.1 y.2.2 y.1.1)*
      Complex.exp (Complex.I*preferredBumpAngle B.m B.p τ y.2.1 y.2.2 y.1.2)‖
  have hcont : Continuous (fun z : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) => F z.1 z.2) := by
    have hp : Continuous B.p := B.smooth.continuous
    have hm : Continuous B.m := hp.comp continuous_neg
    unfold F preferredBumpAngle
    fun_prop
  have hevent : ∀ᶠ τ in 𝓝 (0:ℝ),∀ y∈K',L<F τ y := by
    apply hK'.eventually_forall_of_forall_eventually
    intro y hy
    have hz : F 0 y=f y.1 := by simp [F,f,preferredBumpAngle]
    have hle : f x≤f y.1 := hmin hy.1
    have hb : L<F 0 y := by rw [hz]; dsimp only [L]; linarith only [hfx,hle]
    exact continuousAt_const.eventually_lt hcont.continuousAt hb
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨L,ρ,by dsimp only [L]; positivity,hρ,?_⟩
  intro τ σ υ θ ψ hτ hσ hυ hθψ
  exact (hball (by simpa only [Real.dist_eq,sub_zero] using hτ)
    ((θ,ψ),(σ,υ)) ⟨hθψ,hσ,hυ⟩).le

end
end IsingBulk.Preferred22
