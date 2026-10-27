import IsingBulk.Preferred22.SelectedOneBodyProfile
import IsingBulk.Preferred22.AngularYoung
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Uniform L1 and L^(4/3) bounds for the actual periodic selected-sector
square-root profile. Both true branch points are retained. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

/-- On the positive half-circle the only true zero is b, with a uniform
linear lower bound all the way to both endpoints. -/
theorem preferred_cos_branch_separation (d : PreferredBranchData) :
    ∃c>0,∀θ∈Icc (0:ℝ) Real.pi,c*|θ-d.b|≤|Real.cos d.b-Real.cos θ| := by
  obtain ⟨x,hx,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (d.b/2) ((Real.pi+d.b)/2)).Nonempty from
      ⟨d.b/2,by constructor <;> linarith [Real.pi_pos]⟩) Real.continuous_sin.continuousOn
  have hmx : 0<Real.sin x := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [d.b_pos,hx.1]) (by linarith [d.b_lt,hx.2])
  refine ⟨2*Real.sin x/Real.pi,by positivity,?_⟩
  intro θ hθ
  have hsum : (d.b+θ)/2∈Icc (d.b/2) ((Real.pi+d.b)/2) := by
    constructor <;> linarith [hθ.1,hθ.2]
  have hfirst : Real.sin x≤|Real.sin ((d.b+θ)/2)| := (hmin hsum).trans (le_abs_self _)
  have hdiff : |(d.b-θ)/2|≤Real.pi/2 := by
    rw [abs_le]
    constructor <;> linarith [d.b_pos,d.b_lt,hθ.1,hθ.2]
  have hsin := Real.mul_abs_le_abs_sin hdiff
  calc
    (2*Real.sin x/Real.pi)*|θ-d.b| =
        2*Real.sin x*(2/Real.pi*|(d.b-θ)/2|) := by
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_sub_comm d.b θ]
      ring
    _ ≤ 2*Real.sin x*|Real.sin ((d.b-θ)/2)| :=
      mul_le_mul_of_nonneg_left hsin (by positivity)
    _ ≤ 2*|Real.sin ((d.b+θ)/2)| *|Real.sin ((d.b-θ)/2)| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfirst (by norm_num)) (abs_nonneg _)
    _ = |Real.cos d.b-Real.cos θ| := by
      rw [Real.cos_sub_cos]
      simp only [abs_mul,abs_neg]
      norm_num

/-- The true one-dimensional branch singularity is locally integrable at
exponent -2/3. No regularized integral bound is postulated. -/
theorem preferred_abs_two_thirds_integrable (a l u : ℝ) :
    IntegrableOn (fun θ : ℝ => |θ-a|^(-2/3:ℝ)) (Ioc l u) := by
  have hloc : LocallyIntegrable (fun x : ℝ => ‖x‖^(-2/3:ℝ)) volume := by
    apply locallyIntegrable_of_norm_le_rpow (E:=ℝ) (F:=ℝ) (C:=1) (α:=2/3) (by norm_num) (by norm_num)
    · apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),one_mul]
      norm_num
    · exact (measurable_norm.pow_const (-2/3:ℝ)).aestronglyMeasurable
  have hc : IsCompact ((fun θ : ℝ => θ+(-a)) '' Icc l u) :=
    isCompact_Icc.image (by fun_prop)
  have hi := hloc.integrableOn_isCompact hc
  have ht := ((measurePreserving_add_right (volume : Measure ℝ) (-a)).integrableOn_image
    (measurableEmbedding_addRight (-a))).mp hi
  simpa only [Function.comp_def,Real.norm_eq_abs,←sub_eq_add_neg] using ht.mono_set Ioc_subset_Icc_self

theorem preferred_profile_four_thirds_eq (d : PreferredBranchData) {ε : ℝ} (hε : 0<ε) (θ : ℝ) :
    (preferredSelectedOneBodyProfile d ε θ)^(4/3:ℝ)=
      (|Real.cos d.b-Real.cos θ|+ε)^(-2/3:ℝ) := by
  have hb : 0≤|Real.cos d.b-Real.cos θ|+ε := by positivity
  rw [preferredSelectedOneBodyProfile,Real.sqrt_eq_rpow,←Real.rpow_neg hb,
    ←Real.rpow_mul hb]
  norm_num

/-- A fixed integrable two-branch majorant bounds every positive regularization. -/
theorem preferred_profile_four_thirds_majorant (d : PreferredBranchData) :
    ∃c>0,∀ε>0,∀ᵐ θ ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      (preferredSelectedOneBodyProfile d ε θ)^(4/3:ℝ)≤
        c*((|θ-d.b|)^(-2/3:ℝ)+(|θ+d.b|)^(-2/3:ℝ)) := by
  obtain ⟨c,hc,hsep⟩ := preferred_cos_branch_separation d
  refine ⟨c^(-2/3:ℝ),Real.rpow_pos_of_pos hc _,?_⟩
  intro ε hε
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
    ae_restrict_of_ae ((volume : Measure ℝ).ae_ne d.b),ae_restrict_of_ae ((volume : Measure ℝ).ae_ne (-d.b))] with θ hθ hb hmb
  rw [preferred_profile_four_thirds_eq d hε]
  by_cases hpos : 0≤θ
  · have hsep' := hsep θ ⟨hpos,hθ.2⟩
    have hab : 0 < |θ-d.b| := abs_pos.mpr (sub_ne_zero.mpr hb)
    have hbase : c*|θ-d.b|≤|Real.cos d.b-Real.cos θ|+ε := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hc hab) hbase (by norm_num : (-2/3:ℝ)≤0)
    rw [Real.mul_rpow hc.le hab.le] at hpow
    exact hpow.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)) (Real.rpow_nonneg hc.le _))
  · have hneg : θ<0 := lt_of_not_ge hpos
    have hsep' := hsep (-θ) ⟨by linarith,by linarith [hθ.1]⟩
    have he : |-θ-d.b|=|θ+d.b| := by rw [show -θ-d.b=-(θ+d.b) by ring,abs_neg]
    rw [Real.cos_neg,he] at hsep'
    have hab : 0 < |θ+d.b| := abs_pos.mpr (by intro h; apply hmb; linarith)
    have hbase : c*|θ+d.b|≤|Real.cos d.b-Real.cos θ|+ε := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hc hab) hbase (by norm_num : (-2/3:ℝ)≤0)
    rw [Real.mul_rpow hc.le hab.le] at hpow
    exact hpow.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)) (Real.rpow_nonneg hc.le _))

/-- Both source norms are bounded by one constant before ε is chosen. -/
theorem preferred_selected_profile_uniform_mass (d : PreferredBranchData) :
    ∃C>0,∀ε>0,
      (∫ θ in Ioc (-Real.pi) Real.pi,(preferredSelectedOneBodyProfile d ε θ)^(4/3:ℝ))≤C ∧
      (∫ θ in Ioc (-Real.pi) Real.pi,preferredSelectedOneBodyProfile d ε θ)≤C := by
  obtain ⟨c,hc,hmajor⟩ := preferred_profile_four_thirds_majorant d
  let M : ℝ → ℝ := fun θ => c*((|θ-d.b|)^(-2/3:ℝ)+(|θ+d.b|)^(-2/3:ℝ))
  have hM : IntegrableOn M (Ioc (-Real.pi) Real.pi) := by
    have hm : IntegrableOn (fun θ : ℝ => |θ+d.b|^(-2/3:ℝ)) (Ioc (-Real.pi) Real.pi) := by
      convert preferred_abs_two_thirds_integrable (-d.b) (-Real.pi) Real.pi using 1
      simp only [sub_neg_eq_add]
    exact ((preferred_abs_two_thirds_integrable d.b (-Real.pi) Real.pi).add hm).const_mul c
  let C := 1+2*Real.pi+∫ θ in Ioc (-Real.pi) Real.pi,M θ
  have hI : 0≤∫ θ in Ioc (-Real.pi) Real.pi,M θ :=
    integral_nonneg (fun θ => mul_nonneg hc.le (add_nonneg
      (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)))
  have hC : 0<C := by dsimp [C]; linarith [Real.pi_pos]
  refine ⟨C,hC,?_⟩
  intro ε hε
  have hf := preferred_selected_oneBody_profile_continuous d hε
  have hi : IntegrableOn (preferredSelectedOneBodyProfile d ε) (Ioc (-Real.pi) Real.pi) :=
    hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hfi : IntegrableOn (fun θ => (preferredSelectedOneBodyProfile d ε θ)^(4/3:ℝ))
      (Ioc (-Real.pi) Real.pi) :=
    ((hf.rpow_const (fun _ => Or.inr (by norm_num))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hfour := integral_mono_ae hfi hM (hmajor ε hε)
  have hpoint (θ : ℝ) : preferredSelectedOneBodyProfile d ε θ≤
      1+(preferredSelectedOneBodyProfile d ε θ)^(4/3:ℝ) := by
    let x := preferredSelectedOneBodyProfile d ε θ
    have hx : 0≤x := (preferred_selected_oneBody_profile_pos d hε θ).le
    by_cases hx1 : x≤1
    · exact hx1.trans (le_add_of_nonneg_right (Real.rpow_nonneg hx _))
    · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) (by norm_num : (1:ℝ)≤4/3)
      rw [Real.rpow_one] at hh
      exact hh.trans (le_add_of_nonneg_left zero_le_one)
  have hone : (∫ θ in Ioc (-Real.pi) Real.pi,preferredSelectedOneBodyProfile d ε θ)≤
      2*Real.pi+∫ θ in Ioc (-Real.pi) Real.pi,(preferredSelectedOneBodyProfile d ε θ)^(4/3:ℝ) := by
    have hh := integral_mono hi (integrable_const (1:ℝ) |>.add hfi) hpoint
    change (∫ θ in Ioc (-Real.pi) Real.pi,preferredSelectedOneBodyProfile d ε θ)≤
      ∫ θ in Ioc (-Real.pi) Real.pi,1+(preferredSelectedOneBodyProfile d ε θ)^(4/3:ℝ) at hh
    rw [integral_add (integrable_const (1:ℝ)) hfi] at hh
    have hconst : (∫ θ in Ioc (-Real.pi) Real.pi,(1:ℝ))=2*Real.pi := by
      simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
        sub_neg_eq_add,ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0≤Real.pi+Real.pi),
        smul_eq_mul,mul_one]
      ring
    rwa [hconst] at hh
  constructor <;> dsimp [C] <;> linarith [Real.pi_pos]


end
end IsingBulk.Preferred22
