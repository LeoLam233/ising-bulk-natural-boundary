import IsingBulk.Anisotropic.NegativeNormalForm.PoleNewton
import IsingBulk.Joint.Negative.FamilyPoleCenter

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open scoped Topology

theorem compact_family_dimension_uniform_pole (B : ℂ×E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {P : Set E} (hP : IsCompact P)
    (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈P,B (0,eta)≠0) :
    ∃ δ R C : ℝ, 0<δ ∧ 0<R ∧ 0<C ∧ C*δ<R ∧ ∀eta∈P,∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∀ v : Config n, ‖v‖<δ → ∃ t∈closedBall (1-Complex.cos d) R,
        poleEquation (familyMember B eta) phi hphi d t v=0 ∧
        AnalyticAt ℂ (fun z : Config n × ℂ => poleEquation (familyMember B eta) phi hphi d z.2 z.1) (v,t) ∧
        deriv (fun s => poleEquation (familyMember B eta) phi hphi d s v) t≠0 ∧
        ‖t-(1-Complex.cos d)‖≤C*‖v‖ ∧
        (ZeroMean v → ‖t-(1-Complex.cos d)‖≤C*averageSquaredNorm v) ∧
        ∀ s∈closedBall (1-Complex.cos d) R, poleEquation (familyMember B eta) phi hphi d s v=0 → s=t := by
  obtain ⟨ρ,hρ,hphase⟩ := compact_family_uniform_slope B phi hphi hP hB hB0
  obtain ⟨δ₀,M,hδ₀,hM,hcenter⟩ := compact_family_pole_center_bounds B phi hphi hP hB
  let cfun : E→ℂ := fun eta=>centralParameterSlope (familyMember B eta) phi 0
  have hcn (eta : E) (heta : eta∈P) : cfun eta≠0 :=
    centralParameterSlope_ne_zero (familyMember B eta) phi hphi 0
      (by simpa only [Complex.cos_zero,sub_self,familyMember] using hB0 eta heta)
  have hca (eta : E) (heta : eta∈P) : AnalyticAt ℂ cfun eta := by
    simp only [cfun,centralParameterSlope,Complex.cos_zero,sub_self,familyMember]
    exact analyticAt_const.mul ((hB eta heta).comp (f:=fun e : E=>(0,e))
      (analyticAt_const.prod analyticAt_id))
  have hcont : ContinuousOn (fun eta=>(cfun eta)⁻¹) P := fun eta heta=>
    ((hca eta heta).inv (hcn eta heta)).continuousAt.continuousWithinAt
  obtain ⟨L0,hL0⟩ := hP.exists_bound_of_continuousOn hcont
  let L : ℝ := max L0 0+1
  have hL : 0<L := by dsimp [L]; linarith [le_max_right L0 0]
  let R := ρ/4
  have hR : 0<R := div_pos hρ (by norm_num)
  let D := L*M
  have hK : 0<D := mul_pos hL hM
  have ht : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<R := by
    have hh : ContinuousAt (fun d : ℂ => ‖1-Complex.cos d‖) 0 := by fun_prop
    exact hh.eventually_lt continuousAt_const (by simpa using hR)
  obtain ⟨η,hη,hτ⟩ := Metric.mem_nhds_iff.mp ht
  let δ := min δ₀ (min R (min η (R/(2*(D+1)))))
  have hδ : 0<δ := lt_min hδ₀ (lt_min hR (lt_min hη (by positivity)))
  have hd0 : δ≤δ₀ := min_le_left _ _
  have hdR : δ≤R := (min_le_right _ _).trans (min_le_left _ _)
  have hdη : δ≤η := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdK : δ≤R/(2*(D+1)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsize : (2*D)*δ<R := by
    have hh := (le_div_iff₀ (show 0<2*(D+1) by positivity)).mp hdK
    nlinarith
  refine ⟨δ,R,2*D,hδ,hR,by positivity,hsize,?_⟩
  intro eta heta n hn d hd v hv
  let c := centralParameterSlope (familyMember B eta) phi 0
  have hc : c≠0 := hcn eta heta
  have hci : ‖c⁻¹‖≤L := by
    have h := hL0 eta heta
    dsimp [L]
    linarith [le_max_left L0 0]
  have hLM : ‖c⁻¹‖*M≤D := mul_le_mul_of_nonneg_right hci hM.le
  let τ := 1-Complex.cos d
  have hτR : ‖τ‖<R := hτ (show d∈ball (0:ℂ) η by simpa using hd.trans_le hdη)
  have hdρ : ‖d‖<R := hd.trans_le hdR
  have hvρ : ‖v‖<R := hv.trans_le hdR
  have hdata (t : ℂ) (ht : t∈closedBall τ R) (i : Fin n) :
      AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase (familyMember B eta) phi hphi z.1 z.2) (t,d+v i) ∧
        ‖phaseParameterSlope (familyMember B eta) phi hphi (t,d+v i)-c‖≤‖c‖/4 := by
    apply hphase eta heta
    · have hdist : ‖t-τ‖≤R := by simpa only [mem_closedBall,dist_eq_norm] using ht
      have hh := norm_le_norm_sub_add t τ
      dsimp [R] at *
      linarith
    · have hh := norm_add_le d (v i)
      have hi := norm_le_pi_norm v i
      dsimp [R] at *
      linarith
  have hL : LipschitzOnWith (1/2) (poleNewton (familyMember B eta) phi hphi d v) (closedBall τ R) := by
    apply (convex_closedBall τ R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (poleNewton_hasDerivAt (familyMember B eta) phi hphi d t v (fun i => (hdata t ht i).1)).hasDerivWithinAt)
    intro t ht
    have hh := poleNewton_slope_norm_le hn (familyMember B eta) phi hphi d t v hc (fun i => (hdata t ht i).2)
    change ‖1-(centralParameterSlope (familyMember B eta) phi 0)⁻¹*mean (fun i => phaseParameterSlope (familyMember B eta) phi hphi (t,d+v i))‖≤(1/2:ℝ)
    linarith
  have hstart := hcenter eta heta n hn d (hd.trans_le hd0) v (hv.trans_le hd0)
  have he : ‖poleNewton (familyMember B eta) phi hphi d v τ-τ‖=‖c⁻¹‖*‖poleAverage (familyMember B eta) phi hphi d τ v‖ := by
    have hh : poleNewton (familyMember B eta) phi hphi d v τ-τ= -c⁻¹*poleAverage (familyMember B eta) phi hphi d τ v := by
      unfold poleNewton
      dsimp [c]
      ring
    rw [hh,norm_mul,norm_neg]
  have hcent : ‖poleNewton (familyMember B eta) phi hphi d v τ-τ‖≤R/2 := by
    rw [he]
    have hbound := mul_le_mul_of_nonneg_left hstart.1 (norm_nonneg c⁻¹)
    have hdelta := (le_div_iff₀ (show 0<2*(D+1) by positivity)).mp hdK
    change ‖c⁻¹‖*‖poleAverage (familyMember B eta) phi hphi d τ v‖≤R/2
    dsimp [D] at hdelta
    nlinarith [mul_nonneg (norm_nonneg c⁻¹) hM.le]
  obtain ⟨t,ht,hfix,hbound,hunique⟩ := exists_unique_half_contraction_fixedPoint
    (poleNewton (familyMember B eta) phi hphi d v) τ hR.le hL hcent
  have hz : poleAverage (familyMember B eta) phi hphi d t v=0 := by
    have hh : c⁻¹*poleAverage (familyMember B eta) phi hphi d t v=0 := by
      change t-c⁻¹*poleAverage (familyMember B eta) phi hphi d t v=t at hfix
      linear_combination -hfix
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hc)
  have hEq : poleEquation (familyMember B eta) phi hphi d t v=0 := by
    have hn' : (n:ℂ)≠0 := by exact_mod_cast hn
    have hh : poleEquation (familyMember B eta) phi hphi d t v=poleAverage (familyMember B eta) phi hphi d t v*(n:ℂ) := by
      unfold poleAverage
      rw [div_mul_cancel₀ _ hn']
    rw [hh,hz,zero_mul]
  refine ⟨t,ht,hEq,
    poleEquation_analyticAt_of_phase (familyMember B eta) phi hphi d t v (fun i => (hdata t ht i).1),
    poleEquation_parameter_deriv_ne_zero_of_close hn (familyMember B eta) phi hphi d t v hc
      (fun i => (hdata t ht i).1) (fun i => (hdata t ht i).2),?_,?_,?_⟩
  · rw [he] at hbound
    have hh := mul_le_mul_of_nonneg_left hstart.1 (norm_nonneg c⁻¹)
    have hm := mul_le_mul_of_nonneg_right hLM (norm_nonneg v)
    nlinarith
  · intro hv0
    rw [he] at hbound
    have hh := mul_le_mul_of_nonneg_left (hstart.2 hv0) (norm_nonneg c⁻¹)
    have hm := mul_le_mul_of_nonneg_right hLM (show 0≤averageSquaredNorm v by unfold averageSquaredNorm; positivity)
    nlinarith
  · intro s hs hEq
    apply hunique s hs
    simp only [poleNewton,poleAverage,hEq,zero_div,mul_zero,sub_zero]

end
end IsingBulk.Joint.Negative
