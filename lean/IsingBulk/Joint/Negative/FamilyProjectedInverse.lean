import IsingBulk.Joint.Negative.FamilyRootBounds
import IsingBulk.Joint.Negative.FamilyPoleLipschitz
import IsingBulk.Anisotropic.NegativeNormalForm.UniformProjectedInverse

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open scoped Topology
set_option maxHeartbeats 800000

/-- The actual projected map has an equivariant inverse on one dimension-independent
ball. Scalar bounds, pole existence and contraction are all derived from B and phi. -/
theorem compact_family_projected_inverse (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {P : Set E} (hP : IsCompact P)
    (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈P,B (0,eta)≠0) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀eta∈P,∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<r →
      ∃ (T : Config n → ℂ) (V : Config n → Config n),
        AnalyticOnNhd ℂ T (ball 0 (2*r)) ∧ T 0=1-Complex.cos d ∧
        (∀ e v, T (permute e v)=T v) ∧
        (∀ v : Config n, ‖v‖<2*r → poleEquation (familyMember B eta) phi hphi d (T v) v=0 ∧
          (ZeroMean v → ‖T v-(1-Complex.cos d)‖≤C*averageSquaredNorm v)) ∧
        (∀ v w : Config n, ‖v‖<2*r → ‖w‖<2*r → ‖T v-T w‖≤‖v-w‖) ∧
        LipschitzOnWith (1/64) (fun v => projectedExtension (fun x => phaseSeparableMap (familyMember B eta) phi hphi d (T x) x) v-v) (closedBall 0 r) ∧
        AnalyticOnNhd ℂ V (ball 0 (r/2)) ∧ AnalyticAt ℂ V 0 ∧ V 0=0 ∧
        HasFDerivAt V (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
        (∀ e v, V (permute e v)=permute e (V v)) ∧
        (∀ y, ‖y‖≤r/2 → ‖V y‖≤r ∧ ‖V y‖≤2*‖y‖ ∧
          projectedExtension (fun v => phaseSeparableMap (familyMember B eta) phi hphi d (T v) v) (V y)=y ∧
          (ZeroMean y → ZeroMean (V y) ∧ project (phaseSeparableMap (familyMember B eta) phi hphi d (T (V y)) (V y))=y)) ∧
        (∀ y z, ‖y‖≤r/2 → ‖z‖≤r/2 → ‖V y-V z‖≤2*‖y-z‖) := by
  obtain ⟨ρ,L,hρ,hL,hroot,hrootLip⟩ := compact_family_root_small B phi hphi hP hB hB0 (1/512) (by norm_num)
  obtain ⟨δ,C,hδ,hC,hpole⟩ := compact_family_small_lipschitz_pole B phi hphi hP hB hB0 1 ρ (by norm_num) hρ
  obtain ⟨a,ha,hbranch⟩ := compact_family_branch B phi hP hB hB0
  let r := min δ (min ρ (min a (1/(1024*(L+1)))))/4
  have hr : 0<r := div_pos (lt_min hδ (lt_min hρ (lt_min ha (by positivity)))) (by norm_num)
  have hrδ : 4*r≤δ := by dsimp [r]; linarith [min_le_left δ (min ρ (min a (1/(1024*(L+1)))))]
  have hrρ : 4*r≤ρ := by
    have hh := (min_le_right δ (min ρ (min a (1/(1024*(L+1)))))).trans (min_le_left ρ (min a (1/(1024*(L+1)))))
    dsimp [r]; linarith
  have hra : 4*r≤a := by
    have hh := (min_le_right δ (min ρ (min a (1/(1024*(L+1)))))).trans
      ((min_le_right ρ (min a (1/(1024*(L+1))))).trans (min_le_left a (1/(1024*(L+1)))))
    dsimp [r]; linarith
  have hrL : 2*r*L≤1/512 := by
    have hh := (min_le_right δ (min ρ (min a (1/(1024*(L+1)))))).trans
      ((min_le_right ρ (min a (1/(1024*(L+1))))).trans (min_le_right a (1/(1024*(L+1)))))
    have hh' : 4*r≤1/(1024*(L+1)) := by dsimp [r]; linarith
    have hh'' := (le_div_iff₀ (show 0<1024*(L+1) by positivity)).mp hh'
    nlinarith
  refine ⟨r,C,hr,hC,?_⟩
  intro eta heta n hn d hd
  obtain ⟨T,hT,hT0,hTeq,hTs,hTLip⟩ := hpole eta heta n hn d (by linarith)
  have hbd := hbranch eta heta d (by linarith)
  have hTanalytic : AnalyticAt ℂ T 0 := hT 0 (by simpa using hδ)
  let U : Config n → Config n := fun v => phaseSeparableMap (familyMember B eta) phi hphi d (T v) v
  have hU : AnalyticAt ℂ U 0 := phaseSeparableMap_along_pole_analyticAt (familyMember B eta) phi hphi d hbd.1 hbd.2.1 hbd.2.2 T hTanalytic hT0
  have hdU : HasFDerivAt U (ContinuousLinearMap.id ℂ (Config n)) 0 :=
    phaseSeparableMap_along_pole_hasFDerivAt (familyMember B eta) phi hphi d hbd.1 hbd.2.1 hbd.2.2 T hTanalytic hT0
  have hU0 : U 0=0 := phaseSeparableMap_zero_equivariant_aux (familyMember B eta) phi hphi d (T 0)
  have hUeq (e : Equiv.Perm (Fin n)) (v : Config n) : U (permute e v)=permute e (U v) := by
    dsimp only [U]
    rw [hTeq]
    exact phaseSeparableMap_permute (familyMember B eta) phi hphi d (T v) v e
  have hsmall (v : Config n) (hv : v∈closedBall 0 (2*r)) : ‖v‖<δ := by
    have hh : ‖v‖≤2*r := by simpa using hv
    linarith
  have hULip : LipschitzOnWith (1/256) (fun v => U v-v) (closedBall 0 (2*r) ∩ {v | ZeroMean v}) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro v hv w hw
    have hh := phaseSeparableMap_error_lipschitz_bound (familyMember B eta) phi hphi d T ρ (2*r) (1/512) L
      (by positivity) (by norm_num) hL.le (by linarith) (by linarith)
      (fun x hx => (hTs x (hsmall x hx)).2.1)
      (fun x hx y hy => by simpa using hTLip x y (hsmall x hx) (hsmall y hy))
      (fun p hp => (hroot eta heta p hp).2) (hrootLip eta heta) v hv.1 w hw.1
    simp only [dist_eq_norm,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : 1/512+2*r*L≤1/256) (norm_nonneg _))
  have hFLip : LipschitzOnWith (1/64) (fun v => projectedExtension U v-v) (closedBall 0 r) := by
    convert projectedExtension_error_lipschitz hn U r (1/256) hULip using 1
    norm_num
  have hUall (x : Config n) (hx : ‖x‖<2*r) : AnalyticAt ℂ U x := by
    have hxδ : ‖x‖<δ := by linarith
    have hTx := hT x (show x∈ball 0 δ by simpa using hxδ)
    apply analyticAt_pi_iff.mpr
    intro i
    have hi := (ContinuousLinearMap.proj i : Config n →L[ℂ] ℂ).analyticAt x
    have hinput : ‖(T x,(d,x i))‖<ρ := by
      exact max_lt (hTs x hxδ).2.1 (max_lt (by linarith) ((norm_le_pi_norm x i).trans_lt (by linarith)))
    have hsqrt := (hroot eta heta (T x,(d,x i)) hinput).1
    change AnalyticAt ℂ (fun v : Config n => v i*Complex.sqrt (phaseEnergy (familyMember B eta) phi hphi d (T v) (v i))) x
    exact hi.mul (hsqrt.comp (f := fun v : Config n => (T v,(d,v i)))
      (hTx.prod (analyticAt_const.prod hi)))
  have hFa : AnalyticOnNhd ℂ (projectedExtension U) (ball 0 r) := by
    intro x hx
    have hx' : ‖x‖<r := by simpa using hx
    have hpx : ‖project x‖<2*r := (norm_project_le hn x).trans_lt (by linarith)
    have hUa : AnalyticAt ℂ U ((projectCLM n) x) := by
      simpa only [projectCLM_apply] using hUall (project x) hpx
    have hinner := hUa.comp (f := fun z : Config n => (projectCLM n) z) ((projectCLM n).analyticAt x)
    exact (((projectCLM n).analyticAt (U ((projectCLM n) x))).comp
      (f := fun z : Config n => U ((projectCLM n) z)) hinner).add ((meanVectorCLM n).analyticAt x)
  obtain ⟨V,hV,hV0,hdV,hVeq,hVs,hVLip⟩ := exists_quantitative_equivariant_projected_inverse hn U hU hU0 hdU hUeq r hr (1/64) (by norm_num) hFLip
  have hVa := quantitative_inverse_analyticOnNhd (projectedExtension U) V r hr (1/64) (by norm_num) hFLip hFa
    (fun y hy => ⟨(hVs y hy).1,(hVs y hy).2.1,(hVs y hy).2.2.1⟩)
  have hVsmall : AnalyticOnNhd ℂ V (ball 0 (r/2)) := hVa.mono (ball_subset_ball (by norm_num; linarith))
  refine ⟨T,V,hT.mono (ball_subset_ball (by linarith)),hT0,hTeq,?_,?_,hFLip,hVsmall,hV,hV0,hdV,hVeq,?_,?_⟩
  · intro v hv
    have hh := hTs v (by linarith)
    exact ⟨hh.1,hh.2.2.2⟩
  · intro v w hv hw
    simpa using hTLip v w (by linarith) (by linarith)
  · intro y hy
    have hy' : ‖y‖≤(1-((1/64:NNReal):ℝ))*r := by norm_num; linarith
    have hh := hVs y hy'
    have hnorm : ‖V y‖≤2*‖y‖ := by
      have hb := hh.2.2.1
      norm_num at hb
      nlinarith [norm_nonneg y]
    exact ⟨by simpa using hh.1,hnorm,hh.2.1,hh.2.2.2⟩
  · intro y z hy hz
    have hy' : ‖y‖≤(1-((1/64:NNReal):ℝ))*r := by norm_num; linarith
    have hz' : ‖z‖≤(1-((1/64:NNReal):ℝ))*r := by norm_num; linarith
    have hh := hVLip y z hy' hz'
    norm_num at hh
    nlinarith [norm_nonneg (y-z)]

end
end IsingBulk.Joint.Negative
