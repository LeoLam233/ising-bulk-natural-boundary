import IsingBulk.Joint.Negative.FamilyAngular
import IsingBulk.Joint.Negative.FamilyScalar
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open scoped Topology
set_option maxHeartbeats 800000

/-- Any two sufficiently small actual pole roots obey an arbitrarily small,
dimension-independent configuration Lipschitz bound. No root extension is assumed. -/
theorem compact_family_pole_small_comparison (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {P : Set E} (hP : IsCompact P)
    (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈P,B (0,eta)≠0)
    (κ : ℝ) (hκ : 0<κ) :
    ∃ δ : ℝ, 0<δ ∧ ∀eta∈P,∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∀ v w : Config n, ‖v‖<δ → ‖w‖<δ → ∀ t s : ℂ, ‖t‖<δ → ‖s‖<δ →
      poleEquation (familyMember B eta) phi hphi d t v=0 → poleEquation (familyMember B eta) phi hphi d s w=0 →
      ‖t-s‖≤κ*‖v-w‖ := by
  let cfun : E→ℂ := fun eta=>centralParameterSlope (familyMember B eta) phi 0
  have hcn (eta : E) (heta : eta∈P) : cfun eta≠0 :=
    centralParameterSlope_ne_zero (familyMember B eta) phi hphi 0
      (by simpa only [Complex.cos_zero,sub_self,familyMember] using hB0 eta heta)
  have hca (eta : E) (heta : eta∈P) : AnalyticAt ℂ cfun eta := by
    simp only [cfun,centralParameterSlope,Complex.cos_zero,sub_self,familyMember]
    exact analyticAt_const.mul ((hB eta heta).comp (f:=fun e : E=>(0,e))
      (analyticAt_const.prod analyticAt_id))
  obtain ⟨K0,hK0⟩ := hP.exists_bound_of_continuousOn (fun eta heta=>
    ((hca eta heta).inv (hcn eta heta)).continuousAt.continuousWithinAt)
  let K : ℝ := max K0 0
  have hK : 0≤K := le_max_right _ _
  let ε := κ/(2*(K+1))
  have hε : 0<ε := div_pos hκ (by positivity)
  obtain ⟨η,hη,hangular⟩ := compact_family_angular_small B phi hphi hP hB ε hε
  obtain ⟨ρ,hρ,hphase⟩ := compact_family_uniform_slope B phi hphi hP hB hB0
  let δ := min η (ρ/4)
  have hδ : 0<δ := lt_min hη (by positivity)
  have hδη : δ≤η := min_le_left _ _
  have hδρ : δ≤ρ/4 := min_le_right _ _
  refine ⟨δ,hδ,?_⟩
  intro eta heta n hn d hd v w hv hw t s ht hs htv hsw
  let c := centralParameterSlope (familyMember B eta) phi 0
  have hc : c≠0 := hcn eta heta
  have hci : ‖c⁻¹‖≤K := (hK0 eta heta).trans (le_max_left _ _)
  have hdata (u : ℂ) (hu : u∈closedBall 0 δ) (i : Fin n) :
      AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase (familyMember B eta) phi hphi z.1 z.2) (u,d+v i) ∧
        ‖phaseParameterSlope (familyMember B eta) phi hphi (u,d+v i)-c‖≤‖c‖/4 := by
    apply hphase eta heta
    · have hu' : ‖u‖≤δ := by simpa using hu
      linarith
    · have hi := norm_le_pi_norm v i
      have ha := norm_add_le d (v i)
      linarith
  have hLip : LipschitzOnWith (1/2) (poleNewton (familyMember B eta) phi hphi d v) (closedBall 0 δ) := by
    apply (convex_closedBall 0 δ).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun u hu => (poleNewton_hasDerivAt (familyMember B eta) phi hphi d u v (fun i => (hdata u hu i).1)).hasDerivWithinAt)
    intro u hu
    have hh := poleNewton_slope_norm_le hn (familyMember B eta) phi hphi d u v hc (fun i => (hdata u hu i).2)
    change ‖1-(centralParameterSlope (familyMember B eta) phi 0)⁻¹*mean (fun i => phaseParameterSlope (familyMember B eta) phi hphi (u,d+v i))‖≤(1/2:ℝ)
    linarith
  have ht' : t∈closedBall 0 δ := by simpa using ht.le
  have hs' : s∈closedBall 0 δ := by simpa using hs.le
  have hft : poleNewton (familyMember B eta) phi hphi d v t=t := by simp [poleNewton,poleAverage,htv]
  have hfs : poleNewton (familyMember B eta) phi hphi d w s=s := by simp [poleNewton,poleAverage,hsw]
  have hfirst := hLip.dist_le_mul t ht' s hs'
  simp only [dist_eq_norm,hft,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hfirst
  have hsecond0 := poleAverage_angular_bound hn (familyMember B eta) phi hphi d s v w ε hε.le
    (fun i => hangular eta heta s d (v i) (w i) (hs.trans_le hδη) (hd.trans_le hδη)
      ((norm_le_pi_norm v i).trans_lt (hv.trans_le hδη))
      ((norm_le_pi_norm w i).trans_lt (hw.trans_le hδη)))
  have hdiff : poleNewton (familyMember B eta) phi hphi d v s-poleNewton (familyMember B eta) phi hphi d w s=
      -c⁻¹*(poleAverage (familyMember B eta) phi hphi d s v-poleAverage (familyMember B eta) phi hphi d s w) := by
    unfold poleNewton
    dsimp [c]
    ring
  have hsecond : ‖poleNewton (familyMember B eta) phi hphi d v s-s‖≤K*(ε*‖v-w‖) := by
    rw [hfs] at hdiff
    rw [hdiff,norm_mul,norm_neg]
    exact (mul_le_mul_of_nonneg_left hsecond0 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hci (by positivity))
  have htriangle := norm_sub_le_norm_sub_add_norm_sub t (poleNewton (familyMember B eta) phi hphi d v s) s
  have hscale : 2*K*ε≤κ := by
    have he : ε*(2*(K+1))=κ := by dsimp [ε]; field_simp
    nlinarith
  have hscale' := mul_le_mul_of_nonneg_right hscale (norm_nonneg (v-w))
  nlinarith

end
end IsingBulk.Joint.Negative
