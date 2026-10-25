import IsingBulk.Joint.Negative.FamilyCyclePhaseDisk
import IsingBulk.Joint.Negative.FamilyCycleBounds
import IsingBulk.Joint.Negative.FamilyCycleDensityAnalytic
import IsingBulk.Joint.Negative.FamilyWindingSlope
import IsingBulk.Anisotropic.NegativeCycles.ActualInnerRemainder

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_actual_inner_remainder (B rootB : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta∈Q, B (0,eta)≠0)
    (hrB : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta)) :
    ∃ (R₀ : ℂ → ℂ) (r c σ C M : ℝ), 0<r ∧ 0<c ∧ 0<σ ∧ 0<C ∧ 1≤M ∧
      ∀ eta∈Q, ∀ m : ℕ, ∀ v : Config (2*m+1), absoluteEnergy v<σ → ∀ T : ℂ,
        ‖T‖≤r/2 → poleEquation (familyMember B eta) phi hphi 0 T v=0 →
        AnalyticOnNhd ℂ (actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m v T) (ball 0 (c/(2*m+1:ℕ))) ∧
        (∀ t∈ball 0 (c/(2*m+1:ℕ)),
          ‖actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m v T t‖≤C*remainderGaussianEnvelope M m) ∧
        (∀ Tmap : Config (2*m+1) → ℂ, AnalyticAt ℂ Tmap v → Tmap v=T →
          ∀ t∈ball 0 (c/(2*m+1:ℕ)),
            AnalyticAt ℂ (fun p : Config (2*m+1) × ℂ =>
              actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m p.1 (Tmap p.1) p.2) (v,t)) ∧
        ∀ t∈ball 0 (c/(2*m+1:ℕ)), t≠T →
          formFactorNumerator (familyMember B eta) (familyMember rootB eta) phi hphi 0 t v*cothHalf (fun u => poleEquation (familyMember B eta) phi hphi 0 u v) t=
            (2*formFactorNumerator (familyMember B eta) (familyMember rootB eta) phi hphi 0 T v/poleParameterDerivative (familyMember B eta) phi hphi 0 T v)/(t-T)+
              actualInnerRemainder (familyMember B eta) (familyMember rootB eta) phi hphi R₀ m v T t := by
  obtain ⟨R₀,ρ,K,hρ,hK,hRa,hRb,hReq⟩ := exists_uniform_coth_remainder
  obtain ⟨a,ha,hslope⟩ := compact_family_uniform_slope B phi hphi hQ hB hB0
  obtain ⟨b,hb,hanalytic⟩ := compact_family_cycle_density_joint_analytic B rootB phi hphi hQ hB hrB
  obtain ⟨δ,M,hδ,hM,hnum⟩ := compact_family_cycle_numerator_gaussian B rootB phi hphi hQ hB hrB
  let r := min a (min b δ)
  have hr : 0<r := lt_min ha (lt_min hb hδ)
  have hra : r≤a := min_le_left _ _
  have hrb : r≤b := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r≤δ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨c,σ,hc,hσ,hcr,hphase⟩ := compact_family_inner_phase_disk B phi hphi hQ hB (r/2) ρ (by positivity) hρ
  obtain ⟨cmin,hcmin,hclower⟩ := compact_family_central_slope_lower B phi hphi hQ hB hB0
  let C := K+16/(cmin*r)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨R₀,r,c,σ,C,M,hr,hc,hσ,hC,hM,?_⟩
  intro eta heta m v hv T hT hzero
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  change poleEquation B phi hphi 0 T v=0 at hzero
  let c₀ := centralParameterSlope B phi 0
  have hc₀ : c₀≠0 := centralParameterSlope_ne_zero B phi hphi 0 (by simpa only [Complex.cos_zero,sub_self,B,familyMember] using hB0 eta heta)
  have hcl : cmin≤‖c₀‖ := hclower eta heta
  have hn : 2*m+1≠0 := by omega
  have hnpos : (0:ℝ)<(2*m+1:ℕ) := by positivity
  have hn1 : (1:ℝ)≤(2*m+1:ℕ) := by exact_mod_cast (show 1≤2*m+1 by omega)
  have hnc : ((2*m+1:ℕ):ℂ)≠0 := by exact_mod_cast hn
  have hvnorm : ‖v‖<r/2 := (hphase eta heta (2*m+1) hn 0 v (by simpa using div_pos hc hnpos) hv).2.1
  have hvi (i : Fin (2*m+1)) : ‖v i‖<r := by linarith [norm_le_pi_norm v i]
  let f : ℂ → ℂ := fun t => poleAverage B phi hphi 0 t v
  let H : ℂ → ℂ := fun t => formFactorNumerator B rootB phi hphi 0 t v
  have hjoint (t : ℂ) (ht : t∈ball 0 r) := hanalytic eta heta m 0 t v
    ((show ‖t‖<r by simpa using ht).trans_le hrb)
    (fun i => by simpa only [zero_add] using (hvi i).trans_le hrb)
  have hlocal (t : ℂ) (ht : t∈ball 0 r) : AnalyticAt ℂ H t ∧
      AnalyticAt ℂ (fun s => poleEquation B phi hphi 0 s v) t := by
    have hm : AnalyticAt ℂ (fun s : ℂ => (v,s)) t := analyticAt_const.prod analyticAt_id
    exact ⟨(hjoint t ht).1.fun_comp_of_eq (f := fun s : ℂ => (v,s)) hm rfl,(hjoint t ht).2.fun_comp_of_eq (f := fun s : ℂ => (v,s)) hm rfl⟩
  have hf : AnalyticOnNhd ℂ f (ball 0 r) := fun t ht => (hlocal t ht).2.div_const
  have hH : AnalyticOnNhd ℂ H (ball 0 r) := fun t ht => (hlocal t ht).1
  have hder : ∀ t∈ball 0 r, ‖deriv f t-c₀‖≤‖c₀‖/4 := by
    intro t ht
    have hp (i : Fin (2*m+1)) := hslope eta heta t (v i)
      ((show ‖t‖<r by simpa using ht).trans_le hra) ((hvi i).trans_le hra)
    have hd := poleAverage_hasDerivAt B phi hphi 0 t v (fun i => by simpa only [zero_add] using (hp i).1)
    change ‖deriv (fun s => poleAverage B phi hphi 0 s v) t-c₀‖≤_
    rw [hd.deriv]
    exact norm_mean_sub_le hn _ c₀ (by positivity) (fun i => by simpa only [zero_add] using (hp i).2)
  have hE : 0≤remainderGaussianEnvelope M m := by unfold remainderGaussianEnvelope; positivity
  have hbound : ∀ t∈ball 0 r, ‖H t‖≤remainderGaussianEnvelope M m := by
    intro t ht
    exact hnum eta heta m 0 t v (by simpa using hδ)
      ((show ‖t‖<r by simpa using ht).trans_le hrδ) (fun i => (hvi i).trans_le hrδ)
  have hηr : c/(2*m+1:ℕ)≤r/2 := by
    have hh := div_le_self hc.le hn1
    linarith
  have heq (t : ℂ) : ((2*m+1:ℕ):ℂ)*f t=poleEquation B phi hphi 0 t v := by
    dsimp [f,poleAverage]
    exact mul_div_cancel₀ _ hnc
  obtain ⟨R,hR,hRanalytic,hRbound,hRe⟩ := uniform_coth_subtraction (2*m+1) hn hr hηr hc₀ hE
    hf (by simp only [f,poleAverage,hzero,zero_div]) hder hT hH hbound hRa hRb hReq
    (fun t ht => by rw [heq]; exact (hphase eta heta _ hn t v (by simpa using ht) hv).2.2)
  subst R
  refine ⟨hRanalytic,?_,?_,?_⟩
  · intro t ht
    have hden : ‖c₀‖*r≤((2*m+1:ℕ):ℝ)*‖c₀‖*r := by
      simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hn1 (mul_nonneg (norm_nonneg c₀) hr.le)
    have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤16)
      (mul_pos (norm_pos_iff.mpr hc₀) hr) hden
    apply (hRbound t ht).trans
    calc
      _ ≤ remainderGaussianEnvelope M m*(K+16/(‖c₀‖*r)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hh) hE
      _ ≤ remainderGaussianEnvelope M m*C := by
        apply mul_le_mul_of_nonneg_left _ hE
        dsimp [C]
        exact add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤16)
          (mul_pos hcmin hr) (mul_le_mul_of_nonneg_right hcl hr.le))
      _ = _ := by ring
  · intro Tmap hTm hTv t ht
    have htr : t∈ball (0:ℂ) r := ball_subset_ball (by linarith : c/(2*m+1:ℕ)≤r) ht
    have hTr : T∈ball (0:ℂ) r := by simpa using (show ‖T‖<r by linarith)
    have hTmBall : Tmap v∈ball (0:ℂ) r := hTv.symm ▸ hTr
    have hFj (u : ℂ) (hu : u∈ball 0 r) :
        AnalyticAt ℂ (fun p : Config (2*m+1) × ℂ => poleAverage B phi hphi 0 p.2 p.1) (v,u) :=
      (hjoint u hu).2.div_const
    have hfac : dslope f (Tmap v) t≠0 := by
      rw [hTv]
      exact (normalized_phase_factor_bounds hc₀ hf hder hTr).2 t htr |>.2.2
    have hdt : deriv f (Tmap v)≠0 := by
      rw [hTv]
      simpa only [dslope_same] using (normalized_phase_factor_bounds hc₀ hf hder hTr).2 T hTr |>.2.2
    have hpnf : ‖((2*m+1:ℕ):ℂ)*f t‖<ρ := by
      rw [heq]
      exact (hphase eta heta _ hn t v (by simpa using ht) hv).2.2
    have hRta : AnalyticAt ℂ R₀ (((2*m+1:ℕ):ℂ)*f t) := hRa _ (by simpa using hpnf)
    exact cothPoleRemainder_joint_analytic (2*m+1) (hFj t htr) (hFj (Tmap v) hTmBall)
      (hjoint t htr).1 (hjoint (Tmap v) hTmBall).1 hTm hfac hdt hRta
  · intro t ht htT
    have hTr : T∈ball (0:ℂ) r := by simpa using (show ‖T‖<r by linarith)
    have hdf : deriv f T=deriv (fun u => poleEquation B phi hphi 0 u v) T/((2*m+1:ℕ):ℂ) :=
      ((hlocal T hTr).2.differentiableAt.hasDerivAt.div_const ((2*m+1:ℕ):ℂ)).deriv
    have hdF : ((2*m+1:ℕ):ℂ)*deriv f T=poleParameterDerivative B phi hphi 0 T v := by
      rw [hdf]
      exact mul_div_cancel₀ _ hnc
    have hh := hRe t ht htT
    rw [show (fun u => ((2*m+1:ℕ):ℂ)*f u)=(fun u => poleEquation B phi hphi 0 u v) from funext heq,hdF] at hh
    exact hh

end
end IsingBulk.Joint.Negative
