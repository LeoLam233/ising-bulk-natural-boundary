import IsingBulk.Anisotropic.NegativeCycles.JointCothRemainder
import IsingBulk.Anisotropic.NegativeCycles.JointDensityAnalytic
import IsingBulk.Anisotropic.NegativeCycles.UniformCothSubtraction
import IsingBulk.Anisotropic.NegativeCycles.InnerPhaseDisk
import IsingBulk.Anisotropic.NegativeCycles.LocalDensityAnalytic
import IsingBulk.Anisotropic.NegativeNormalForm.PoleNewton

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
set_option maxHeartbeats 800000
open Set Metric NegativeNormalForm
open scoped BigOperators

def remainderGaussianEnvelope (M : ℝ) (m : ℕ) : ℝ :=
  (M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2)

def actualInnerRemainder (B rootB : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (R₀ : ℂ → ℂ) (m : ℕ) (v : Config (2*m+1)) (T : ℂ) : ℂ → ℂ :=
  cothPoleRemainder (2*m+1) R₀ (fun t => poleAverage B phi hphi 0 t v)
    (fun t => formFactorNumerator B rootB phi hphi 0 t v) T

/-- The actual inner analytic remainder has a c/N disk and a Gaussian bound,
with constants fixed before N and the angle configuration. Pole subtraction is
performed on its own larger fixed disk, without a contour-distance assumption. -/
theorem exists_actual_inner_remainder (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) :
    ∃ (R₀ : ℂ → ℂ) (r c σ C M : ℝ), 0<r ∧ 0<c ∧ 0<σ ∧ 0<C ∧ 1≤M ∧
      ∀ m : ℕ, ∀ v : Config (2*m+1), absoluteEnergy v<σ → ∀ T : ℂ,
        ‖T‖≤r/2 → poleEquation B phi hphi 0 T v=0 →
        AnalyticOnNhd ℂ (actualInnerRemainder B rootB phi hphi R₀ m v T) (ball 0 (c/(2*m+1:ℕ))) ∧
        (∀ t∈ball 0 (c/(2*m+1:ℕ)),
          ‖actualInnerRemainder B rootB phi hphi R₀ m v T t‖≤C*remainderGaussianEnvelope M m) ∧
        (∀ Tmap : Config (2*m+1) → ℂ, AnalyticAt ℂ Tmap v → Tmap v=T →
          ∀ t∈ball 0 (c/(2*m+1:ℕ)),
            AnalyticAt ℂ (fun p : Config (2*m+1) × ℂ =>
              actualInnerRemainder B rootB phi hphi R₀ m p.1 (Tmap p.1) p.2) (v,t)) ∧
        ∀ t∈ball 0 (c/(2*m+1:ℕ)), t≠T →
          formFactorNumerator B rootB phi hphi 0 t v*cothHalf (fun u => poleEquation B phi hphi 0 u v) t=
            (2*formFactorNumerator B rootB phi hphi 0 T v/poleParameterDerivative B phi hphi 0 T v)/(t-T)+
              actualInnerRemainder B rootB phi hphi R₀ m v T t := by
  obtain ⟨R₀,ρ,K,hρ,hK,hRa,hRb,hReq⟩ := exists_uniform_coth_remainder
  obtain ⟨a,ha,hslope⟩ := negativePhase_uniform_slope B phi hphi hB hB0
  obtain ⟨b,hb,hanalytic⟩ := local_density_phase_joint_analytic B rootB phi hphi hB hrB
  obtain ⟨δ,M,hδ,hM,hnum⟩ := formFactorNumerator_complex_uniform_bound B rootB phi hphi hB hrB
  let r := min a (min b δ)
  have hr : 0<r := lt_min ha (lt_min hb hδ)
  have hra : r≤a := min_le_left _ _
  have hrb : r≤b := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r≤δ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨c,σ,hc,hσ,hcr,hphase⟩ := exists_inner_phase_disk B phi hphi hB (r/2) ρ (by positivity) hρ
  let c₀ := centralParameterSlope B phi 0
  have hc₀ : c₀≠0 := centralParameterSlope_ne_zero B phi hphi 0 (by simpa using hB0)
  let C := K+16/(‖c₀‖*r)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨R₀,r,c,σ,C,M,hr,hc,hσ,hC,hM,?_⟩
  intro m v hv T hT hzero
  have hn : 2*m+1≠0 := by omega
  have hnpos : (0:ℝ)<(2*m+1:ℕ) := by positivity
  have hn1 : (1:ℝ)≤(2*m+1:ℕ) := by exact_mod_cast (show 1≤2*m+1 by omega)
  have hnc : ((2*m+1:ℕ):ℂ)≠0 := by exact_mod_cast hn
  have hvnorm : ‖v‖<r/2 := (hphase (2*m+1) hn 0 v (by simpa using div_pos hc hnpos) hv).2.1
  have hvi (i : Fin (2*m+1)) : ‖v i‖<r := by linarith [norm_le_pi_norm v i]
  let f : ℂ → ℂ := fun t => poleAverage B phi hphi 0 t v
  let H : ℂ → ℂ := fun t => formFactorNumerator B rootB phi hphi 0 t v
  have hjoint (t : ℂ) (ht : t∈ball 0 r) := hanalytic m 0 t v
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
    have hp (i : Fin (2*m+1)) := hslope t (v i)
      ((show ‖t‖<r by simpa using ht).trans_le hra) ((hvi i).trans_le hra)
    have hd := poleAverage_hasDerivAt B phi hphi 0 t v (fun i => by simpa only [zero_add] using (hp i).1)
    change ‖deriv (fun s => poleAverage B phi hphi 0 s v) t-c₀‖≤_
    rw [hd.deriv]
    exact norm_mean_sub_le hn _ c₀ (by positivity) (fun i => by simpa only [zero_add] using (hp i).2)
  have hE : 0≤remainderGaussianEnvelope M m := by unfold remainderGaussianEnvelope; positivity
  have hbound : ∀ t∈ball 0 r, ‖H t‖≤remainderGaussianEnvelope M m := by
    intro t ht
    exact hnum m 0 t v (by simpa using hδ)
      ((show ‖t‖<r by simpa using ht).trans_le hrδ) (fun i => (hvi i).trans_le hrδ)
  have hηr : c/(2*m+1:ℕ)≤r/2 := by
    have hh := div_le_self hc.le hn1
    linarith
  have heq (t : ℂ) : ((2*m+1:ℕ):ℂ)*f t=poleEquation B phi hphi 0 t v := by
    dsimp [f,poleAverage]
    exact mul_div_cancel₀ _ hnc
  obtain ⟨R,hR,hRanalytic,hRbound,hRe⟩ := uniform_coth_subtraction (2*m+1) hn hr hηr hc₀ hE
    hf (by simp only [f,poleAverage,hzero,zero_div]) hder hT hH hbound hRa hRb hReq
    (fun t ht => by rw [heq]; exact (hphase _ hn t v (by simpa using ht) hv).2.2)
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
      _ = _ := by dsimp [C]; ring
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
      exact (hphase _ hn t v (by simpa using ht) hv).2.2
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
end IsingBulk.Anisotropic.NegativeCycles
