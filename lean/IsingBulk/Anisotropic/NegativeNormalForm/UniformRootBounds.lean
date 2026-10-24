import IsingBulk.Anisotropic.NegativeNormalForm.UniformScalarEnergy
import IsingBulk.Anisotropic.NegativeNormalForm.ProjectedUniformEstimates

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology
open Set Metric
set_option maxHeartbeats 800000

 theorem phaseRootEnergy_origin (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) (hBn : B 0 ≠ 0) :
    Complex.sqrt (phaseEnergy B phi hphi 0 0 0)=1 := by
  have h := phaseEnergy_center B phi hphi 0 (by simpa using hB) (by simpa using hBn)
    (by simp [centralHessian_zero])
  simpa using congrArg Complex.sqrt h

/-- Uniform smallness and Lipschitz control of the actual scalar root, before choosing n. -/
 theorem phaseRootEnergy_uniform_small (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) (hBn : B 0 ≠ 0)
    (ε : ℝ) (hε : 0<ε) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧
      (∀ p : ScalarTriple, ‖p‖<r →
        AnalyticAt ℂ (fun x : ScalarTriple => Complex.sqrt (phaseEnergy B phi hphi x.2.1 x.1 x.2.2)) p ∧
        ‖Complex.sqrt (phaseEnergy B phi hphi p.2.1 p.1 p.2.2)-1‖≤ε) ∧
      (∀ p q : ScalarTriple, ‖p‖<r → ‖q‖<r →
        ‖Complex.sqrt (phaseEnergy B phi hphi p.2.1 p.1 p.2.2)-
          Complex.sqrt (phaseEnergy B phi hphi q.2.1 q.1 q.2.2)‖≤L*‖p-q‖) := by
  obtain ⟨r,L,M,hr,hL,_hM,ha,hl⟩ := analytic_scalarTriple_uniform_lipschitz
    (phaseRootEnergy_triple_analyticAt B phi hphi hB hBn)
  refine ⟨min r (ε/(L+1)),L,lt_min hr (div_pos hε (by linarith)),hL,?_,?_⟩
  · intro p hp
    have hp' := hp.trans_le (min_le_left _ _)
    refine ⟨(ha p hp').1,?_⟩
    have hh := hl p 0 hp' (by simpa using hr)
    simp only [Prod.fst_zero,Prod.snd_zero,phaseRootEnergy_origin B phi hphi hB hBn,sub_zero] at hh
    have hsmall := (lt_div_iff₀ (by linarith : 0<L+1)).mp (hp.trans_le (min_le_right _ _))
    exact hh.trans (by nlinarith [norm_nonneg p])
  · intro p q hp hq
    exact hl p q (hp.trans_le (min_le_left _ _)) (hq.trans_le (min_le_left _ _))

/-- A coordinatewise root perturbation has a dimension-free sup-norm estimate. -/
 theorem coordinateProduct_error_bound {n : ℕ} (S : Config n → Config n)
    (R ε L : ℝ) (hR : 0≤R) (hε : 0≤ε) (hL : 0≤L)
    (v w : Config n) (hw : ‖w‖≤R)
    (hs : ∀ i, ‖S v i-1‖≤ε) (hl : ∀ i, ‖S v i-S w i‖≤L*‖v-w‖) :
    ‖((fun i => v i*S v i)-v)-((fun i => w i*S w i)-w)‖≤(ε+R*L)*‖v-w‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have he : (((fun i => v i*S v i)-v)-((fun i => w i*S w i)-w)) i=
      (v i-w i)*(S v i-1)+w i*(S v i-S w i) := by
    simp only [Pi.sub_apply]
    ring
  rw [he]
  calc
    _ ≤ ‖v i-w i‖*‖S v i-1‖+‖w i‖*‖S v i-S w i‖ := by
      simpa only [norm_mul] using norm_add_le ((v i-w i)*(S v i-1)) (w i*(S v i-S w i))
    _ ≤ ‖v-w‖*ε+R*(L*‖v-w‖) := add_le_add
      (mul_le_mul (norm_le_pi_norm (v-w) i) (hs i) (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul ((norm_le_pi_norm w i).trans hw) (hl i) (norm_nonneg _) hR)
    _ = _ := by ring

/-- The actual separable map inherits the proved scalar root bounds. -/
 theorem phaseSeparableMap_error_lipschitz_bound {n : ℕ}
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (d : ℂ) (T : Config n → ℂ) (r R ε L : ℝ)
    (hR : 0≤R) (hε : 0≤ε) (hL : 0≤L) (hRr : R<r) (hd : ‖d‖<r)
    (hT : ∀ v ∈ closedBall 0 R, ‖T v‖<r)
    (hTL : ∀ v ∈ closedBall 0 R, ∀ w ∈ closedBall 0 R, ‖T v-T w‖≤‖v-w‖)
    (hs : ∀ p : ScalarTriple, ‖p‖<r → ‖Complex.sqrt (phaseEnergy B phi hphi p.2.1 p.1 p.2.2)-1‖≤ε)
    (hl : ∀ p q : ScalarTriple, ‖p‖<r → ‖q‖<r →
      ‖Complex.sqrt (phaseEnergy B phi hphi p.2.1 p.1 p.2.2)-
        Complex.sqrt (phaseEnergy B phi hphi q.2.1 q.1 q.2.2)‖≤L*‖p-q‖)
    (v : Config n) (hv : v∈closedBall 0 R) (w : Config n) (hw : w∈closedBall 0 R) :
    ‖(phaseSeparableMap B phi hphi d (T v) v-v)-
      (phaseSeparableMap B phi hphi d (T w) w-w)‖≤(ε+R*L)*‖v-w‖ := by
  have hwR : ‖w‖≤R := by simpa using hw
  have hp (x : Config n) (hx : x∈closedBall 0 R) (i : Fin n) : ‖(T x,(d,x i))‖<r := by
    have hxR : ‖x‖≤R := by simpa using hx
    exact max_lt (hT x hx) (max_lt hd ((norm_le_pi_norm x i).trans hxR |>.trans_lt hRr))
  apply coordinateProduct_error_bound
    (fun x i => Complex.sqrt (phaseEnergy B phi hphi d (T x) (x i))) R ε L hR hε hL v w hwR
  · intro i
    exact hs (T v,(d,v i)) (hp v hv i)
  · intro i
    have hdist : ‖(T v,(d,v i))-(T w,(d,w i))‖≤‖v-w‖ := by
      change max ‖T v-T w‖ (max ‖d-d‖ ‖v i-w i‖)≤‖v-w‖
      simp only [sub_self,norm_zero,max_eq_right (norm_nonneg _)]
      exact max_le (hTL v hv w hw) (norm_le_pi_norm (v-w) i)
    exact (hl (T v,(d,v i)) (T w,(d,w i)) (hp v hv i) (hp w hw i)).trans (mul_le_mul_of_nonneg_left hdist hL)

end
end IsingBulk.Anisotropic.NegativeNormalForm
