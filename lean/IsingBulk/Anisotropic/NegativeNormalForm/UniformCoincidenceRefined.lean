import IsingBulk.Anisotropic.NegativeNormalForm.CollisionBoundExtension
import IsingBulk.Anisotropic.NegativeNormalForm.CorrectedPairUniform
import IsingBulk.Anisotropic.NegativeNormalForm.WitnessPairIdentity
import IsingBulk.Anisotropic.NegativeNormalForm.UniformDerivativeBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

/-- Refined coincidence-factor bounds for the actual constructed full inverse.
The common radius and constants are chosen before n, and the estimate includes
all collision hyperplanes in the zero-mean space. -/
theorem exists_uniform_refined_coincidence (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃ δ R r Cp K : ℝ, 0<δ ∧ 0<R ∧ 0<r ∧ 0<Cp ∧ 0<K ∧ δ≤R/2 ∧ 4*R≤r ∧
      ∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∃ P : UniformProjectedWitness B phi hphi n d r Cp,
      ∃ J : UniformCorrectionWitness B phi hphi n d r Cp P R,
      ∀ y : Config n, ‖y‖<δ → ZeroMean y → ∀ i j, i≠j →
      ‖coincidenceFactor (fun z => P.V (J.W z)) i j y-1‖≤
        K*((Cp+1)*absoluteEnergy (P.V (J.W y))/(n:ℝ)+
          ‖d‖*(‖P.V (J.W y) i‖+‖P.V (J.W y) j‖)+
          ‖P.V (J.W y) i‖^2+‖P.V (J.W y) j‖^2) := by
  obtain ⟨R,r,Cp,hR,hr,hCp,hRr,hex⟩ := exists_uniform_correction_witness B phi hphi hB hBn
  obtain ⟨rb,K,hrb,hK,hbound⟩ := correctedSeparablePairFactor_uniform B phi hphi hB hBn
  obtain ⟨ri,Li,hri,_hLi,hidentity⟩ := rootPair_uniform_bounds B phi hphi hB hBn
  let s := min rb ri
  have hs : 0<s := lt_min hrb hri
  have htau : ContinuousAt (fun d : ℂ => 1-Complex.cos d) 0 := by fun_prop
  have hetau : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<s/4 :=
    htau.norm.eventually_lt continuousAt_const (by simp; positivity)
  obtain ⟨η,hη,hηtau⟩ := Metric.eventually_nhds_iff.mp hetau
  let δ := min (R/4) (min (s/16) η)
  have hδ : 0<δ := lt_min (by positivity) (lt_min (by positivity) hη)
  have hδR : δ≤R/2 := by have h := min_le_left (R/4) (min (s/16) η); dsimp [δ]; linarith
  have hδs : δ≤s/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hδη : δ≤η := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,R,r,Cp,2*K,hδ,hR,hr,hCp,by positivity,hδR,hRr,?_⟩
  intro n hn d hd
  obtain ⟨P,⟨J⟩⟩ := hex n hn d (lt_of_lt_of_le hd (hδR.trans (by linarith)))
  refine ⟨P,J,?_⟩
  let Phi : Config n → Config n := fun y => P.V (J.W y)
  have hRhalf : R≤r/2 := by linarith
  have hPhi := J.corrected_bounds B phi hphi d r Cp R P hr hR hRhalf
  have hPa : AnalyticOnNhd ℂ Phi (ball 0 δ) := hPhi.1.mono (ball_subset_ball hδR)
  have hPeq : ∀ e y, Phi (permute e y)=permute e (Phi y) := by
    intro e y
    dsimp [Phi]
    rw [J.w_perm,P.v_perm]
  have hPL : LipschitzOnWith (3/32) (fun y => Phi y-y) (closedBall 0 δ) :=
    (J.corrected_perturbation_lipschitz B phi hphi d r Cp R P hRhalf).mono (closedBall_subset_closedBall hδR)
  have hsize (y : Config n) (hy : ‖y‖<δ) :
      ‖Phi y‖<s ∧ ‖P.T (Phi y)‖<s ∧ ‖Phi y‖<2*r ∧ (ZeroMean y → ZeroMean (Phi y)) := by
    have hyR := hy.le.trans hδR
    have hw := J.w_inverse y hyR
    have hv := P.v_inverse (J.W y) (hw.1.trans hRhalf)
    have hvnorm : ‖Phi y‖<s/4 := by
      have hh := (hPhi.2 y hyR).1
      dsimp [Phi] at *
      linarith
    have hvr : ‖Phi y‖<2*r := lt_of_le_of_lt hv.1 (by linarith)
    have hdiff := P.t_lip (Phi y) 0 hvr (by simpa using (show (0:ℝ)<2*r by positivity))
    rw [P.t_zero,sub_zero] at hdiff
    have hτ := hηtau (show dist d 0<η by simpa using hd.trans_le hδη)
    have htri := norm_add_le (P.T (Phi y)-(1-Complex.cos d)) (1-Complex.cos d)
    rw [sub_add_cancel] at htri
    refine ⟨by linarith,by linarith,hvr,?_⟩
    intro hmy
    exact (hv.2.2.2 (hw.2.2.2 hmy)).1
  intro y hy hmy i j hij
  let F : Config n → ℂ := fun z => correctedSeparablePairFactor B phi hphi (P.T (Phi z)) d (Phi z) i j
  let H : Config n → ℝ := fun z => K*((Cp+1)*absoluteEnergy (Phi z)/(n:ℝ)+
    ‖d‖*(‖Phi z i‖+‖Phi z j‖)+‖Phi z i‖^2+‖Phi z j‖^2)
  have hH : ContinuousOn H (ball 0 δ) := by
    intro z hz
    have hpc := (hPa z hz).continuousAt
    have hnreal : (n:ℝ)≠0 := by exact_mod_cast hn
    have hcoord (k : Fin n) : ContinuousAt (fun w => Phi w k) z :=
      (continuous_apply k).continuousAt.comp hpc
    apply ContinuousAt.continuousWithinAt
    dsimp [H]
    unfold absoluteEnergy
    fun_prop
  have hforward : ∀ z, ‖z‖<δ → ZeroMean z → (Phi z i-Phi z j)*F z=z i-z j := by
    intro z hz hzm
    obtain ⟨hv,ht,_hvr,_hm⟩ := hsize z hz
    have hsri : s≤ri := min_le_right _ _
    have hi := hidentity (P.T (Phi z)) d (Phi z i) (Phi z j) (ht.trans_le hsri)
      (lt_of_lt_of_le hd (by linarith))
      ((norm_le_pi_norm (Phi z) i).trans_lt (hv.trans_le hsri))
      ((norm_le_pi_norm (Phi z) j).trans_lt (hv.trans_le hsri))
    exact J.forward_pair_identity hn B phi hphi d r Cp R P hRhalf z (hz.le.trans hδR) hzm i j hi.1 hi.2.1
  have hFbound : ∀ z, ‖z‖<δ → ZeroMean z → ‖F z-1‖≤H z := by
    intro z hz hzm
    obtain ⟨hv,ht,hvr,hm⟩ := hsize z hz
    have hsrb : s≤rb := min_le_left _ _
    have hb := hbound n hn (P.T (Phi z)) d (Phi z) (ht.trans_le hsrb)
      (lt_of_lt_of_le hd (by linarith)) (hv.trans_le hsrb) (hm hzm) i j
    have hp := (P.t_pole (Phi z) hvr).2 (hm hzm)
    change ‖P.T (Phi z)-(1-Complex.cos d)‖≤Cp*(absoluteEnergy (Phi z)/(n:ℝ)) at hp
    apply hb.trans
    change K*_≤K*_
    apply mul_le_mul_of_nonneg_left _ hK.le
    simp only [div_eq_mul_inv] at hp ⊢
    nlinarith
  have h := coincidenceFactor_refined_from_forward Phi δ hPa hPeq (3/32) (by norm_num)
    hPL i j hij F H hH hforward hFbound y hy hmy
  convert h using 1
  dsimp [H,Phi]
  ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
