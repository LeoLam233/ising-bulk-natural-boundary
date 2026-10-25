import IsingBulk.Joint.Negative.FamilyCoincidence
import IsingBulk.Anisotropic.NegativeNormalForm.UniformVandermondeLog

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open Set Metric Filter IsingBulk.First
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

/-- Actual complete inverse Vandermonde density has a single exact complex
logarithm with the growing-order energy bound, uniformly before n. -/
theorem compact_family_vandermonde_log (B : ℂ × E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈P,B (0,eta)≠0) (D : ℝ) (hD : 0≤D) :
    ∃ δ R r Cp K : ℝ, 0<δ ∧ 0<R ∧ 0<r ∧ 0<Cp ∧ 0<K ∧ δ≤R/2 ∧ 4*R≤r ∧
      ∀eta∈P,∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ → (n:ℝ)*‖d‖≤D →
      ∃ P : UniformProjectedWitness (familyMember B eta) phi hphi n d r Cp,
      ∃ J : UniformCorrectionWitness (familyMember B eta) phi hphi n d r Cp P R,
      ∀ y : Config n, ‖y‖<δ → ZeroMean y →
      Complex.exp (2*actualPairLog (fun z => P.V (J.W z)) y)=
        actualPairMultiplier (fun z => P.V (J.W z)) y^2 ∧
      ‖2*actualPairLog (fun z => P.V (J.W z)) y‖≤
        K*(Real.sqrt ((n:ℝ)*absoluteEnergy y)+(n:ℝ)*absoluteEnergy y) := by
  obtain ⟨δ,R,r,Cp,K,hδ,hR,hr,hCp,hK,hδR,hRr,hex⟩ :=
    compact_family_refined_coincidence B phi hphi hP hB hBn
  refine ⟨δ,R,r,Cp,16*K*(Cp+3+D),hδ,hR,hr,hCp,by positivity,hδR,hRr,?_⟩
  intro eta heta n hn d hd hdD
  obtain ⟨P,J,hpair⟩ := hex eta heta n hn d hd
  refine ⟨P,J,?_⟩
  let Phi : Config n → Config n := fun y => P.V (J.W y)
  have hRhalf : R≤r/2 := by linarith
  have hPa : AnalyticOnNhd ℂ Phi (ball 0 δ) :=
    (J.corrected_bounds (familyMember B eta) phi hphi d r Cp R P hr hR hRhalf).1.mono (ball_subset_ball hδR)
  have hPeq : ∀ e y, Phi (permute e y)=permute e (Phi y) := by
    intro e y
    dsimp [Phi]
    rw [J.w_perm,P.v_perm]
  have hPL : LipschitzOnWith (3/32) (fun y => Phi y-y) (closedBall 0 δ) :=
    (J.corrected_perturbation_lipschitz (familyMember B eta) phi hphi d r Cp R P hRhalf).mono (closedBall_subset_closedBall hδR)
  intro y hy hmy
  have hclose (i j : Fin n) (hij : i≠j) : ‖coincidenceFactor Phi i j y-1‖≤1/2 :=
    (coincidenceFactor_uniform_close Phi δ hPa hPeq (3/32) hPL i j hij y hy).trans (by norm_num)
  have hnz (i j : Fin n) (hij : i≠j) : coincidenceFactor Phi i j y≠0 := by
    intro hz
    have h := hclose i j hij
    rw [hz,zero_sub,norm_neg,norm_one] at h
    norm_num at h
  have hexp := actualPairLog_exp Phi y hnz
  constructor
  · rw [show (2:ℂ)*actualPairLog Phi y=actualPairLog Phi y+actualPairLog Phi y by ring,
      Complex.exp_add,hexp]
    ring
  · have hsum := pair_error_sum_bound_off_diagonal hn (Phi y)
      (fun i j => coincidenceFactor Phi i j y) K Cp ‖d‖ hK.le hCp.le (norm_nonneg d) (hpair y hy hmy)
    have hl := (actualPairLog_norm_bound Phi y hclose).trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
    have he := (J.corrected_energy_bounds hn (familyMember B eta) phi hphi d r Cp R P hRhalf y (hy.le.trans hδR) hmy).2
    have hq := absoluteEnergy_nonneg y
    have hqv : absoluteEnergy (Phi y)≤4*absoluteEnergy y := by
      have hh := absoluteEnergy_add_le (Phi y-y) y
      rw [sub_add_cancel] at hh
      change absoluteEnergy (Phi y-y)≤absoluteEnergy y/64 at he
      nlinarith
    have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hqv (Nat.cast_nonneg n))
    rw [show (n:ℝ)*(4*absoluteEnergy y)=4*((n:ℝ)*absoluteEnergy y) by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt (4:ℝ)=2 by norm_num] at hsqrt
    have hfirst : (Cp+3)*(n:ℝ)*absoluteEnergy (Phi y)≤4*(Cp+3)*(n:ℝ)*absoluteEnergy y := by
      have h := mul_le_mul_of_nonneg_left hqv (show 0≤(Cp+3)*(n:ℝ) by positivity)
      convert h using 1; ring
    have hsecond : 2*(n:ℝ)*‖d‖*Real.sqrt ((n:ℝ)*absoluteEnergy (Phi y))≤
        4*D*Real.sqrt ((n:ℝ)*absoluteEnergy y) := by
      have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdD (by norm_num : (0:ℝ)≤2))
        (Real.sqrt_nonneg ((n:ℝ)*absoluteEnergy (Phi y)))
      have h2 := mul_le_mul_of_nonneg_left hsqrt (show 0≤2*D by positivity)
      nlinarith
    have hlog : ‖actualPairLog Phi y‖≤8*K*((Cp+3)*(n:ℝ)*absoluteEnergy y+D*Real.sqrt ((n:ℝ)*absoluteEnergy y)) := by
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (show 0≤2*K by positivity)]
    change ‖(2:ℂ)*actualPairLog Phi y‖≤_
    rw [norm_mul,show ‖(2:ℂ)‖=2 by norm_num]
    have hfinal : (Cp+3)*(n:ℝ)*absoluteEnergy y+D*Real.sqrt ((n:ℝ)*absoluteEnergy y)≤
        (Cp+3+D)*(Real.sqrt ((n:ℝ)*absoluteEnergy y)+(n:ℝ)*absoluteEnergy y) := by
      nlinarith [mul_nonneg hD (mul_nonneg (Nat.cast_nonneg n) hq),
        mul_nonneg (show 0≤Cp+3 by positivity) (Real.sqrt_nonneg ((n:ℝ)*absoluteEnergy y))]
    have hh := mul_le_mul_of_nonneg_left hfinal (show 0≤16*K by positivity)
    nlinarith

end
end IsingBulk.Joint.Negative
