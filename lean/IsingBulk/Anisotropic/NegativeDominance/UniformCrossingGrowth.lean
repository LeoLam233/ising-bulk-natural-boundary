import IsingBulk.Anisotropic.NegativeDominance.PhysicalLowDominance

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

/-- Growth holds for every integer in the crossing interval, so the same
integer chosen for middle-model dominance may be used for all other ranges. -/
theorem physical_growth_on_crossing_range
    (B rootB : ℂ → ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ), rootB t^2=B t) (hphi : Real.sin phi≠0)
    (q : ℕ) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ n≥N, Odd n → ∀ j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) → (j : ℝ)≤upperCrossingOrder n →
      (j : ℝ)*(2*Real.log n-K)≤Real.log ‖physicalModel B rootB phi (n+2*q) j‖ := by
  obtain ⟨K,Ng,hg⟩ := physical_model_growth_bound B rootB phi 256 hB hB0 hroot hroot0 hsq hphi (by norm_num)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_crossing_scale 64 (max Ng (max 2 (4*q))))
  refine ⟨K,N,?_⟩
  intro n hn ho j hjL hjH
  obtain ⟨hnb,hlog,hu⟩ := hN n hn
  have hnG : Ng≤n := (le_max_left _ _).trans hnb
  have hn2 : 2≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hnb)
  have hnq : 4*q≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hnb)
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn2
  have hmR : ((n+2*q : ℕ) : ℝ)≤2*n := by exact_mod_cast (show n+2*q≤2*n by omega)
  have hmlo : (n : ℝ)≤((n+2*q : ℕ) : ℝ) := by exact_mod_cast (show n≤n+2*q by omega)
  have hloglo := Real.log_le_log (by positivity : (0 : ℝ)<n) hmlo
  have hloghi : Real.log ((n+2*q : ℕ) : ℝ)≤2*Real.log n := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ)<(n+2*q : ℕ)) hmR
    rw [Real.log_mul (by norm_num) (by positivity)] at hh
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have hr := crossing_order_range n (2*q) hn2 (by omega) ho hlog hu
  have hAj : alpha (n+2*q)<j := by
    have hA := alpha_mono (show n+2*q≤n+2*(2*q) by omega)
    have hh : (2*alpha (n+2*(2*q)) : ℝ)<j := lt_of_le_of_lt (by simpa using hr.1) hjL
    have hhN : 2*alpha (n+2*(2*q))<j := by exact_mod_cast hh
    omega
  have hjH' : j≤(n+2*q)^3 := by
    have hh := mul_le_mul_of_nonneg_left hu (sq_nonneg (n : ℝ))
    have hjn : j≤n^3 := by
      dsimp [upperCrossingOrder] at hjH
      exact_mod_cast (show (j : ℝ)≤(n : ℝ)^3 by nlinarith only [hh,hjH])
    exact hjn.trans (Nat.pow_le_pow_left (by omega) 3)
  have hbase : (n : ℝ)^2*Real.log n≤32*(j : ℝ) := by
    have hp : (4 : ℝ)≤(n : ℝ)^2 := by nlinarith only [hnR]
    have hl : 32≤(n : ℝ)^2*Real.log n := by nlinarith only [hp,hlog]
    dsimp [lowerCrossingOrder] at hjL
    linarith only [hjL,hl]
  have hscale : ((n+2*q : ℕ) : ℝ)^2*Real.log ((n+2*q : ℕ) : ℝ)≤256*(j : ℝ) := by
    have hs : ((n+2*q : ℕ) : ℝ)^2≤4*(n : ℝ)^2 := by nlinarith only [hmR,hmlo,hnR]
    have hh : ((n+2*q : ℕ) : ℝ)^2*Real.log ((n+2*q : ℕ) : ℝ)≤
        (4*(n : ℝ)^2)*(2*Real.log n) :=
      mul_le_mul hs hloghi (by linarith) (by positivity)
    push_cast at hh ⊢
    nlinarith only [hh,hbase]
  have hmOdd : Odd (n+2*q) := by obtain ⟨k,rfl⟩ := ho; exact ⟨k+q,by ring⟩
  have hh := hg (n+2*q) (by omega) hmOdd j hAj hjH' (by linarith) hscale
  apply le_trans _ hh
  gcongr

/-- Uniform low-range negligibility for every crossing-order witness, including
exactly the witness used by the full middle-model sum theorem. -/
theorem physical_low_on_crossing_range
    (B rootB : ℂ → ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ), rootB t^2=B t) (hphi : Real.sin phi≠0)
    (q : ℕ) {a D : ℝ} (ha : 0<a) (hD : 0<D) :
    ∃ N : ℕ, ∀ n≥N, Odd n → ∀ j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) → (j : ℝ)≤upperCrossingOrder n → n≤j →
      ∀ L : ℕ, (L : ℝ)≤Real.log j →
        D*(L : ℝ)^3*((L : ℝ)^3/a)^j ≤
          Real.exp (-(n : ℝ))*‖physicalModel B rootB phi (n+2*q) j‖ := by
  obtain ⟨K,Ng,hg⟩ := physical_growth_on_crossing_range B rootB phi hB hB0 hroot hroot0 hsq hphi q
  obtain ⟨Nl,hl⟩ := eventually_atTop.mp (logarithmic_low_envelope_vs_growth ha hD K)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_crossing_scale (|K|+1) (max Ng (max Nl 1)))
  refine ⟨N,?_⟩
  intro n hn ho j hjL hjH hnj L hL
  obtain ⟨hnb,hlog,hu⟩ := hN n hn
  have hnG : Ng≤n := (le_max_left _ _).trans hnb
  have hnL : Nl≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hnb)
  have hn1 : 1≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hnb)
  have hgrowth := hg n hnG ho j hjL hjH
  have hjH' : j≤n^3 := by
    have h := mul_le_mul_of_nonneg_left hu (sq_nonneg (n : ℝ))
    dsimp [upperCrossingOrder] at hjH
    exact_mod_cast (show (j : ℝ)≤(n : ℝ)^3 by nlinarith only [h,hjH])
  have hrate : 0<2*Real.log (n : ℝ)-K := by linarith [le_abs_self K,abs_nonneg K]
  have hjpos : (0 : ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have hP : 0<‖physicalModel B rootB phi (n+2*q) j‖ := by
    by_contra hh
    have he := le_antisymm (not_lt.mp hh) (norm_nonneg _)
    rw [he,Real.log_zero] at hgrowth
    exact (not_le_of_gt (mul_pos hjpos hrate)) hgrowth
  exact hl n hnL j hnj hjH' L hL _ hP hgrowth

end
end IsingBulk.Anisotropic.NegativeDominance
