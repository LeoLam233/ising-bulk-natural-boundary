import IsingBulk.HT22.Anchor.Definitions
import IsingBulk.HT22.Tail.BorderedNormalization
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter Metric IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
theorem amplitude_ball_of_data (η C q₀ : ℝ)
    (hη : 0<η) (hC : 1≤C) (hq₀ : 0≤q₀) (hq₀1 : q₀<1) :
    ∃ c H : ℝ,0<c ∧ 0<H ∧ ∀ N : ℕ,0<N → ∀ σ : ℂ,‖σ‖=1 → ∀ s : ℂ,∀ q : Fin N → ℂ,
      ∀ anchor : Fin N,
      PreferredAnchorScalarBallData s q η C → PreferredAnchorPairBallData s q η C →
      (∀ i,AnalyticOnNhd ℂ (fun z : ℂ × ℂ => inverseGauge z.1 z.2) (closedBall (s,q i) η) ∧
        ∀ z∈closedBall (s,q i) η,‖inverseGauge z.1 z.2‖≤C) →
      ‖preferredRegularDiskRoot s (q anchor)‖≤q₀ →
      ∃ F : (ℂ × (Fin N → ℂ)) → ℂ,
        (fun z : ℂ × (Fin N → ℂ) => amplitude σ z.1 z.2) =ᶠ[𝓝 (s,q)] F ∧
        AnalyticOnNhd ℂ F (closedBall (s,q) (c/(N:ℝ))) ∧
        ∀ z∈closedBall (s,q) (c/(N:ℝ)),
          ‖F z‖≤H*(Real.sqrt (N+1:ℕ)*C^3)^(N+1)*C^N/(N.factorial:ℝ) := by
  classical
  obtain ⟨a,ha,hgap⟩ := preferred_anchor_product_relative_gap hq₀ hq₀1
  let c := min (η/4) (a*η/(4*C*C))
  let q₁ := (1+q₀)/2
  let H := 2/(1-q₁)
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hc : 0<c := lt_min (by positivity) (by positivity)
  have hq₁ : 0≤q₁ := by dsimp [q₁]; positivity
  have hq₁1 : q₁<1 := by dsimp [q₁]; linarith
  have hH : 0<H := div_pos (by norm_num) (sub_pos.mpr hq₁1)
  refine ⟨c,H,hc,hH,?_⟩
  intro N hN σ hσ s q anchor hscalar hpair hgauge hanchor
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hr : 0<c/(N:ℝ) := div_pos hc hNr
  have hrη : c/(N:ℝ)≤η/4 := (div_le_self hc.le hN1).trans (min_le_left _ _)
  choose G hGeq hGa hGb using hpair
  let Z : (ℂ × (Fin N → ℂ)) → ℂ := fun z => ∏ i,preferredRegularDiskRoot z.1 (z.2 i)
  let K : (ℂ × (Fin N → ℂ)) → Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
    fun z => Algebra.ghostBorder (fun i j => inverseGauge z.1 (z.2 i)*inverseGauge z.1 (z.2 j)*
      G i j (z.1,z.2 i,z.2 j)) (fun _ => 1)
  let A : (ℂ × (Fin N → ℂ)) → ℂ := fun z => ∏ i,preferredOneBodyExtension z.1 (z.2 i)
  let F : (ℂ × (Fin N → ℂ)) → ℂ := fun z =>
    ((1+σ*Z z)/(1-σ*Z z))*(K z).det*A z/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))
  have hproj {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) (i : Fin N) :
      (z.1,z.2 i)∈closedBall (s,q i) (c/(N:ℝ)) := by
    rw [mem_closedBall,dist_eq_norm] at hz ⊢
    change ‖preferredOneProjection i z-preferredOneProjection i (s,q)‖≤c/(N:ℝ)
    rw [← map_sub]
    exact (preferredOneProjection_norm_le i _).trans hz
  have hpairproj {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) (i j : Fin N) :
      (z.1,z.2 i,z.2 j)∈closedBall (s,q i,q j) η := by
    rw [mem_closedBall,dist_eq_norm] at hz ⊢
    change ‖preferredPairProjection i j z-preferredPairProjection i j (s,q)‖≤η
    rw [← map_sub]
    exact (preferredPairProjection_norm_le i j _).trans (hz.trans (hrη.trans (by linarith)))
  have hscalarproj {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) (i : Fin N) :
      (z.1,z.2 i)∈closedBall (s,q i) η :=
    closedBall_subset_closedBall (hrη.trans (by linarith)) (hproj hz i)
  have hZbound {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) : ‖Z z‖≤q₁ := by
    apply hgap N hN (fun i => preferredRegularDiskRoot s (q i))
      (fun i => preferredRegularDiskRoot z.1 (z.2 i)) anchor
      (fun _ => Complex.exp_ne_zero _) (fun i => (hscalar i).2.2.2.2.2.2) hanchor
    intro i
    have hh := preferred_analytic_relative_movement
      (fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2) (s,q i) η C hη hCp.le
      (hscalar i).2.2.2.1 (hscalar i).2.2.2.2.1 (Complex.exp_ne_zero _)
      (hscalar i).2.2.2.2.2.1 (z.1,z.2 i)
      (closedBall_subset_closedBall hrη (hproj hz i))
    have hdist : ‖(z.1,z.2 i)-(s,q i)‖≤c/(N:ℝ) := by
      simpa only [mem_closedBall,dist_eq_norm] using hproj hz i
    calc
      _ ≤ (4*C*C/η)*(c/(N:ℝ)) := hh.trans (mul_le_mul_of_nonneg_left hdist (by positivity))
      _ ≤ (4*C*C/η)*((a*η/(4*C*C))/(N:ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (min_le_right _ _) hNr.le) (by positivity)
      _ = a/(N:ℝ) := by field_simp
  have hZne {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) : 1-σ*Z z≠0 := by
    intro he
    have hzz : σ*Z z=1 := (sub_eq_zero.mp he).symm
    have hh := hZbound hz
    have heq : ‖Z z‖=1 := by
      have := congrArg norm hzz
      simpa only [norm_mul,hσ,one_mul,norm_one] using this
    rw [heq] at hh
    linarith
  have hZana {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) : AnalyticAt ℂ Z z := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g := fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2)
      ((hscalar i).2.2.2.1 _ (hscalarproj hz i)) ((preferredOneProjection i).analyticAt z)
  have hKana {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) :
      AnalyticAt ℂ (fun z => (K z).det) z := by
    have hg (i : Fin N) : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => inverseGauge z.1 (z.2 i)) z :=
      AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
        (g := fun z : ℂ × ℂ => inverseGauge z.1 z.2) ((hgauge i).1 _ (hscalarproj hz i))
        ((preferredOneProjection i).analyticAt z)
    have hentry (i j : Fin (N+1)) : AnalyticAt ℂ (fun z => K z i j) z := by
      cases i using Fin.cases with
      | zero => cases j using Fin.cases <;> exact analyticAt_const
      | succ i =>
        cases j using Fin.cases with
        | zero => exact analyticAt_const
        | succ j =>
          exact ((hg i).mul (hg j)).mul (AnalyticAt.comp
            (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i,z.2 j))
            (g := G i j) (hGa i j _ (hpairproj hz i j)) ((preferredPairProjection i j).analyticAt z))
    simp only [Matrix.det_apply']
    exact Finset.univ.analyticAt_fun_sum (fun σ _ =>
      analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => hentry (σ i) i)))
  have hAana {z : ℂ × (Fin N → ℂ)} (hz : z∈closedBall (s,q) (c/(N:ℝ))) : AnalyticAt ℂ A z := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
      (g := fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2)
      ((hscalar i).2.1 _ (hscalarproj hz i)) ((preferredOneProjection i).analyticAt z)
  refine ⟨F,?_,?_,?_⟩
  · have hg : ∀ᶠ z : ℂ × (Fin N → ℂ) in 𝓝 (s,q),∀ i j,
        preferredRegularPair z.1 (z.2 i) (z.2 j)=G i j (z.1,z.2 i,z.2 j) := by
      apply eventually_all.mpr
      intro i
      apply eventually_all.mpr
      intro j
      have ht : Tendsto (fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i,z.2 j))
          (𝓝 (s,q)) (𝓝 (s,q i,q j)) :=
        (show Continuous (fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i,z.2 j)) by fun_prop).tendsto (s,q)
      exact ht.eventually (hGeq i j)
    have ha : ∀ᶠ z : ℂ × (Fin N → ℂ) in 𝓝 (s,q),∀ i,
        preferredRegularOneBody z.1 (z.2 i)=preferredOneBodyExtension z.1 (z.2 i) := by
      apply eventually_all.mpr
      intro i
      have ht : Tendsto (fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i))
          (𝓝 (s,q)) (𝓝 (s,q i)) :=
        (show Continuous (fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 i)) by fun_prop).tendsto (s,q)
      exact ht.eventually (hscalar i).1
    filter_upwards [hg,ha] with z hzg hza
    have hmat : borderedKernel z.1 z.2=K z := by
      unfold borderedKernel K
      congr 1
      funext i j
      rw [ordinaryPair_eq_gauged,hzg i j]
    simp only [amplitude,hmat,hza]
    rfl
  · intro z hz
    exact ((((analyticAt_const.add (analyticAt_const.mul (hZana hz))).div
      (analyticAt_const.sub (analyticAt_const.mul (hZana hz)))
      (hZne hz)).mul (hKana hz)).mul (hAana hz)).div_const
  · intro z hz
    have hres : ‖(1+σ*Z z)/(1-σ*Z z)‖≤H := by
      have hnum : ‖1+σ*Z z‖≤2 := by
        have hh := norm_add_le (1:ℂ) (σ*Z z)
        rw [norm_one,norm_mul,hσ,one_mul] at hh
        linarith [hZbound hz]
      have hden : 1-q₁≤‖1-σ*Z z‖ := by
        have hh := norm_sub_norm_le (1:ℂ) (σ*Z z)
        rw [norm_one,norm_mul,hσ,one_mul] at hh
        linarith [hZbound hz]
      rw [norm_div]
      exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left (by norm_num) (sub_pos.mpr hq₁1) hden)
    have hC3 : 1≤C^3 := one_le_pow₀ hC
    have hentry (i j : Fin (N+1)) : ‖K z i j‖≤C^3 := by
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simp only [K,Algebra.ghostBorder_zero_zero,norm_zero]; positivity
        | succ j => simpa only [K,Algebra.ghostBorder_zero_succ,norm_one] using hC3
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa only [K,Algebra.ghostBorder_succ_zero,norm_neg,norm_one] using hC3
        | succ j =>
          simp only [K,Algebra.ghostBorder_succ_succ,norm_mul]
          calc
            _ ≤ C*C*C := mul_le_mul
              (mul_le_mul ((hgauge i).2 _ (hscalarproj hz i)) ((hgauge j).2 _ (hscalarproj hz j))
                (norm_nonneg _) hCp.le) (hGb i j _ (hpairproj hz i j))
              (norm_nonneg _) (mul_nonneg hCp.le hCp.le)
            _ = _ := by ring
    have hdet : ‖(K z).det‖≤(Real.sqrt (N+1:ℕ)*C^3)^(N+1) :=
      determinant_bound (by omega) (K z) (by positivity) hentry
    have hbody : ‖A z‖≤C^N := by
      rw [show A z=∏ i,preferredOneBodyExtension z.1 (z.2 i) from rfl,norm_prod]
      calc
        _ ≤ ∏ _i : Fin N,C := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => (hscalar i).2.2.1 _ (hscalarproj hz i))
        _ = _ := by simp
    have hnorm : ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))‖=
        (N.factorial:ℝ)*(2*Real.pi)^(N-1) := by
      simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_ofNat,abs_of_pos Real.pi_pos]
    have hfactor : (N.factorial:ℝ)≤(N.factorial:ℝ)*(2*Real.pi)^(N-1) :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith [Real.two_le_pi]))
    have hraw : ‖F z‖≤H*(Real.sqrt (N+1:ℕ)*C^3)^(N+1)*C^N/(N.factorial:ℝ) := by
      change ‖((1+σ*Z z)/(1-σ*Z z))*(K z).det*A z/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))‖≤_
      rw [norm_div,norm_mul,norm_mul,hnorm]
      calc
        _ ≤ (H*(Real.sqrt (N+1:ℕ)*C^3)^(N+1)*C^N)/((N.factorial:ℝ)*(2*Real.pi)^(N-1)) :=
          div_le_div_of_nonneg_right
            (mul_le_mul (mul_le_mul hres hdet (norm_nonneg _) hH.le) hbody (norm_nonneg _) (by positivity))
            (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hfactor
    exact hraw

end
end IsingBulk.HT22.Anchor
