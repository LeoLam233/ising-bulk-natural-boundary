import IsingBulk.Tail.ActualCompactFullIntegral
import IsingBulk.Tail.UniformCompactGaussianJets
import IsingBulk.Tail.CompactSectorIntegralBridge
import IsingBulk.Tail.WeightedCompactSourceMajorant

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem compact_right_strict_margin (d : LocalBranchData) {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 2*(1-Real.cos d.thetaB)) :
    ∀ a ∈ Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ),
      |1+Real.cos d.thetaB-Real.cos a| < 1 := by
  have hS : 0 < 1+Real.cos d.thetaB := by
    have hh := Real.strictAntiOn_cos ⟨d.thetaB_pos.le,d.thetaB_lt.le⟩
      ⟨Real.pi_pos.le,le_rfl⟩ d.thetaB_lt
    simp only [Real.cos_pi] at hh
    linarith
  have hm : 0 < min (δ/2) ((1+Real.cos d.thetaB)/2) := lt_min (by positivity) (by positivity)
  intro a ha
  exact (right_sector_interval_uniform_margin d.thetaB_pos d.thetaB_lt hδ hδsmall a ha).trans_lt (by linarith)

theorem compact_radial_window_small (d : LocalBranchData) {D β δ : ℝ}
    (hD : 0 ≤ D) (hβ : 0 < β) (hδ : 0 < δ) :
    ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 0 < N → (N:ℝ) ≤ D*Real.sqrt H →
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      lam ≤ 1 ∧ ‖radialParameter d.theta (Real.exp (-H))-radialParameter d.theta 0‖+
        d.c₀*Real.exp (-H)+2*lam ≤ δ := by
  have hden : 0 < 3+d.c₀ := by have := d.c₀_pos; positivity
  filter_upwards [intermediate_window_current_small D β (δ/(3+d.c₀)) hD hβ (div_pos hδ hden),
    eventually_ge_atTop (0:ℝ)] with H hsmall hH
  intro N hN hND lam hlam hlamB
  refine ⟨hlamB.trans (Real.exp_le_one_iff.mpr (by nlinarith)),?_⟩
  rw [radialParameter_sub_zero_norm d.theta _ (Real.exp_pos _).le]
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hh := hsmall N hND lam hlam hlamB
  have he : Real.exp (-H)+lam ≤ (N:ℝ)*(Real.exp (-H)+lam) := le_mul_of_one_le_left (by positivity) hN1
  have hmul := (lt_div_iff₀ hden).mp (he.trans_lt hh)
  nlinarith [mul_nonneg d.c₀_pos.le hlam,Real.exp_pos (-H)]

theorem compact_full_pair_count (n : ℕ) :
    2*(orderedIndexPairs (Finset.univ : Finset (Fin (n+1)))).card=(n+1)*n := by
  rw [orderedIndexPairs_card,Finset.card_univ,Fintype.card_fin]
  have hh := Nat.cast_choose_two (K := ℝ) (n+1)
  have he : (2:ℝ)*((n+1).choose 2:ℝ)=((n+1:ℕ):ℝ)*(n:ℝ) := by
    push_cast at hh ⊢
    nlinarith
  exact_mod_cast he

/-- Literal original all-right sector, uniformly in the intermediate window.
The returned majorant includes enough summability for all finite sector counts. -/
theorem original_compact_sector_window_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 : ℝ, 0 < alpha0 ∧ ∀ alpha : ℝ, 0 < alpha → alpha < alpha0 →
      ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
      ∀ (J : ℕ) (τ D : ℝ), 0 ≤ τ → τ ≤ 1 → 0 ≤ D →
      ∃ S : ℕ → ℝ, (∀ N, 0 ≤ S N) ∧ Summable (fun N => compactSectorMultiplicity N*S N) ∧
        ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, (n+1:ℕ) ≤ D*Real.sqrt H → 2*J+1 ≤ (n+1)*n →
          ∀ q : Fin (n+1), ∀ sigma : Fin (n+1) → Fin 3, (∀ i, sigma i=1) →
          ‖iteratedDeriv J (originalSectorIntegral (n+1) (constructedSelector d.thetaB eta alpha)
            (Real.exp (-d.c₀*Real.exp (-H))) τ d.thetaB outer inner ho hi (some (q,sigma)))
              (radialParameter d.theta (Real.exp (-H)))‖ ≤ S (n+1)*(H+1)^2 := by
  obtain ⟨eta0,he0,hgauss⟩ := original_compact_sector_gaussian_jets_uniform d hcsmall
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,c,e,κ,ha0,hc,heps,hκ,hgauss⟩ := hgauss eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,ha0,?_⟩
  intro alpha ha haL outer inner ho hi his J τ D hτ hτ1 hD
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  have hp1 : ∀ x, f.p x ≤ 1 := fun x => (thresholdStep_range _ _ _).2
  let R := rightSectorRadius d.thetaB inner
  have hRπ : R < Real.pi := (right_sector_radius_bounds d.thetaB_pos d.thetaB_lt hi his).2.trans d.thetaB_lt
  have hmargin := compact_right_strict_margin d hi his
  obtain ⟨δf,Cf,hδf,hCf,hfar⟩ := hgauss alpha ha haL (-R) R hmargin outer inner ho hi J
  obtain ⟨δn,Cn,hδn,hCn,hnear⟩ := actual_compact_sector_collision_jets d f hf hp1 hmargin outer inner ho hi J
  obtain ⟨K,G,Q,hK,hG,hQ,hbound⟩ := actual_compact_full_integral_bound d hcsmall f hf hp1 hi his
    hτ hτ1 hD (show (0:ℝ)<1 by norm_num) J
  let T := max 1 (2*R)
  have hG0 : 0 ≤ G := by linarith
  have hT : 0 ≤ T := zero_le_one.trans (le_max_left _ _)
  have hCn0 : 0 ≤ Cn := by linarith
  have hCf0 : 0 ≤ Cf := by linarith
  obtain ⟨B,hB,hSumm⟩ := compactSourceMajorant_weighted_summable J K G T Q Cn Cf hK.le hG0 hT hQ.le hCn0 hCf0 hκ
    compactSectorMultiplicity_envelope
  let S := compactSourceMajorant J K G T Q Cn Cf κ B
  refine ⟨S,(fun N => compactSourceMajorant_nonneg J N hK.le hG0 hT hQ.le hCn0 hCf0),hSumm B le_rfl,?_⟩
  have ht : Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,Eventually.of_forall (fun H => Real.exp_pos (-H))⟩
  filter_upwards [hbound,ht.eventually (radial_source_eventually_damping d hcsmall),
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds heps),
    compact_radial_window_small d hD (show (0:ℝ)<1 by norm_num) (lt_min hδn hδf)]
    with H hbH hdom heH hsmall
  intro n hND hdeg q sigma hsigma
  let P := orderedIndexPairs (Finset.univ : Finset (Fin (n+1)))
  have hcard : 2*P.card=(n+1)*n := compact_full_pair_count n
  let w := originalSectorAngularWeight f d.thetaB outer inner ho hi q sigma
  have hws := original_all_right_signed_support f d.thetaB outer inner ho hi q sigma hsigma
  have hw := (compactSignedWeight_smooth w (original_sector_smooth f hf d.thetaB outer inner ho hi q sigma) hRπ hws).1
  have hsmall0 := (hsmall (n+1) (Nat.succ_pos n) hND 0 le_rfl (Real.exp_pos _).le).2
  have hnsmall : ‖radialParameter d.theta (Real.exp (-H))-radialParameter d.theta 0‖+d.c₀*Real.exp (-H)+2*0 ≤ δn :=
    hsmall0.trans (min_le_left _ _)
  have hfsmall : ‖radialParameter d.theta (Real.exp (-H))-radialParameter d.theta 0‖+d.c₀*Real.exp (-H) ≤ δf := by
    simpa only [mul_zero,add_zero] using hsmall0.trans (min_le_right _ _)
  have hρ : 0 < Real.exp (-B*(n+1:ℕ)) := Real.exp_pos _
  have hρ1 : Real.exp (-B*(n+1:ℕ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hh := mul_nonneg hB.le (Nat.cast_nonneg (n+1) (α := ℝ))
    nlinarith)
  have hh := hbH n hND 0 le_rfl (Real.exp_pos _).le P (fun _ h => h) (by rw [hcard]; exact hdeg)
    (compactSignedWeight w) hw (compactSignedWeight_tsupport w hws)
    (2^(3*J)*Cn^(2*(n+1)^2+2*(n+1))*(n+1:ℕ)^(8*J))
    (Cf^(n+1)*(n+1:ℕ)^(6*J)*Real.exp (-κ*(n+1:ℕ)^2)) (Real.exp (-B*(n+1:ℕ)))
    (by positivity) (by positivity) hρ hρ1
    (fun θ hθ hd hd1 => compactSignedWeight_mul_jets w _ hRπ hws hd.le (by positivity) _ (fun _ =>
      (hnear (n+1) (Nat.succ_pos n) (Real.exp (-H)) τ 0 (Real.exp_pos _) hτ hτ1 le_rfl zero_le_one _ hdom.2.2
        hnsmall θ (fun i => ⟨hθ.1 i,hθ.2 i⟩) q sigma P (fun _ h => h) _ hd hd1
          (fun _ h => compactAllowedDiameter_pair_le P θ h)).1))
    (fun θ hθ => compactSignedWeight_mul_jets w _ hRπ hws zero_le_one (by positivity) _ (fun _ =>
      hfar (n+1) (Nat.succ_pos n) (Real.exp (-H)) τ (Real.exp_pos _) heH hτ hτ1 _ hdom.2.2
        (by simp only [sub_self,norm_zero]; positivity) hfsmall θ (fun i => ⟨hθ.1 i,hθ.2 i⟩) q sigma))
  rw [original_sector_compact_integral_jets (Nat.succ_pos n) f hf hdom.1 hdom.2.1 hτ _ _ _ ho hi q sigma J hdom.2.2]
  apply hh.trans_eq
  dsimp only [S,compactSourceMajorant]
  rw [hcard]
  have hedeg : (n+1)*n-2*J-1=(n+1)*((n+1)-1)-(2*J+1) := by
    simp only [Nat.add_sub_cancel]
    omega
  rw [hedeg]
  ring

end
end IsingBulk.Tail
