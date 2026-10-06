import IsingBulk.Tail.CompactSectorWindowBounds

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Literal named-current all-right sector. The same summable particle
majorant controls every lambda in the small-current interval. -/
theorem current_compact_sector_window_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta < eta0 →
      ∃ alpha0 tau0 : ℝ, 0 < alpha0 ∧ 0 < tau0 ∧ ∀ alpha tau : ℝ,
        0 < alpha → alpha < alpha0 → 0 < tau → tau < tau0 → tau ≤ 1 →
        ∀ (outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner), inner < 2*(1-Real.cos d.thetaB) →
        ∀ (J : ℕ) (D β : ℝ), 0 ≤ D → 0 < β →
        ∃ S : ℕ → ℝ, (∀ N, 0 ≤ S N) ∧ Summable (fun N => compactSectorMultiplicity N*S N) ∧
          ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, (n+1:ℕ) ≤ D*Real.sqrt H → 2*J+1 ≤ (n+1)*n →
            ∀ lam : ℝ, 0 ≤ lam → lam ≤ Real.exp (-β*H) →
            ∀ qS q : Fin (n+1), ∀ sigma : Fin (n+1) → Fin 3, (∀ i, sigma i=1) →
            ‖iteratedDeriv J (currentSectorIntegral (n+1) (constructedSelector d.thetaB eta alpha)
              (Real.exp (-d.c₀*Real.exp (-H))) tau lam qS d.thetaB outer inner ho hi (some (q,sigma)))
                (radialParameter d.theta (Real.exp (-H)))‖ ≤ S (n+1)*(H+1)^2 := by
  obtain ⟨eta0,he0,hgauss⟩ := current_compact_sector_gaussian_jets_uniform d hcsmall
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,tau0,ha0,ht0,hgauss⟩ := hgauss eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,tau0,ha0,ht0,?_⟩
  intro alpha tau ha haL ht htL ht1
  obtain ⟨c,e,κ,hc,heps,hκ,hgauss⟩ := hgauss alpha tau ha haL ht htL ht1
  intro outer inner ho hi his J D β hD hβ
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  have hp1 : ∀ x, f.p x ≤ 1 := fun x => (thresholdStep_range _ _ _).2
  let R := rightSectorRadius d.thetaB inner
  have hRπ : R < Real.pi := (right_sector_radius_bounds d.thetaB_pos d.thetaB_lt hi his).2.trans d.thetaB_lt
  have hmargin := compact_right_strict_margin d hi his
  obtain ⟨δf,Cf,hδf,hCf,hfar⟩ := hgauss (-R) R hmargin outer inner ho hi J
  obtain ⟨δn,Cn,hδn,hCn,hnear⟩ := actual_compact_sector_collision_jets d f hf hp1 hmargin outer inner ho hi J
  obtain ⟨K,G,Q,hK,hG,hQ,hbound⟩ := actual_compact_full_integral_bound d hcsmall f hf hp1 hi his
    ht.le ht1 hD hβ J
  let T := max 1 (2*R)
  have hG0 : 0 ≤ G := by linarith
  have hT : 0 ≤ T := zero_le_one.trans (le_max_left _ _)
  have hCn0 : 0 ≤ Cn := by linarith
  have hCf0 : 0 ≤ Cf := by linarith
  obtain ⟨B,hB,hSumm⟩ := compactSourceMajorant_weighted_summable J K G T Q Cn Cf hK.le hG0 hT hQ.le hCn0 hCf0 hκ
    compactSectorMultiplicity_envelope
  let S := compactSourceMajorant J K G T Q Cn Cf κ B
  refine ⟨S,(fun N => compactSourceMajorant_nonneg J N hK.le hG0 hT hQ.le hCn0 hCf0),hSumm B le_rfl,?_⟩
  have hext : Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,Eventually.of_forall (fun H => Real.exp_pos (-H))⟩
  filter_upwards [hbound,hext.eventually (radial_source_eventually_damping d hcsmall),
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds heps),
    compact_radial_window_small d hD hβ (lt_min hδn hδf)] with H hbH hdom heH hsmall
  intro n hND hdeg lam hlam hlamB qS q sigma hsigma
  let P := orderedIndexPairs (Finset.univ : Finset (Fin (n+1)))
  have hcard : 2*P.card=(n+1)*n := compact_full_pair_count n
  let w := currentSectorAngularWeight f tau qS d.thetaB outer inner ho hi q sigma
  have hws := current_all_right_signed_support f tau d.thetaB outer inner ho hi qS q sigma hsigma
  have hw := (compactSignedWeight_smooth w (current_sector_smooth f hf tau d.thetaB outer inner ho hi qS q sigma) hRπ hws).1
  have hsmallL := hsmall (n+1) (Nat.succ_pos n) hND lam hlam hlamB
  have hnsmall := hsmallL.2.trans (min_le_left δn δf)
  have hfsmall := hsmallL.2.trans (min_le_right δn δf)
  have hρ : 0 < Real.exp (-B*(n+1:ℕ)) := Real.exp_pos _
  have hρ1 : Real.exp (-B*(n+1:ℕ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hh := mul_nonneg hB.le (Nat.cast_nonneg (n+1) (α := ℝ))
    nlinarith)
  have hh := hbH n hND lam hlam hlamB P (fun _ h => h) (by rw [hcard]; exact hdeg)
    (compactSignedWeight w) hw (compactSignedWeight_tsupport w hws)
    (2^(3*J)*Cn^(2*(n+1)^2+2*(n+1))*(n+1:ℕ)^(8*J))
    (Cf^(n+1)*(n+1:ℕ)^(6*J)*Real.exp (-κ*(n+1:ℕ)^2)) (Real.exp (-B*(n+1:ℕ)))
    (by positivity) (by positivity) hρ hρ1
    (fun θ hθ hd hd1 => compactSignedWeight_mul_jets w _ hRπ hws hd.le (by positivity) _ (fun _ =>
      (hnear (n+1) (Nat.succ_pos n) (Real.exp (-H)) tau lam (Real.exp_pos _) ht.le ht1 hlam hsmallL.1 _ hdom.2.2
        hnsmall θ (fun i => ⟨hθ.1 i,hθ.2 i⟩) q sigma P (fun _ h => h) _ hd hd1
          (fun _ h => compactAllowedDiameter_pair_le P θ h)).2 qS))
    (fun θ hθ => compactSignedWeight_mul_jets w _ hRπ hws zero_le_one (by positivity) _ (fun _ =>
      hfar (n+1) (Nat.succ_pos n) (Real.exp (-H)) lam (Real.exp_pos _) heH hlam hsmallL.1 _ hdom.2.2
        (by simp only [sub_self,norm_zero]; positivity) hfsmall θ (fun i => ⟨hθ.1 i,hθ.2 i⟩) qS q sigma))
  rw [current_sector_compact_integral_jets (Nat.succ_pos n) f hf hdom.1 hdom.2.1 ht.le hlam qS _ _ _ ho hi q sigma J hdom.2.2]
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
