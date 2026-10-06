import IsingBulk.Tail.AllBranchExteriorKernelRadialCost

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch

theorem allBranchExterior_inv_sqrt_le_inv {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (Real.sqrt a)⁻¹ ≤ a⁻¹ :=
  inv_anti₀ ha (Real.le_sqrt_of_sq_le (by nlinarith))

theorem allBranchExterior_positive_cost_scalar {d : LocalBranchData} (B : BranchEstimates d)
    (a D : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 < D) (hD1 : D ≤ 1)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    D^Q*allBranchExteriorPositiveCost B a D ≤
      ((B.original.C^2/min (B.original.k/4) (B.original.a/2))+
        (2*B.original.C^2/B.original.k)*Real.sqrt B.r)*a⁻¹*D^(Q-1) := by
  obtain ⟨P,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Q ≠ 0)
  let U := B.original.C^2/min (B.original.k/4) (B.original.a/2)
  let V := (2*B.original.C^2/B.original.k)*Real.sqrt B.r
  have hk := B.original.k_pos
  have hA := B.original.a_pos
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hi := allBranchExterior_inv_sqrt_le_inv ha ha1
  have hai : 1 ≤ a⁻¹ := (one_le_inv₀ ha).mpr ha1
  have hDai : D*(Real.sqrt a)⁻¹ ≤ a⁻¹ :=
    (mul_le_of_le_one_left (inv_nonneg.mpr (Real.sqrt_nonneg a)) hD1).trans hi
  have hnum : U*D*(Real.sqrt a)⁻¹+V ≤ (U+V)*a⁻¹ := by
    have h₁ := mul_le_mul_of_nonneg_left hDai hU
    have h₂ := le_mul_of_one_le_right hV hai
    nlinarith
  have he : D^(P+1)*allBranchExteriorPositiveCost B a D=
      (U*D*(Real.sqrt a)⁻¹+V)*D^P := by
    unfold allBranchExteriorPositiveCost
    dsimp [U,V]
    rw [pow_succ]
    field_simp
  rw [show P.succ=P+1 from rfl,he,Nat.add_sub_cancel]
  exact mul_le_mul_of_nonneg_right hnum (pow_nonneg hD.le P)

theorem allBranchExterior_negative_cost_scalar {d : LocalBranchData} (B : BranchEstimates d)
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : ℝ), 0 < a → a ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      allBranchExteriorNegativeCost B 1 1 a c C N ≤
        K*(N:ℝ)^2*(max 1 B.lengthC)^N*a⁻¹ := by
  let S := simpleKernelConstant*(1+|Real.log d.c₀|)
  let K₁ := (2*B.magnitudeUpper/c)*S
  let K₂ := (2*B.magnitudeUpper*C)*S*(2*Real.log 2)
  have hmag := B.magnitudeUpper_pos
  have hlen := B.lengthC_pos
  have hsk := simpleKernelConstant_pos
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂]; positivity
  refine ⟨K₁+K₂,add_nonneg hK₁ hK₂,?_⟩
  intro a ha ha1 N hN
  have hn : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hpow (k : ℕ) : B.lengthC^(N-k) ≤ (max 1 B.lengthC)^N :=
    (pow_le_pow_left₀ hlen.le (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le _ _))
  have hi := allBranchExterior_inv_sqrt_le_inv ha ha1
  have hsqrt := Real.sqrt_pos.mpr ha
  have he : 2*(B.magnitudeUpper/Real.sqrt a)/(c*Real.sqrt a)=(2*B.magnitudeUpper/c)*a⁻¹ := by
    have hs := Real.sq_sqrt ha.le
    field_simp
    nlinarith
  unfold allBranchExteriorNegativeCost
  simp only [mul_one,show (1:ℝ)+1=2 by norm_num,div_one]
  rw [he]
  calc
    _ ≤ ((2*B.magnitudeUpper/c)*a⁻¹)*
          (((N:ℝ)*simpleKernelConstant*(1+|Real.log d.c₀|))*(max 1 B.lengthC)^N)+
        (N:ℝ)*((2*(B.magnitudeUpper*a⁻¹)*C)*
          (((N:ℝ)*simpleKernelConstant*(1+|Real.log d.c₀|))*(2*Real.log 2)*(max 1 B.lengthC)^N)) := by
      simp only [div_eq_mul_inv]
      gcongr
      · exact hpow 1
      · exact hpow 2
    _ = (K₁*(N:ℝ)+K₂*(N:ℝ)^2)*(max 1 B.lengthC)^N*a⁻¹ := by dsimp [K₁,K₂,S]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr ha.le)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh := mul_le_mul_of_nonneg_left (show (N:ℝ) ≤ (N:ℝ)^2 by nlinarith) hK₁
      nlinarith

theorem allBranchExterior_near_kernel_cost_scalar {d : LocalBranchData} (B : BranchEstimates d)
    (ζ c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ a D : ℝ, 0 < a → a ≤ 1 → 0 < D → D ≤ 1 →
      ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q →
      allBranchExteriorNearKernelCost B 1 1 a D ζ c C N Q ≤
        K*(N:ℝ)^4*(max 1 B.lengthC)^N*a⁻¹*D^(Q-1) := by
  obtain ⟨Kn,hKn,hnegative⟩ := allBranchExterior_negative_cost_scalar B c C hc hC
  let T := (B.original.C^2/min (B.original.k/4) (B.original.a/2))+
    (2*B.original.C^2/B.original.k)*Real.sqrt B.r
  let Kp := 4*T*(simpleKernelConstant*(1+|Real.log d.c₀|))*(simpleKernelConstant*(1+|Real.log ζ|))
  have hk := B.original.k_pos
  have hA := B.original.a_pos
  have hsk := simpleKernelConstant_pos
  have hlen := B.lengthC_pos
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hKp : 0 ≤ Kp := by dsimp [Kp]; positivity
  refine ⟨1+Kp+Kn,by positivity,?_⟩
  intro a D ha ha1 hD hD1 N Q hN hQ
  have hn : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hlenN : B.lengthC^(N-2) ≤ (max 1 B.lengthC)^N :=
    (pow_le_pow_left₀ hlen.le (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le _ _))
  have hpos := allBranchExterior_positive_cost_scalar B a D ha ha1 hD hD1 Q hQ
  have hneg := hnegative a ha ha1 N hN
  have hDpow : D^Q ≤ D^(Q-1) := pow_le_pow_of_le_one hD.le hD1 (Nat.sub_le _ _)
  have hNpow : (N:ℝ)^2 ≤ (N:ℝ)^4 := pow_le_pow_right₀ hn (by norm_num)
  unfold allBranchExteriorNearKernelCost
  simp only [mul_one]
  calc
    _ ≤ 4*((N:ℝ)^2*((T*a⁻¹*D^(Q-1))*
          (((N:ℝ)*simpleKernelConstant*(1+|Real.log d.c₀|))*
            ((N:ℝ)*simpleKernelConstant*(1+|Real.log ζ|))*(max 1 B.lengthC)^N)))+
        D^Q*(Kn*(N:ℝ)^2*(max 1 B.lengthC)^N*a⁻¹) := by
      have hpc := allBranchExterior_positive_cost_nonneg B ha hD
      gcongr
    _ = Kp*(N:ℝ)^4*(max 1 B.lengthC)^N*a⁻¹*D^(Q-1)+
        Kn*(N:ℝ)^2*(max 1 B.lengthC)^N*a⁻¹*D^Q := by dsimp [Kp]; ring
    _ ≤ Kp*(N:ℝ)^4*(max 1 B.lengthC)^N*a⁻¹*D^(Q-1)+
        Kn*(N:ℝ)^4*(max 1 B.lengthC)^N*a⁻¹*D^(Q-1) := by gcongr
    _ ≤ _ := by
      have hfactor : 0 ≤ (N:ℝ)^4*(max 1 B.lengthC)^N*a⁻¹*D^(Q-1) := by positivity
      nlinarith

theorem allBranchExterior_near_kernel_cost_radial_scalar {d : LocalBranchData} (B : BranchEstimates d)
    (ζ c C : ℝ) (hζ : 0 < ζ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ R a D H : ℝ, 0 ≤ R → R ≤ 1 → 0 < a → a ≤ 1 →
      0 < D → D ≤ 1 → 0 ≤ H → ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q →
      allBranchExteriorNearKernelCost B (Real.exp (-H)) R a D ζ c C N Q ≤
        K*(N:ℝ)^4*(max 1 B.lengthC)^N*a⁻¹*D^(Q-1)*(H+1)^2 := by
  obtain ⟨K,hK,hscalar⟩ := allBranchExterior_near_kernel_cost_scalar B ζ c C hc hC
  have hT : 0 < allBranchExteriorRadialLogConstant := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold allBranchExteriorRadialLogConstant
    positivity
  refine ⟨allBranchExteriorRadialLogConstant*K,mul_pos hT hK,?_⟩
  intro R a D H hR hR1 ha ha1 hD hD1 hH N Q hN hQ
  apply (allBranchExterior_near_kernel_cost_radial B R a D ζ c C H N Q hR hR1 ha hD hζ hc hC hH).trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hscalar a D ha ha1 hD hD1 N Q hN hQ) hT.le) (sq_nonneg (H+1))
  exact hh.trans_eq (by ring)

end
end IsingBulk.Tail
