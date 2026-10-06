import IsingBulk.Tail.CompactNormalizationJets
import IsingBulk.Tail.CompactCompletePairJets
import IsingBulk.Tail.CompactRegularDensity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def compactRegularPrefactor {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  let y := deformedPoint f r τ lam θ
  let z := fun i => globalRoot s (y i)
  mixedDensityNormalization f τ lam θ*
    ((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)*(∏ i,y i*residueFactor (z i))

theorem compactRegularDensity_prefactor {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    compactRegularDensity f r τ lam s θ=compactRegularPrefactor f r τ lam s θ*
      canceledPairProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))
        (deformedPoint f r τ lam θ) := by
  unfold compactRegularDensity compactRegularPrefactor
  ring

theorem actual_compact_prefactor_jets (d : LocalBranchData)
    (f : SelectorFunctions) (hf : RegularSelector f) (hp1 : ∀ x, f.p x ≤ 1) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1)
    (J : ℕ) : ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧
      ∀ N : ℕ, 0 < N → ∀ eps τ lam : ℝ, 0 < eps → 0 ≤ τ → τ ≤ 1 →
      0 ≤ lam → lam ≤ 1 → ∀ s : ℂ, s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
      ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ δ →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc a b) →
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
        compactRegularPrefactor f (Real.exp (-d.c₀*eps)) τ lam q.1 q.2)
        (s,θ) J 1 (C^N*(N:ℝ)^(3*J)) 0 := by
  obtain ⟨δ,B,hδ,hB,hscalar⟩ := actual_compact_regular_scalar_jets d f hf hp1 hmargin J
  obtain ⟨A,hA,hnorm⟩ := mixedDensityNormalization_joint_jets f hf J
  let C := 2^(2*J+1)*(A*B^2)
  have hbase : 1 ≤ (2:ℝ)^(2*J+1) := one_le_pow₀ (by norm_num)
  have hAB : 1 ≤ A*B^2 := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hB)
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le hbase hAB
  refine ⟨δ,C,hδ,hC,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 s hs hsmall θ hθ
  let r := Real.exp (-d.c₀*eps)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hprod (a : Fin 3) : RealScaledJetBound
      (fun q : ℂ × (Fin N → ℝ) => ∏ i,mixedCompactAmplitudeFactor a q.1 (deformedPoint f r τ lam q.2 i))
      (s,θ) J 1 (B^N*(N:ℝ)^J) 0 := by
    have hh := RealScaledJetBound.finset_prod Finset.univ
      (fun i _ => hscalar N hN eps τ lam heps.le hτ hτ1 hlam hlam1 s hsmall θ i i
        (hθ i) (hθ i) (Sum.inr a)) (zero_le_one.trans hB) zero_lt_one
    simpa only [Finset.card_univ,Fintype.card_fin,zero_mul,max_eq_right hN1,compactRegularScalar] using hh
  have hh := ((hnorm N hN τ lam hτ hτ1 hlam hlam1 (s,θ)).mul
    ((hprod 1).add (hprod 2)) zero_lt_one).mul (hprod 0) zero_lt_one
  simp only [zero_add] at hh
  have hcost : 2^J*(2^J*(A^N*(N:ℝ)^J)*(B^N*(N:ℝ)^J+B^N*(N:ℝ)^J))*(B^N*(N:ℝ)^J) ≤
      C^N*(N:ℝ)^(3*J) := by
    have hpow : (2:ℝ)^(2*J+1) ≤ ((2:ℝ)^(2*J+1))^N := le_self_pow₀ hbase (by omega : N ≠ 0)
    calc
      _ = 2^(2*J+1)*(A*B^2)^N*(N:ℝ)^(3*J) := by
        rw [show 2*J+1=J+J+1 by omega,show 3*J=J+J+J by omega]
        simp only [pow_add,pow_one,mul_pow,pow_two]
        ring
      _ ≤ ((2:ℝ)^(2*J+1))^N*(A*B^2)^N*(N:ℝ)^(3*J) := by gcongr
      _ = _ := by rw [← mul_pow]
  apply (hh.mono zero_lt_one le_rfl hcost).congr
  filter_upwards [compact_globalRoot_eventually_selected hN f hf hr hr1 hτ hlam
    (p := (s,θ)) ⟨hs,mem_univ _⟩] with q hq
  change mixedDensityNormalization f τ lam q.2*
    ((coordinateProduct (fun i => globalRoot q.1 (deformedPoint f r τ lam q.2 i)))⁻¹+
      (coordinateProduct (deformedPoint f r τ lam q.2))⁻¹)*
      (∏ i,deformedPoint f r τ lam q.2 i*residueFactor (globalRoot q.1 (deformedPoint f r τ lam q.2 i))) = _
  simp_rw [hq]
  simp only [mixedCompactAmplitudeFactor,Fin.reduceEq,ite_false,ite_true,Finset.prod_inv_distrib,coordinateProduct]

end
end IsingBulk.Tail
