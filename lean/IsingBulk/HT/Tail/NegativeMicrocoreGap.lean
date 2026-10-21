import IsingBulk.Tail.MicrocoreGap
import IsingBulk.Tail.MicrocoreWindowGeometry

/-! Actual reflected microcore gaps. The plus Y-kernel is separated using
the proved resultant bound at 2N; the plus Z-kernel is uniformly regular. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Tail IsingBulk.Jets
open scoped BigOperators

theorem negative_algebraic_microcore_gap (b : ℝ)
    (halg : IsAlgebraic ℚ (Complex.exp (-(b:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ,1 ≤ N → Complex.exp (-(b:ℂ)*Complex.I)^N ≠ 1) :
    ∃ B : ℝ,0 < B ∧ ∀ N : ℕ,1 ≤ N → ∀ u : Fin N → ℝ,
      ∀ c ε radius : ℝ,0 ≤ c → 0 ≤ ε →
      (∀ i,|u i| ≤ radius) →
      (N:ℝ)*(c*ε+radius) ≤ Real.exp (-B*N)/2 →
      Real.exp (-B*N)/2 ≤ ‖1+∏ i,microcoreY c ε b (u i)‖ := by
  obtain ⟨A,hA,hgap⟩ := IsingBulk.Separation.exponential_separation halg hnot
  refine ⟨2*A+1,by linarith,?_⟩
  intro N hN u c ε radius hc hε hu hsmall
  let z := Complex.exp (-(b:ℂ)*Complex.I)^N
  have hNr : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hz : ‖z‖=1 := by
    dsimp [z]
    rw [norm_pow]
    have he : ‖Complex.exp (-(b:ℂ)*Complex.I)‖=1 := by
      rw [show -(b:ℂ)=((-b:ℝ):ℂ) by simp]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [he,one_pow]
  have hm : ‖1-z‖ ≤ 2 := by
    calc
      ‖1-z‖ ≤ ‖(1:ℂ)‖+‖z‖ := norm_sub_le (1:ℂ) z
      _ = 2 := by rw [norm_one,hz]; norm_num
  have hp : ‖1-z^2‖ ≤ 2*‖1+z‖ := by
    rw [show 1-z^2=(1-z)*(1+z) by ring,norm_mul]
    nlinarith [norm_nonneg (1+z)]
  have hg : Real.exp (-A*(2*N:ℕ)) ≤ 2*‖1+z‖ := by
    have ht := hgap (2*N) (by omega)
    have he : Complex.exp (-(b:ℂ)*Complex.I)^(2*N)=z^2 := by
      dsimp [z]
      rw [← pow_mul]
      congr 1
      omega
    rw [he] at ht
    exact ht.trans hp
  have he : Real.exp (-(2*A+1)*(N:ℝ))*Real.exp (N:ℝ)=Real.exp (-A*(2*N:ℕ)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have h2 : 2 ≤ Real.exp (N:ℝ) := by linarith [Real.add_one_le_exp (N:ℝ)]
  have hcenter : Real.exp (-(2*A+1)*(N:ℝ)) ≤ ‖1+z‖ := by
    have hpos := Real.exp_pos (-(2*A+1)*(N:ℝ))
    nlinarith
  have hpert := microcore_product_near_center N u c ε b radius hc hε hu
  have htri := norm_sub_le (1+∏ i,microcoreY c ε b (u i))
    ((∏ i,microcoreY c ε b (u i))-z)
  have hid : (1+∏ i,microcoreY c ε b (u i))-
      ((∏ i,microcoreY c ε b (u i))-z)=1+z := by ring
  rw [hid] at htri
  change ‖(∏ i,microcoreY c ε b (u i))-z‖ ≤ _ at hpert
  linarith

theorem negative_microcore_Z_gap {N : ℕ} (φ : Fin N → ℂ)
    (hsmall : (∑ i,‖φ i‖) ≤ 1/2) :
    (∑ i,‖φ i‖)/4 ≤ ‖1+regularZProduct (0:ℂ) φ‖ := by
  let w := -Complex.I*∑ i,φ i
  have hw : ‖w‖ ≤ ∑ i,‖φ i‖ := by
    calc
      ‖w‖ = ‖∑ i,φ i‖ := by simp [w]
      _ ≤ ∑ i,‖φ i‖ := norm_sum_le _ _
  have he := Complex.norm_exp_sub_one_le (x := w) (by linarith : ‖w‖ ≤ 1)
  have ht := norm_sub_le (1+Complex.exp w) (Complex.exp w-1)
  rw [show (1+Complex.exp w)-(Complex.exp w-1)=(2:ℂ) by ring] at ht
  norm_num at ht
  change (∑ i,‖φ i‖)/4 ≤ ‖1+Complex.exp w‖
  linarith

end
end IsingBulk.HT.Tail
