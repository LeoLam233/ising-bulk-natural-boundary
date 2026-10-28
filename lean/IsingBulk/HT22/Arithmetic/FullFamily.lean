import IsingBulk.HT22.Arithmetic.PrimeDensity
import IsingBulk.HT22.Arithmetic.EndpointBranch
import IsingBulk.HT22.Arithmetic.SignedNickel

/-! Exact complete arithmetic input to the new F001 first/tail mechanism. -/
namespace IsingBulk.HT22.Arithmetic
noncomputable section
open IsingBulk.PrimeFamily

theorem f001_prime_family {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ}
    (ha : PrimeIndex p a) :
    angleRoot p a ∈ primeRootFamily ∧
    (0<angle p a ∧ angle p a<Real.pi) ∧
    2*Real.cos (angle p a)≠0 ∧
    ((p^2-1)/2)%4=0 ∧
    (Odd p ∧ NickelAt (angleRoot p a) p ∧
      ∀ n : ℕ, 0<n → n<p → ¬ NickelAt (angleRoot p a) n) ∧
    (∀ l m : ℤ, angleRoot p a+(angleRoot p a)⁻¹ =
      (Real.cos (angle p l):ℂ)+(Real.cos (angle p m):ℂ) →
      Real.cos (angle p l)=Real.cos (angle p a) ∧
      Real.cos (angle p m)=Real.cos (angle p a)) ∧
    IsAlgebraic ℚ (endpointBranch p a) ∧
    ¬ IsOfFinOrder (endpointBranch p a) ∧
    (∀ N : ℕ, 0<N → endpointBranch p a^N≠1 ∧ endpointBranch p a^N≠ -1) ∧
    (∀ t : ℝ, 0<t → t<Real.pi →
      Complex.exp ((t:ℂ)*Complex.I) ∈ closure primeRootFamily) := by
  exact ⟨⟨p,a,hp,hp5,ha,rfl⟩,primeIndex_angle_bounds hp.pos ha,
    primeRoot_level_ne_zero hp hp5 ha,prime_critical_order_mod_four hp hp5,
    primeRoot_first_order hp hp5 ha,primeRoot_unique_cosine_pair hp hp5 ha,
    (endpointBranch_algebraic_nonresonant hp hp5 ha).1,
    (endpointBranch_algebraic_nonresonant hp hp5 ha).2,
    endpointBranch_pow_ne_signs hp hp5 ha,
    fun _ ht htπ => primeRoot_family_dense_upper_arc ht htπ⟩

end
end IsingBulk.HT22.Arithmetic
