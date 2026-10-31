import Architect
import PrimeGapsTheory.Endgame.Main
import BombieriVinogradov.Assembly.PrimeCountingConversion.Main

namespace MaynardTaoBoundedPrimeGaps

/-- The Maynard-Tao bounded prime gaps theorem: there is a finite bound `B` such that arbitrarily
large pairs of distinct primes differ by at most `B`.

The Bombieri–Vinogradov theorem supplies the distribution hypothesis of the Maynard sieve
endgame, which gives the bound 600. -/
@[blueprint "MaynardTaoBoundedPrimeGaps.MainTheorem"]
theorem MainTheorem :
    ∃ B : ℕ, 0 < B ∧
      ∀ N : ℕ, ∃ p q : ℕ,
        N ≤ p ∧ Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ q - p ≤ B := by
  refine ⟨600, by omega, ?_⟩
  intro N
  obtain ⟨p, q, hpN, hpq, hp, hq, hqbound⟩ :=
    bombieriVinogradov_implies_prime_gap_le_600
      BombieriVinogradov.PrimeCountingConversion.weighted_to_prime_counting N
  exact ⟨p, q, hpN, hp, hq, hpq, by omega⟩

end MaynardTaoBoundedPrimeGaps
