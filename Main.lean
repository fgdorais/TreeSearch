import TreeSearch.Concrete.Basic
import Reap

def main : IO Unit :=
  IO.println "Hello, world!"

def test {m n : Nat} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  reapMCTS
