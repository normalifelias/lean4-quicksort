import Lean4Quicksort.Basic
import Lean4Quicksort.Benchmark

def main : IO Unit :=
  benchmark 10 1000000 quicksort
