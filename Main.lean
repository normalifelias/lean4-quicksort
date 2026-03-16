import Lean4Quicksort.Basic
import Lean4Quicksort.Benchmark

def main : IO Unit :=
  benchmark 10 100000 quicksort
