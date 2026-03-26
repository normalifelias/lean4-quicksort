import Lean4Quicksort.Basic
import Lean4Quicksort.Benchmark
-- import Lean4Quicksort.HiLo

def main : IO Unit :=
  benchmark 10 1000000 quicksort
