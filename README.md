# lean4-quicksort

**(Lean4Quicksort.)Benchmark.benchmark**  
Runs a number of tests on a number of shuffled Nats with a selected algorithm, returns runtimes  
Usage: benchmark [number of tests] [number of elements] [target sorting algorithm]  
  
**Notes**  
  
- Algorithm in Basic.lean is currently around 33% faster than Std implementation (Array.qsort)
- Precalculating arr.size for pivotsplitHelper in Basic.lean does not show any notable performance improvements (simplified by compiler?)  
- Rewrite using lo-hi ranges WIP, currently significantly slower than old implementation (Basic.lean)
- Use Array.swap or Array.set exclusively via [Dutch National Flag Problem](https://en.wikipedia.org/wiki/Dutch_national_flag_problem)
- Use true recursion on smaller returned stack from split
