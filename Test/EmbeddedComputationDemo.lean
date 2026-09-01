import ProofScript

structure FibonacciRequest where
  n : Nat
deriving Lean.FromJson, Lean.ToJson

structure FibonacciResponse where
  n : Nat
  value : Nat
  sequence : Array Nat
deriving Lean.FromJson, Lean.ToJson

private def fibonacciPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
      let (current, next) := fibonacciPair n
      (next, current + next)

def fibonacci (n : Nat) : Nat :=
  (fibonacciPair n).1

def computeFibonacci (request : FibonacciRequest) : Except String FibonacciResponse := do
  if request.n > 40 then
    throw "n must not exceed 40"
  return {
    n := request.n
    value := fibonacci request.n
    sequence := (Array.range (request.n + 1)).map fibonacci
  }

@text r#"
= Interactive Fibonacci <interactive-fibonacci>

Move the slider to call a Lean function compiled to WebAssembly. The response
contains both the selected Fibonacci number and the complete prefix sequence.
Inputs above 40 demonstrate a structured Lean computation error.
"#

@computation {
  metadata := (title := "Lean/Wasm Fibonacci calculator", label := "fibonacci-calculator"),
  renderer := "proof-script/fibonacci-calculator-v1",
  function := computeFibonacci,
  payload := r#"
  {
    "contractVersion": "1.0.0",
    "defaultInput": {"n": 10},
    "controls": {
      "n": {"kind": "range", "min": 0, "max": 40, "step": 1}
    },
    "views": ["value", "sequence-bars", "timing"],
    "fallback": {
      "summary": "Choose n from 0 to 40 to compute Fibonacci numbers in Lean/Wasm."
    }
  }
  "#}

page_end
