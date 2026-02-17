# zkLean

zkLean is a domain specific language (DSL) in Lean for specifying and verify zero-knowledge statements.
It is developed by [Galois, Inc](https://www.galois.com/) and originally lived in [this repository](https://github.com/GaloisInc/zkLean).

# Development

To compile the zkLean library, run the following in the `zkLean` directory:
```
lake build
```

There are also examples in the `example` directory.
These can be compiled by running `lake build` in the `example` directory.

The [`CircuitSoundness`](./examples/CircuitSoundness.lean) example shows a trivial circuit that constrains three field elements to be equal.
The theorem `constrainEq3.soundness` proves soundness of the `constrainEq3` circuit compositionally by relying on the `constrainEq2.soundness` theorem.
zkLean is compatible with Lean's Std.Do notation.
This allows users to write specifications about circuits using standard Hoare triples.
For example, the `constrainEq3.soundness` statement is as follows:
```
⦃ λ _s => ⌜True⌝ ⦄
constrainEq3 a b c
⦃ ⇓? _r _s => ⌜a.eval = c.eval⌝ ⦄
```
The first line indicates the precondition for the `constrainEq3`.
Since the precondition is `True`, there are no requirements when calling `constrainEq3`.
The postcondition states the required specification that the circuit `constrainEq3` must ensure that `a` and `c` are equal.
One of the benefits of using Lean's builtin Std.Do is that users can use tactics like `mspec` to compositionally write proofs.

A more involved example circuit is the SHA-3 circuit.
The specification is in the [`Sha3.Spec`](./examples/zkLeanExamples/Sha3/Spec.lean) module and simply is a Lean implementation of SHA-3. 
The circuit implementation of SHA-3 lives in [`Sha3.Circuit`](./examples/zkLeanExamples/Sha3/Circuit.lean) and its submodules, while the proof lives in [`Sha3.Proof`](./examples/zkLeanExamples/Sha3/Proof.lean).
Note that the circuits and proofs for the binary operations (and, xor, shift) currently live in another fork and will be merged in the future.

# Defining circuits

To build ZK circuits in zkLean, you should use the combinators provided in the [`Builder`](./zkLean/zkLean/Builder.lean) module.
Combinators are provided for most ZK primitives including equality constraints, R1CS constraints, lookup tables, MLE based lookup tables, and even RAM operations.

If you want to run a circuit given private input witnesses, you can use the `semantics` function in the [`Semantics`](./zkLean/zkLean/Semantics.lean) module.
It will return a boolean indicating whether or not the circuit's constraints are satisfied by the witness.

# Integration

Oftentimes users will want to verify properties about circuits written in other systems.
One option for doing so is to define a custom extraction from the tool into zkLean.
For example, Galois developed [an extractor](https://github.com/a16z/jolt/tree/main/zklean-extractor) for the Jolt zkVM that converts all of the frontend constraints in Jolt into a zkLean circuit.

An alternative approach is to use [LLZK](https://github.com/project-llzk/llzk-lib/).
LLZK is an MLIR dialect for ZK circuits.
We have defined LLZK frontends and backends, which allow users to convert LLZK circuits to zkLean (or convert zkLean circuits to LLZK).
LLZK has integration with other circuit languages like Circom, so users can user LLZK to convert their Circom circuits into zkLean.

# Automation

Proofs about finite field ZK operations and their corresponding bitvector operations can be tedious and time consuming.
The `bvmod_eq` package provides tactics to help automate such proofs. 
The [`And`](./examples/zkLeanExamples/And.lean) example uses these tactics to proof that the MLE for bitwise and matches its corresponding bitvector operation.

# Limitations

The trusted computing base (TCB) for proofs about circuits in zkLean assumes that (1) zkLean's circuit semantics (defined in [`Semantics`](./zkLean/Semantics.lean)) are correct and (2) Lean's core typechecker is sound.
Furthermore, if users import circuits from other systems using tools like LLZK, the TCB includes the tools that import circuits into zkLean.

# Acknowledgements

Thank you to the Ethereum Foundation for providing a grant that funds the development of zkLean.

Contributors to zkLean include Valentin Robert, Benoit Razet, and James Parker at [Galois, Inc](https://www.galois.com/) and Elizaveta Pertseva at Stanford University.
