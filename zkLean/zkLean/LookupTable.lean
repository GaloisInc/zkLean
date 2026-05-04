import zkLean.Interleaving

/-- Type for subtables, the building blocks to construct lookup tables.

A subtable is an `n`-variate function on the boolean hypercube returning a field value.
A key property of Jolt's subtables is that they can be written as multilinear extensions (MLE).
We model an MLE as simply a function that takes a vector of `n` field input and returns a field output;
the polynomial and multilinearity properties are not important at this point in the formalization.
-/
inductive Subtable (f: Type) (n: Nat) where
  | SubtableMLE (mle : Vector f n -> f) : Subtable f n

/-- Construct a `Subtable` from an MLE. -/
def subtableFromMLE {n: Nat} (mle : Vector f n -> f) : Subtable f n := Subtable.SubtableMLE mle


inductive Interleaving where
  | Interleaved
  | Concatenated

structure LookupTableMLE (f: Type) (n: Nat) where
  interleaving: Interleaving
  mle : Vector f n -> f



/-- Type for composed lookup tables

A `ComposedLookupTable` is a collection of subtables with a function to
combine the results of the subtables into a single output.
--/
inductive ComposedLookupTable
  (f: Type)
  (num_bits: Nat)
  (num_chunks: Nat) where
  | Table
    (num_subtables: Nat)
    (subtables: Vector (Subtable f num_bits × Fin num_chunks) num_subtables)
    (combine_lookups: Vector f num_subtables -> f) :
    ComposedLookupTable f num_bits num_chunks

/-- Function to make a `ComposedLookupTable` -/
def mkComposedLookupTable {num_bits:Nat} {num_subtables: Nat} {num_chunks: Nat}
  (subtables: Vector (Subtable f num_bits × Fin num_chunks) num_subtables)
  (combine_lookups: Vector f num_subtables -> f) :
  ComposedLookupTable f num_bits num_chunks :=
  ComposedLookupTable.Table num_subtables subtables combine_lookups


/-- Evaluation function defining the semantics of `Subtable` --/
def evalSubtable {f: Type} {num_bits: Nat} (subtable: Subtable f num_bits) (input: Vector f num_bits): f :=
  match subtable with
  | Subtable.SubtableMLE mle => mle input

/-- Evaluation function defining the semantics of `Subtable` --/
def evalLookupTableMLE (table: LookupTableMLE f (n + n)) (input1 input2: Vector f n): f :=
  match table.interleaving with
  | .Interleaved => table.mle (interleave input1 input2)
  | .Concatenated => table.mle (input1 ++ input2)

/--
  Evaluation function defining the semantics of `ComposedLookupTable`
  given an input that is partitioned into `c` chunks.

  It applies the indexed chunks to the corresponding subtables,
  and then it combines the lookups.

  This evaluation implements the Definition 2.6 of the Jolt paper
  `T[r] = g(T_1[r_1], ... , T_k[r_1], T_{k+1}[r_2], ... , T_2k[r_2], ... , T_{ α - (k + 1)}[r_c], ... , T_{α}[r_c])`
  With the difference that chunks do not come necessarily in order r_1, r_2, etc.
  but instead are determined by indices provided in `subtables`.
  It also aligns with Definition 2.1 of the "Verifying Jolt zkVM Lookup Semantics" article.
--/
def evalComposedLookupTable {f: Type}
  {num_bits: Nat}
  {num_chunks: Nat}
  (table: ComposedLookupTable f num_bits num_chunks)
  (input: Vector (Vector f num_bits) num_chunks)
  : f :=
  match table with
    | ComposedLookupTable.Table num_subtables subtables combine_lookups =>
      let l := Vector.map (fun (t, i) => evalSubtable t input[i]) subtables
      combine_lookups l
