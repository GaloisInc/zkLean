#!/usr/bin/env python3
"""
lean_subtable_to_smt.py

Handles Lean files shaped like your examples:
  def NAME : Subtable ... N := subtableFromMLE (fun x => <arith expr on x[i]>)
  lemma ... (bv1 bv2 : BitVec B) (fv1 fv2 : Vector f B) : ... map_f_to_bv ... -> ... = (foutput = evalSubtable NAME (Vector.append fv1 fv2))

What this script does:
  - parses modulus if present (abbrev ffff0 := <big nat> or abbrev FF0 := ZMod <big nat>)
  - parses bitwidth B from BVModEq.map_f_to_bv B
  - parses subtable size N from "Subtable ... N"
  - parses wiring hypotheses: fv1[j] / fv2[j] mapped to bv1[k] or bv2[k]
  - emits SMT:
      - FiniteField sort
      - declares bv1, bv2, bvoutput : (_ BitVec B)
      - declares v0..v{N-1} : FF (these correspond to x[0..N-1])
      - sets vK = ite(extract ...) one zero according to wiring
      - bitness: vK = vK*vK
      - defines SUBTABLE_FF_N(v{N-1} .. v0) = translated arithmetic expr
      - asserts foutput = SUBTABLE_FF_N(...)
      - asserts bvoutput = ??? (optional; we keep a placeholder and also extract out bits)
      - asserts (not (= foutput weighted_sum(out bits))) like your OR file

You can tweak the bvoutput assertion depending on your lemma (bvor vs bool_to_bv vs something else).
"""

from __future__ import annotations
import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple, Optional


# -------------------------
# Basic parsing
# -------------------------

def strip_comments(s: str) -> str:
    return re.sub(r"--.*?$", "", s, flags=re.MULTILINE)


def find_modulus(text: str) -> Optional[int]:
    m = re.search(r"\babbrev\s+fffff?0\s*:=\s*(\d+)", text)
    if m: return int(m.group(1))
    m = re.search(r"\babbrev\s+FF0\s*:=\s*ZMod\s+(\d+)", text)
    if m: return int(m.group(1))
    # many of your ZKField files are polymorphic and won't have a concrete modulus
    return None


# def find_bitwidth(text: str) -> int:
#     m = re.search(r"BVModEq\.map_f_to_bv\s+(\d+)", text)
#     if m: return int(m.group(1))
#     m = re.search(r":\s*BitVec\s+(\d+)", text)
#     if m: return int(m.group(1))
#     raise ValueError("Could not find bitwidth B (expected BVModEq.map_f_to_bv B or BitVec B).")

def find_input_bitwidth_from_binders(text: str) -> int:
    """
    Find the BitVec width of bv1/bv2 from the lemma binder: (bv1 bv2 : BitVec 8)
    """
    i = text.find("lemma")
    if i == -1:
        raise ValueError("No 'lemma' found in file")
    scan = text[i:i+20000]
    m = re.search(r"\(\s*[A-Za-z0-9_\s]+\s*:\s*BitVec\s+(\d+)\s*\)", scan, flags=re.DOTALL)
    if m:
        return int(m.group(1))
    raise ValueError("Could not find input BitVec width from lemma binders.")


def find_output_bitwidth_from_outmap(text: str) -> int:
    """
    Find output width from: some bvoutput = BVModEq.map_f_to_bv 16 foutput ->
    """
    m = re.search(r"\bsome\s+[A-Za-z0-9_]+\s*=\s*BVModEq\.map_f_to_bv\s+(\d+)\s+[A-Za-z0-9_]+\s*->", text)
    if m:
        return int(m.group(1))
    raise ValueError("Could not find output width from 'some bvoutput = BVModEq.map_f_to_bv W foutput ->'.")


def find_lemma_params(text: str) -> Tuple[List[str], List[str]]:
    """
    Find (bv1 bv2 : BitVec N) and (fv1 fv2 : Vector f N) binders robustly,
    by scanning starting at the first 'lemma' in the file.
    Returns ([bv1, bv2], [fv1, fv2]).
    """

    i = text.find("lemma")
    if i == -1:
        raise ValueError("No 'lemma' found in file")

    # Only scan a window after lemma to avoid matching other defs
    scan = text[i:i+20000]

    # Match binders like: (bv1 bv2 : BitVec 8)
    bv_binders = re.findall(
        r"\(\s*([A-Za-z0-9_\s]+?)\s*:\s*BitVec\s+(\d+)\s*\)",
        scan,
        flags=re.DOTALL,
    )

    # Match binders like: (fv1 fv2 : Vector f 8) or (fv1 fv2 : Vector FF0 8)
    fv_binders = re.findall(
        r"\(\s*([A-Za-z0-9_\s]+?)\s*:\s*Vector\s+[A-Za-z0-9_.]+\s+(\d+)\s*\)",
        scan,
        flags=re.DOTALL,
    )

    if not bv_binders or not fv_binders:
        raise ValueError(f"Could not find BitVec/Vector binders after lemma. bv={bv_binders}, fv={fv_binders}")

    bv_names_str, _bvN = bv_binders[0]
    fv_names_str, _fvN = fv_binders[0]

    bv_vars = bv_names_str.split()
    fv_vars = fv_names_str.split()

    if len(bv_vars) < 2 or len(fv_vars) < 2:
        raise ValueError(f"Expected ≥2 bv and ≥2 fv vars; got bv={bv_vars}, fv={fv_vars}")

    return bv_vars[:2], fv_vars[:2]


def find_out_names(text: str) -> Tuple[str, str]:
    m = re.search(r"\bsome\s+([a-zA-Z0-9_]+)\s*=\s*BVModEq\.map_f_to_bv\s+\d+\s+([a-zA-Z0-9_]+)\s*->", text)
    if not m:
        raise ValueError("Could not find output names (expected 'some bvoutput = BVModEq.map_f_to_bv B foutput ->').")
    return m.group(1), m.group(2)


def parse_mappings(text: str) -> Dict[Tuple[str, int], Tuple[str, int]]:
    """
    Parses:
      some (BVModEq.bool_to_bv B bvX[bit]) = BVModEq.map_f_to_bv B fvY[idx] ->
    Returns map: (fvName, idx) -> (bvName, bit)
    """
    fv_to_bv: Dict[Tuple[str, int], Tuple[str, int]] = {}
    pat = re.compile(
        r"some\s*\(\s*BVModEq\.bool_to_bv\s+\d+\s+([a-zA-Z0-9_]+)\[(\d+)\]\s*\)\s*=\s*BVModEq\.map_f_to_bv\s+\d+\s+([a-zA-Z0-9_]+)\[(\d+)\]\s*->"
    )
    for m in pat.finditer(text):
        bv_name = m.group(1)
        bv_bit  = int(m.group(2))
        fv_name = m.group(3)
        fv_idx  = int(m.group(4))
        fv_to_bv[(fv_name, fv_idx)] = (bv_name, bv_bit)

    if not fv_to_bv:
        raise ValueError("No fv<->bv mapping hypotheses found.")
    return fv_to_bv


def find_subtable_def(text: str) -> Tuple[str, int, str]:
    """
    Finds:
      def NAME ... : Subtable ... N := subtableFromMLE (fun x => BODY)
    Returns (name, N, BODY_as_string)
    """
    m = re.search(
        r"\bdef\s+([A-Za-z0-9_]+)\b.*?:\s*Subtable\s+[A-Za-z0-9_.]+\s+(\d+)\s*:=\s*subtableFromMLE\s*\(\s*fun\s+x\s*=>",
        text,
        flags=re.DOTALL
    )
    if not m:
        raise ValueError("Could not find subtableFromMLE definition.")
    name = m.group(1)
    N = int(m.group(2))
    start = m.end()

    # balance parentheses until we close the subtableFromMLE '('
    open_pos = text.rfind("(", 0, m.start())
    if open_pos < 0:
        body = text[start:].split("\n", 1)[0].strip()
        return name, N, body

    i = start
    depth = 1
    out: List[str] = []
    while i < len(text) and depth > 0:
        c = text[i]
        if c == "(":
            depth += 1
            out.append(c)
        elif c == ")":
            depth -= 1
            if depth == 0:
                break
            out.append(c)
        else:
            out.append(c)
        i += 1
    body = "".join(out).strip()
    return name, N, body


# -------------------------
# Lean expr -> SMT(FiniteField) parser
# -------------------------

TOK_PAT = re.compile(r"""
    \s*(
        \d+                       |  # integer literal
        x\[\d+\]                  |  # x[123]
        \+|\-|\*|\(|\)            |  # operators / parens
        \S+                          # fallback (shouldn't happen)
    )
""", re.VERBOSE)

def tokenize(expr: str) -> List[str]:
    toks = [m.group(1) for m in TOK_PAT.finditer(expr)]
    # reject unknown garbage early
    for t in toks:
        if t in {"+", "-", "*", "(", ")"}: continue
        if re.fullmatch(r"\d+", t): continue
        if re.fullmatch(r"x\[\d+\]", t): continue
        raise ValueError(f"Unexpected token in subtable expr: {t}")
    return toks

class Parser:
    def __init__(self, toks: List[str], p_mod: int):
        self.toks = toks
        self.i = 0
        self.p = p_mod

    def peek(self) -> Optional[str]:
        return self.toks[self.i] if self.i < len(self.toks) else None

    def eat(self, t: str) -> None:
        if self.peek() != t:
            raise ValueError(f"Expected '{t}', got '{self.peek()}' at token index {self.i}")
        self.i += 1

    def parse(self) -> str:
        e = self.parse_addsub()
        if self.peek() is not None:
            raise ValueError(f"Trailing tokens starting at {self.peek()} (index {self.i})")
        return e

    # Grammar:
    #   addsub := mul (('+'|'-') mul)*
    #   mul    := atom ('*' atom)*
    #   atom   := INT | x[idx] | '(' addsub ')'

    def parse_addsub(self) -> str:
        left = self.parse_mul()
        while self.peek() in {"+", "-"}:
            op = self.peek()
            self.i += 1
            right = self.parse_mul()
            if op == "+":
                left = f"(ff.add {left} {right})"
            else:
                # left - right
                left = f"(ff.add {left} (ff.mul neg_one {right}))"
        return left

    def parse_mul(self) -> str:
        left = self.parse_atom()
        while self.peek() == "*":
            self.i += 1
            right = self.parse_atom()
            left = f"(ff.mul {left} {right})"
        return left

    def parse_atom(self) -> str:
        t = self.peek()
        if t is None:
            raise ValueError("Unexpected end of tokens in atom")
        if t == "(":
            self.i += 1
            e = self.parse_addsub()
            self.eat(")")
            return e
        if re.fullmatch(r"\d+", t):
            self.i += 1
            n = int(t)
            return f"#f{n}m{self.p}"
        if re.fullmatch(r"x\[\d+\]", t):
            self.i += 1
            idx = int(t[2:-1])
            return f"v{idx}"
        raise ValueError(f"Bad atom token: {t}")


def lean_expr_to_smt_ff(expr: str, p_mod: int) -> str:
    toks = tokenize(expr)
    return Parser(toks, p_mod).parse()


# -------------------------
# SMT emission
# -------------------------

@dataclass
class Job:
    in_path: Path
    modulus: int
    Bin: int      # input BitVec width (bv1/bv2) and fv vector length
    Bout: int     # output BitVec width (bvoutput)
    N: int
    subtable_name: str
    subtable_body: str
    bv1: str
    bv2: str
    bvout: str
    fv1: str
    fv2: str
    foutput: str
    fv_to_bv: Dict[Tuple[str, int], Tuple[str, int]]



def mk_job(text: str, path: Path) -> Job:
    text = strip_comments(text)
    p = find_modulus(text)
    if p is None:
        raise ValueError(
            "This file is polymorphic over [Field f] / [ZKField f] and has no concrete modulus.\n"
            "This script currently emits concrete FiniteField SMT; give me the modulus or specialize the file."
        )
    Bin = find_input_bitwidth_from_binders(text)
    Bout = find_output_bitwidth_from_outmap(text)
    (bv_names, fv_names) = find_lemma_params(text)
    (bvout, foutput) = find_out_names(text)
    fv_to_bv = parse_mappings(text)
    (subname, N, body) = find_subtable_def(text)
    return Job(
        in_path=path,
        modulus=p,
        Bin=Bin,
        Bout=Bout,
        N=N,
        subtable_name=subname,
        subtable_body=body,
        bv1=bv_names[0],
        bv2=bv_names[1],
        bvout=bvout,
        fv1=fv_names[0],
        fv2=fv_names[1],
        foutput=foutput,
        fv_to_bv=fv_to_bv,
    )


def emit_smt(job: Job) -> str:
    p = job.modulus
    Bin = job.Bin
    Bout = job.Bout
    N = job.N

    if N != 2 * Bin:
        # For your patterns, N is typically 2*B (append fv1 fv2)
        # If not, you can still proceed if your hypotheses cover all needed x[i].
        pass

    # Translate the subtable body generically
    body_smt = lean_expr_to_smt_ff(job.subtable_body, p)

    # wiring: v[idx] corresponds to:
    #   idx < B  -> fv1[idx]
    #   idx >= B -> fv2[idx-B]
    def wiring_for_v(idx: int) -> Tuple[str, int]:
        if idx < Bin:
            key = (job.fv1, idx)
        else:
            key = (job.fv2, idx - Bin)
        if key not in job.fv_to_bv:
            raise ValueError(f"Missing wiring for appended vector element {key}")
        return job.fv_to_bv[key]

    lines: List[str] = []
    lines += [
        "(set-logic ALL)",
        "(set-option :produce-models true)",
        f"(define-sort FF () (_ FiniteField {p}))",
        "(declare-fun one () FF)",
        "(declare-fun zero () FF)",
        "(declare-fun neg_one () FF)",
        f"(assert (= one #f1m{p}))",
        f"(assert (= zero #f0m{p}))",
        f"(assert (= neg_one #f{p-1}m{p}))",
        "",
        f"(declare-fun {job.bv1} () (_ BitVec {Bin}))",
        f"(declare-fun {job.bv2} () (_ BitVec {Bin}))",
        f"(declare-fun {job.bvout} () (_ BitVec {Bout}))",
        "",
    ]

    # v0..v{N-1}
    for i in range(N):
        lines.append(f"(declare-fun v{i} () FF)")
    lines.append("")
    lines.append(f"(declare-fun {job.foutput} () FF)")
    lines.append("")

    # Wiring constraints v[i] = ite(extract bit bit) one zero
    lines.append(";; BV → FF wiring (from hypotheses)")
    for i in range(N):
        (bvn, bit) = wiring_for_v(i)
        lines.append(f"(assert (= v{i} (ite (= ((_ extract {bit} {bit}) {bvn}) #b1) one zero)))")
    lines.append("")

    # bitness constraints
    lines.append(";; bitness constraints for all v[i]")
    for i in range(N):
        lines.append(f"(assert (= v{i} (ff.mul v{i} v{i})))")
    lines.append("")

    # Define the subtable function: take args in reverse order like your sample is fine (not required)
    fun_name = f"{job.subtable_name}_FF"
    sig = " ".join([f"(v{idx} FF)" for idx in range(N-1, -1, -1)])
    args = " ".join([f"v{idx}" for idx in range(N-1, -1, -1)])
    lines.append(f"(define-fun {fun_name} ({sig}) FF")
    lines.append(f"  {body_smt}")
    lines.append(")")
    lines.append("")
    lines.append(f"(assert (= {job.foutput} ({fun_name} {args})))")
    lines.append("")

    # OPTIONAL: bvoutput relation.
    # For OR you'd want: (assert (= bvoutput (bvor bv1 bv2)))
    # For LTE you'd want: (assert (= bvoutput (ite (bvule bv1 bv2) (_ bv1 B) (_ bv0 B)))) etc.
    # Since your lemma says: bvoutput = bool_to_bv 32 (bv1 <= bv2)
    # I'll encode "bool_to_bv" as 0/1 bitvector:
    lines.append(";; bvoutput = bool_to_bv (bvule bv1 bv2)  (encoded as 0/1 BV)")
    lines.append(f"(assert (= {job.bvout}")

    lines.append(";; TODO(BV-ENCODING):")
    lines.append("")

    # If you still want the same "negated decomposition" style:
    # Extract out bits -> FF out_i and assert not(equal weighted sum)
    for i in range(Bout):
        lines.append(f"(declare-fun out{i} () FF)")
    lines.append("")
    lines.append(";; output bits from bvoutput")
    for i in range(Bout):
        bit = Bout - 1 - i  # out0 is MSB
        lines.append(f"(assert (= out{i} (ite (= ((_ extract {bit} {bit}) {job.bvout}) #b1) one zero)))")
    lines.append("")
    lines.append(";; bitness for output bits")
    for i in range(Bout):
        lines.append(f"(assert (= out{i} (ff.mul out{i} out{i})))")
    lines.append("")

    # weighted sum: Σ 2^(B-1-i)*out[i]
    def ff_lit(n: int) -> str:
        return f"#f{n}m{p}"
    weighted = []
    for i in range(Bout):
        w = 1 << (Bout - 1 - i)
        weighted.append(f"(ff.mul {ff_lit(w)} out{i})")
    weighted_sum = "(ff.add " + " ".join(weighted) + ")" if len(weighted) > 1 else weighted[0]

    lines.append(";; negated bit-decomposition link (same pattern as your OR file)")
    lines.append(f"(assert (not (= {job.foutput} {weighted_sum})))")
    lines.append("")
    lines.append("(check-sat)")
    return "\n".join(lines)


def convert_file(inp: Path, outp: Path) -> None:
    text = inp.read_text(encoding="utf-8")
    job = mk_job(text, inp)
    smt = emit_smt(job)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(smt, encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", help="input .lean file OR directory")
    ap.add_argument("-o", "--output", help="output .smt2 (only if input is a file)")
    ap.add_argument("--outdir", default="smt_out", help="output dir (only if input is a directory)")
    ap.add_argument("--keep-going", action="store_true", help="keep converting even if some files fail")
    args = ap.parse_args()

    inp = Path(args.input)

    if inp.is_file():
        outdir = Path(args.outdir)
        outdir.mkdir(parents=True, exist_ok=True)

        # If user gave -o, use it; otherwise put <file>.smt2 inside outdir
        if args.output:
            outp = Path(args.output)
        else:
            outp = outdir / (inp.stem + ".smt2")

        convert_file(inp, outp)
        print(f"[OK] {inp} -> {outp}")
        return


    if inp.is_dir():
        outdir = Path(args.outdir)
        ok = 0
        fail = 0
        for p in sorted(inp.rglob("*.lean")):
            rel = p.relative_to(inp)
            outp = (outdir / rel).with_suffix(".smt2")
            try:
                convert_file(p, outp)
                ok += 1
                print(f"[OK]   {p} -> {outp}")
            except Exception as e:
                fail += 1
                print(f"[FAIL] {p}: {e}")
                if not args.keep_going:
                    raise
        print(f"\nDone. ok={ok} fail={fail} outdir={outdir}")
        return

    raise SystemExit(f"Not a file/dir: {inp}")



if __name__ == "__main__":
    main()

