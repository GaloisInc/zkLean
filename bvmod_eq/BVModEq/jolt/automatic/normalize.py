#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.resolve()

HEADER = """import BVModEq.TranslateAll
set_option maxRecDepth 1048576
set_option maxHeartbeats  20000000000000000000
set_option exponentiation.threshold 900
abbrev ffff0 := 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance : Fact (Nat.Prime ffff0) := by sorry
instance : Fact (NeZero ffff0) := by sorry
instance NotTwo: BVModEq.GtTwo (ffff0) := by sorry
abbrev FF0 := ZMod 52435875175126190479447740508185965837690552500527637822603658699938581184513
abbrev f := FF0
"""

def ensure_header(text: str) -> str:
    if re.search(r"(?m)^\s*import\s+BVModEq\.TranslateAll\s*$", text):
        return text
    return HEADER + "\n" + text.lstrip()

def normalize_global_helpers(text: str) -> str:
    # Fix stuck equals like "=map_f_to_bv_8"
    text = re.sub(r"=\s*(map_f_to_bv_\d+\b)", r"= \1", text)
    text = re.sub(r"=\s*(bool_to_bv_\d+\b)", r"= \1", text)
    return text

def infer_bitwidth_from_decl(block: str) -> int | None:
    # Look for "(bv1 bv2 : BitVec 8)" or similar
    m = re.search(r"\(bv1\s+bv2\s*:\s*BitVec\s+(\d+)\)", block)
    if m:
        return int(m.group(1))
    # Some generators use "(bv1 bv2 : BitVec W)" without extra spaces
    m = re.search(r"\(bv1\s+bv2\s*:\s*BitVec\s*(\d+)\)", block)
    if m:
        return int(m.group(1))
    return None

def extract_subtable_name(block: str) -> str | None:
    # Find "evalSubtable AND_64" etc in the statement
    m = re.search(r"\bevalSubtable\s+([A-Za-z0-9_']+)\b", block)
    if m:
        return m.group(1)
    return None

def rewrite_helpers_with_width(block: str, width: int) -> str:
    # map_f_to_bv_<n>  -> BVModEq.map_f_to_bv <n>
    block = re.sub(
        r"(?<!\.)\bmap_f_to_bv_(\d+)\b",
        r"BVModEq.map_f_to_bv \1",
        block,
    )
    # bool_to_bv_<n>   -> BVModEq.bool_to_bv <n>
    block = re.sub(
        r"(?<!\.)\bbool_to_bv_(\d+)\b",
        r"BVModEq.bool_to_bv \1",
        block,
    )
    # bare bool_to_bv  -> BVModEq.bool_to_bv <width>
    # only if unqualified (no dot before)
    block = re.sub(
        r"(?<!\.)\bbool_to_bv\b",
        f"BVModEq.bool_to_bv {width}",
        block,
    )

    # small cleanup: "=BVModEq..." -> "= BVModEq..."
    block = re.sub(r"=\s*BVModEq\.", r"= BVModEq.", block)
    return block

def standardized_proof(subtable_name: str) -> str:
    return (
        " := by\n"
        f"  unfold {subtable_name}\n"
        "  unfold evalSubtable\n"
        "  unfold subtableFromMLE\n"
        "  unfold Vector.append\n"
        "  translate_all false\n"
    )

def replace_lemma_theorem_proofs(text: str) -> str:
    decls = list(re.finditer(r"(?m)^(lemma|theorem)\b", text))
    if not decls:
        return text

    out = []
    out.append(text[:decls[0].start()])

    for i, m in enumerate(decls):
        start = m.start()
        end = decls[i + 1].start() if i + 1 < len(decls) else len(text)
        block = text[start:end]

        # If there's no ':= by', leave proof untouched (but still do helper rewrites if we can infer width)
        width = infer_bitwidth_from_decl(block)
        if width is not None:
            block = rewrite_helpers_with_width(block, width)

        by_idx = block.find(":= by")
        if by_idx == -1:
            out.append(block)
            continue

        # We *replace* the proof with the standardized one
        decl_part = block[:by_idx].rstrip()

        subtable = extract_subtable_name(block)
        if subtable is None:
            # Fallback: if we can't find evalSubtable, keep old proof (but we already did helper rewrites)
            out.append(block)
            continue

        new_block = decl_part.rstrip() + standardized_proof(subtable)
        if not new_block.endswith("\n"):
            new_block += "\n"
        out.append(new_block)

    return "".join(out)

def process_one_file(path: Path) -> None:
    src = path.read_text(encoding="utf-8")
    out = src
    out = normalize_global_helpers(out)
    out = ensure_header(out)
    out = replace_lemma_theorem_proofs(out)

    out_path = SCRIPT_DIR / path.name
    out_path.write_text(out, encoding="utf-8")
    print(f"[OK] {path.name} -> {out_path}")

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path, help="A .lean file or a directory containing .lean files")
    args = ap.parse_args()

    inp: Path = args.input
    if inp.is_file():
        if inp.suffix != ".lean":
            raise SystemExit("Input file must be a .lean file")
        process_one_file(inp)
        return

    if inp.is_dir():
        files = sorted(inp.glob("*.lean"))
        if not files:
            print("[WARN] No .lean files found")
            return
        for f in files:
            process_one_file(f)
        return

    raise SystemExit(f"Invalid input: {inp}")

if __name__ == "__main__":
    main()

