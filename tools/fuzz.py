#!/usr/bin/env python3
"""Differential test of bvsmt against z3 on random QF_BV problems.

Usage: fuzz.py BVSMT Z3 N [SEED]

For each random problem: both solvers must agree on sat/unsat, and for sat the model printed by
bvsmt, added to the problem as assertions, must be satisfiable for z3.
"""
import random
import subprocess
import sys

BIN = ["bvand", "bvor", "bvxor", "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv",
       "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr", "bvnand", "bvnor", "bvxnor"]
UN = ["bvnot", "bvneg"]
CMP = ["=", "distinct", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"]


def const(w):
    return "#b" + "".join(random.choice("01") for _ in range(w))


def bv(vs, w, d):
    """A term of width w."""
    cands = [v for v, vw in vs if vw == w]
    if d == 0 or random.random() < 0.25:
        if cands and random.random() < 0.7:
            return random.choice(cands)
        return const(w)
    r = random.random()
    if r < 0.45:
        return "(%s %s %s)" % (random.choice(BIN), bv(vs, w, d - 1), bv(vs, w, d - 1))
    if r < 0.55:
        return "(%s %s)" % (random.choice(UN), bv(vs, w, d - 1))
    if r < 0.65:
        return "(ite %s %s %s)" % (boolean(vs, d - 1), bv(vs, w, d - 1), bv(vs, w, d - 1))
    if r < 0.75 and w > 1:
        k = random.randint(1, w - 1)
        return "(concat %s %s)" % (bv(vs, w - k, d - 1), bv(vs, k, d - 1))
    if r < 0.85:
        big = w + random.randint(0, 3)
        lo = random.randint(0, big - w)
        return "((_ extract %d %d) %s)" % (lo + w - 1, lo, bv(vs, big, d - 1))
    if r < 0.92 and w > 1:
        k = random.randint(1, w - 1)
        return "((_ %s %d) %s)" % (random.choice(["zero_extend", "sign_extend"]), k, bv(vs, w - k, d - 1))
    if r < 0.96:
        return "((_ %s %d) %s)" % (random.choice(["rotate_left", "rotate_right"]), random.randint(0, 2 * w), bv(vs, w, d - 1))
    return "(let ((t %s)) (bvadd t t))" % bv(vs, w, d - 1)


def boolean(vs, d):
    r = random.random()
    if d == 0 or r < 0.5:
        w = random.randint(1, 4)
        return "(%s %s %s)" % (random.choice(CMP), bv(vs, w, max(d - 1, 0)), bv(vs, w, max(d - 1, 0)))
    if r < 0.7:
        return "(not %s)" % boolean(vs, d - 1)
    op = random.choice(["and", "or", "xor", "=>", "="])
    return "(%s %s %s)" % (op, boolean(vs, d - 1), boolean(vs, d - 1))


def problem():
    vs = [("v%d" % i, random.randint(1, 4)) for i in range(random.randint(1, 3))]
    decls = "".join("(declare-const %s (_ BitVec %d))\n" % v for v in vs)
    asserts = "".join("(assert %s)\n" % boolean(vs, 3) for _ in range(random.randint(1, 3)))
    return "(set-logic QF_BV)\n" + decls + asserts + "(check-sat)\n"


def run(cmd, src):
    return subprocess.run(cmd, input=src, capture_output=True, text=True, timeout=300).stdout


def main():
    bvsmt, z3, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
    random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    stats = {"sat": 0, "unsat": 0}
    for k in range(n):
        p = problem()
        ours = run([bvsmt], p + "(get-model)\n").split("\n")
        theirs = run([z3, "-in"], p).strip()
        if ours[0] != theirs:
            print("MISMATCH (bvsmt %s, z3 %s):\n%s" % (ours[0], theirs, p))
            sys.exit(1)
        stats[theirs] += 1
        if theirs == "sat":
            model = "\n".join(l.strip() for l in ours[1:] if l.strip().startswith("(define-fun"))
            check = p.replace("(check-sat)\n", "") + model.replace("(define-fun ", "(define-fun m_") + "\n"
            for line in ours[1:]:
                line = line.strip()
                if line.startswith("(define-fun"):
                    name = line.split()[1]
                    check += "(assert (= %s m_%s))\n" % (name, name)
            check += "(check-sat)\n"
            if run([z3, "-in"], check).strip() != "sat":
                print("BAD MODEL:\n%s\n%s" % (p, "\n".join(ours)))
                sys.exit(1)
    print("ok: %d problems, %d sat, %d unsat" % (n, stats["sat"], stats["unsat"]))


main()
